// MIT/Apache2 License

//! This crate provides a way to unwrap the contents of an `Rc<T>` or an `Arc<T>` into a `Box<T>`. This allows
//! one to use `try_unwrap`, but for an unsized type.
//!
//! # Example
//!
//! ```rust
//! use std::{convert::TryInto, error::Error, num::TryFromIntError, sync::Arc};
//!
//! #[derive(Debug)]
//! enum CustomErrorType {
//!     IncorrectValue(usize),
//!     Dynamic(Arc<dyn Error + Send + Sync>),
//! }
//!
//! fn do_stuff(value: usize) -> Result<usize, CustomErrorType> {
//!     if value == 0 {
//!         return Err(CustomErrorType::IncorrectValue(value));
//!     }
//!     
//!     let mut value: u16 = match value.try_into() {
//!         Ok(value) => value,
//!         Err(e) => return Err(CustomErrorType::Dynamic(Arc::new(e))),
//!     };
//! 
//!     value += 3;
//! 
//!     Ok(value as usize)
//! }
//!
//! match do_stuff(10000000) {
//!     Err(CustomErrorType::Dynamic(e)) => {
//!         let boxed = try_unwrap_boxed::unwrap_arc(e).unwrap();
//!         boxed.downcast::<TryFromIntError>().unwrap();
//!     }
//!     res => panic!(), 
//! }
//! ```

#![no_std]

extern crate alloc;

use alloc::{
    boxed::Box,
    rc::{Rc, Weak as RcWeak},
    sync::{Arc, Weak as ArcWeak},
};
use core::{
    cell::Cell,
    iter,
    mem::{self, MaybeUninit},
    ptr::{self, addr_of},
    sync::atomic::{fence, AtomicUsize, Ordering},
};

/// Try to unwrap an `Rc<T>` into a `Box<T>`. This works even for unsized data.
#[inline]
pub fn unwrap_rc<T: ?Sized>(rc: Rc<T>) -> Result<Box<T>, Rc<T>> {
    if Rc::strong_count(&rc) == 1 {
        // SAFETY: &*rc is well defined
        let boxed = unsafe { read_unsized::<T>(&*rc) };

        // SAFETY: an Rc<T> is just a NonNull<RcBox<T>>, so this transmutation is valid
        let ptr: *const RcBox<T> = unsafe { mem::transmute::<Rc<T>, *const RcBox<T>>(rc) };
        let ptr = unsafe { &*ptr };
        ptr.strong.set(ptr.strong.get() - 1);

        // destroy the implicit weak reference
        let _weak = unsafe { mem::transmute::<*const RcBox<T>, RcWeak<T>>(ptr) };

        // when we drop the pointer, we've essentially already "mem::forgotten" the Rc, so that step is
        // unnecessary
        Ok(boxed)
    } else {
        Err(rc)
    }
}

/// Try to unwrap an `Arc<T>` into a `Box<T>`. This works even for unsized data.
#[inline]
pub fn unwrap_arc<T: ?Sized>(arc: Arc<T>) -> Result<Box<T>, Arc<T>> {
    // SAFETY: an Arc<T> is just a NonNull<ArcInner<T>>, so this transmutation is valid
    let this: *const ArcInner<T> = unsafe { mem::transmute::<Arc<T>, *const ArcInner<T>>(arc) };

    // See if we can replace the inner value (which should be a 1) with a 0
    // SAFETY: "this" refers to a valid, well-aligned RcBox
    if unsafe { &*this }
        .strong
        .compare_exchange(1, 0, Ordering::Relaxed, Ordering::Relaxed)
        .is_err()
    {
        // SAFETY: just reversing the transmutation from above
        return Err(unsafe { mem::transmute::<*const ArcInner<T>, Arc<T>>(this) });
    }

    // Emit a memory fence
    fence(Ordering::Acquire);

    // Create a weak reference in  order to drop the weak counter.
    let _weak = unsafe { mem::transmute::<*const ArcInner<T>, ArcWeak<T>>(this) };

    Ok(unsafe { read_unsized::<T>(addr_of!((*this).data)) })
}

/// The layout of the memory that an `Rc<T>` points to. Remember, an `Rc<T>` is just a `NonNull<RcBox<T>>`
/// and thus can be transmuted into one. Since the layout is "repr(C)", it is well-defined.
///
/// # Safety
///
/// If the layout for an `RcBox<T>` in the standard library is ever changed, this needs to be updated as well or
/// this crate is unsound.
#[repr(C)]
struct RcBox<T: ?Sized> {
    strong: Cell<usize>,
    weak: Cell<usize>,
    value: T,
}

/// As above, the layout of an `Arc<T>` is well-defined.
#[repr(C)]
struct ArcInner<T: ?Sized> {
    strong: AtomicUsize,
    weak: AtomicUsize,
    data: T,
}

/// Utility function to copy unsized data into a `Box` built to fit it.
///
/// # Safety
///
/// `src` must be a well-defined pointer that is aligned, non-null, and refers to a value. The value in `src`
/// must also not be dropped, in order to avoid a double-drop condition.
#[inline]
#[must_use]
unsafe fn read_unsized<T: ?Sized>(src: *const T) -> Box<T> {
    // first, create heap space with enough memory to hold the value in "src"
    let obj_size = mem::size_of_val(&*src);
    // TODO: use new_uninit once it is stabilized
    let mut heap: Box<[MaybeUninit<u8>]> = iter::repeat(MaybeUninit::<u8>::uninit())
        .take(obj_size)
        .collect();

    // use ptr::copy_nonoverlapping to copy the bytes from src to heap
    let src_bytes = src as *const u8;
    ptr::copy_nonoverlapping(
        src_bytes,
        &mut *heap as *mut [MaybeUninit<u8>] as *mut MaybeUninit<u8> as *mut u8,
        obj_size,
    );

    // reconstruct the fat pointer, based on "src"
    let heap_ptr = copy_metadata(src, Box::into_raw(heap) as *mut u8);

    // convert the heap to a valid Box and return
    Box::from_raw(heap_ptr)
}

/// Create a fat pointer that takes the pointer part of `input` and the metadata part of `template`.
///
/// # Safety
///
/// Both pointers must be valid.
#[inline]
unsafe fn copy_metadata<T: ?Sized>(template: *const T, input: *mut u8) -> *mut T {
    // note: all fat pointers are currently 2*usize bytes wide. change this if this changes.
    const RPSIZE: usize = mem::size_of::<usize>() * 2;

    // nothing to do if T is a thin pointer
    if mem::size_of::<*mut T>() == mem::size_of::<usize>() {
        return mem::transmute_copy::<*mut u8, *mut T>(&input);
    }

    // copy the first part of the pointer
    let mut raw_bytes = MaybeUninit::<[MaybeUninit<u8>; RPSIZE]>::uninit().assume_init();
    ptr::copy_nonoverlapping(
        &input as *const *mut u8 as *const u8,
        &mut raw_bytes as *mut [MaybeUninit<u8>] as *mut MaybeUninit<u8> as *mut u8,
        mem::size_of::<usize>(),
    );

    // copy all of the metadata (i.e. all of the bytes after the initial pointer) into raw_bytes
    ptr::copy_nonoverlapping(
        (&template as *const *const T as *const u8).add(mem::size_of::<usize>()),
        (&mut raw_bytes as *mut [MaybeUninit<u8>] as *mut [u8] as *mut u8)
            .add(mem::size_of::<usize>()),
        RPSIZE - mem::size_of::<usize>(),
    );

    mem::transmute_copy::<[MaybeUninit<u8>; RPSIZE], *mut T>(&raw_bytes)
}
