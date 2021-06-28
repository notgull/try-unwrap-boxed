# try-unwrap-boxed

This crate exports two simple functions: `unwrap_rc` and `unwrap_arc`. These functions allow one to convert an
`Rc<T>` or an `Arc<T>`, respectively, into a `Box<T>`, as long as that `[A]Rc` is the only strong one left. This
allows one to use the `try_unwrap` function, but for unsized types.

## License

MIT/Apache2 License
