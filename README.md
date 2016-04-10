Sayava language.

**С**упер

**Я**зык

**В**ысокой

**А**ктуальности

### About
`Syava-lang` is a compiler project. The result of compilation is LLVM's IR.

Current features:
- [x] let
- [x] if
- [x] Numbers
- [x] Void
Etc

Future plans:
- [ ] Pointers
- [ ] &
- [ ] Return last statement

### Building
You will need `rust-nightly` and `cargo`.
After you obtain them for your distro, simply run
```
cargo update
cargo build
```

### Testing

```
RUST_TEST_THREADS=1 cargo test
```

If you want manual testing run
```
cargo run <path_to_testing_source>
```

### Examples

See `test.sva` and `src/tests.rs`
