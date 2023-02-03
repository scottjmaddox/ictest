# ictest

An implementation of the interaction calculus for testing.

My main goal is to generate arbitrary expressions, reduce them in every possible optimal order, and confirm that the number of reductions and the result is always the same.

I would also like to be able to display the reductions in text form, including which rules were applied.

## Checking for memory leaks

Ensure you have a nightly compiler installed:

```sh
rustup install nightly
```

Collect a baseline for leaks:

```sh
RUSTFLAGS=-Zsanitizer=address ASAN_OPTIONS=detect_leaks=1 cargo +nightly test empty_test
```

Then compare against an actual test run:

```sh
RUSTFLAGS=-Zsanitizer=address ASAN_OPTIONS=detect_leaks=1 cargo +nightly test
```

See the [corresponding section of the Rust Unstable Book](https://doc.rust-lang.org/beta/unstable-book/compiler-flags/sanitizer.html#addresssanitizer) for more information.

## Checking for undefined behavior using Miri

Ensure you have miri installed:

```sh
rustup +nightly component add miri
```

Run the `vm` tests under miri:

```sh
cargo clean
cargo +nightly miri test vm
```
