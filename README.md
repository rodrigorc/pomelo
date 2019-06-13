# pomelo
A procedural macro to create Lemon-like parsers.

Pomelo is a port to Rust of the Lemon Parser Generator (from now on, Lemon\_C) originally written
by D. Richard Hipp for his SQLite parser.  It is based on a previous attempt to port Lemon to Rust
(Lemon\_Rust), but now it is written as a Rust procedural macro, so it does not contain any of the
original C code (although it uses the same algorithms). Thus the change in name to a different
citrus fruit.

## Getting Started

[Pomelo](https://crates.io/crates/pomelo). It is recommended to look there for
the newest released version, as well as links to the newest builds of the docs.

Add the following dependency to your Cargo manifest...

```toml
[dependencies]
pomelo = "*"
```

## Example

```rust
use pomelo::pomelo;

pomelo! {
    %type input Vec<i32>;
    %type numbers Vec<i32>;
    %type Number i32;

    input ::= numbers?(A) { A.unwrap_or_else(Vec::new) };
    numbers ::= Number(N) { vec![N] }
    numbers ::= numbers(mut L) Comma Number(N) { L.push(N); L }
}
fn main() -> Result<(), ()> {
    let mut parser = parser::Parser::new();
    parser.parse(parser::Token::Number(1))?;
    parser.parse(parser::Token::Comma)?;
    parser.parse(parser::Token::Number(2))?;
    parser.parse(parser::Token::Comma)?;
    parser.parse(parser::Token::Number(3))?;
    let data = parser.end_of_input()?;
    assert_eq!(data, vec![1, 2, 3]);
    Ok(())
}
```

See more examples in the [github repo folder](https://github.com/rodrigorc/pomelo/tree/master/examples).

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.

