# pomelo

A procedural macro to create Lemon-like parsers.

[![Travis-CI Status](https://travis-ci.com/rodrigorc/pomelo.svg?branch=master)](https://travis-ci.com/rodrigorc/pomelo)
[![Latest version](https://img.shields.io/crates/v/pomelo.svg)](https://crates.io/crates/pomelo)
[![Documentation](https://docs.rs/pomelo/badge.svg)](https://docs.rs/pomelo)

Pomelo is a port to Rust of the Lemon Parser Generator (from now on, Lemon\_C) originally written
by D. Richard Hipp for his SQLite parser.  It is based on a previous attempt to port Lemon to Rust
(Lemon\_Rust), but now it is written as a Rust procedural macro, so it does not contain any of the
original C code (although it uses the same algorithms). Thus the change in name to a different
citrus fruit.

## Getting Started

It is recommended to go to [crates.io](https://crates.io/crates/pomelo) for
the newest released version, as well as links to the newest builds of the docs.

Just add the following dependency to your Cargo manifest:

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
    use parser::{Parser, Token};
    //Real world code would use a tokenizer
    let tokens = vec![
        Token::Number(1),
        Token::Comma,
        Token::Number(2),
        Token::Comma,
        Token::Number(3),
    ];
    let mut p = Parser::new();
    for tok in tokens.into_iter() {
        p.parse(tok)?;
    }
    let data = p.end_of_input()?;
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

