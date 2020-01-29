extern crate pomelo;
use pomelo::*;

pomelo! {
    input ::= foo;
    foo ::=
        input;
     //~^ ERROR start symbol on the RHS of a rule
}

fn main() {}
