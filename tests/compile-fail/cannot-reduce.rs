extern crate core;
extern crate pomelo;
use pomelo::*;

pomelo! {
    input ::= ;
    foo ::= Tok;
     //~^ ERROR This rule cannot be reduced
}

fn main() {}
