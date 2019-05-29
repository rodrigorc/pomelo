extern crate pomelo;
use pomelo::*;

pomelo! {
    %type foo i32;
    input ::= foo;
    foo ::= Tok;
 //~^ ERROR This rule has a typed LHS but no code to assign it
}

