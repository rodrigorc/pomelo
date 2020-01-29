extern crate pomelo;
use pomelo::*;

pomelo! {
    %type _xxx i8;
       //~^ ERROR Symbol must start with uppercase or lowercase letter
    input ::= ;
}

pomelo! {
    input ::= _xxx;
           //~^ ERROR Symbol must start with uppercase or lowercase letter
}

fn main() {}
