extern crate pomelo;
use pomelo::*;

pomelo! {
    %fallback One Two Three;
    %type One i8;
           //~^ ERROR Fallback token must have the same type or no type at all

    input ::=;
}

fn main() {}
