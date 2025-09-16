extern crate core;
extern crate pomelo;
use pomelo::*;

pomelo! {
    %module A;
    %fallback One Two Three;
    %type One i8;
           //~^ ERROR Fallback token must have the same type or no type at all

    input ::=;
}

pomelo! {
    %module B;
    %fallback One Two;
    %fallback Two Three;
    %fallback Three One;
           //~^ ERROR 18:15: 18:20: Fallback directive creates a loop

    input ::=;
}

fn main() {
}
