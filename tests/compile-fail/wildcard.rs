extern crate core;
extern crate pomelo;
use pomelo::*;

pomelo! {
    %wildcard Foo;

    start ::=
        Foo(A)
         //~^ ERROR Wildcard token must not have an alias
        { }
}

fn main() {}
