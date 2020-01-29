extern crate pomelo;
use pomelo::*;

pomelo! {
    %module A;
    %parser struct Parser<T> { };
                 //~^ ERROR parameter `T` is never used
    input ::=;
}

pomelo! {
    %module B;
    %token enum Token<T>{ };
                 //~^ ERROR parameter `T` is never used
    input ::=;
}

pomelo! {
    %module C;
    %parser struct Parser<T> { };
    %token enum Token<T, G>{ };
                 //~^ ERROR Generic parameter in Token is not in Parser
    input ::=;
}

fn main() {}
