extern crate core;
extern crate pomelo;
use pomelo::*;

pomelo! {
//~^ ERROR 5:1: 13:2: type annotations needed [E0282]
//~| ERROR 5:1: 13:2: type annotations needed [E0282]
    %module A;
    %parser struct Parser<T> { };
                       //~^ ERROR type parameter `T` is only used recursively
                       //~| ERROR 9:27: 9:28: type parameter `T` is never used [E0392]
    input ::=;
}

pomelo! {
//~^ ERROR 15:1: 24:2: type annotations needed [E0282]
//~| ERROR 15:1: 24:2: type annotations needed [E0282]
    %module B;
    %token enum Token<T>{ };
                   //~^ ERROR type parameter `T` is only used recursively
                   //~| ERROR 19:23: 19:24: type parameter `T` is never used [E0392]
                   //~| ERROR 19:23: 19:24: type parameter `T` is never used [E0392]
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
