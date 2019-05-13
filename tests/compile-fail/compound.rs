extern crate pomelo;
use pomelo::*;

pomelo! {
    %module one;
    %type One i32;
    %type Two i8;

    start ::=
        One|Two|Three(A)
     //~^ ERROR Compound tokens must have all the same type
        { }
}

pomelo! {
    %module two;
    %type One i32;
    %type Two i8;
    %token_class Number One Two;

    start ::=
        Number(A)
     //~^ ERROR Compound tokens must have all the same type
        { }
}
