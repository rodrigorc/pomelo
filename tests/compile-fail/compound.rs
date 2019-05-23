extern crate pomelo;
use pomelo::*;

pomelo! {
    %module one;
    %type One i32;
    %type Two i8;

    start ::=
        One|Two|Three(A)
                   //~^ ERROR Compound tokens with an alias must all have the same type
        { }
}

pomelo! {
    %module two;
    %type One i32;
    %type Two i8;
    %token_class Number One Two;

    start ::=
        Number(A)
            //~^ ERROR Compound tokens with an alias must all have the same type
        { }
}

pomelo! {
    %module three;
    %type Number i32; //TODO: it should fail, currently is ignored
    %token_class Number One Two;

    start ::=;
}
