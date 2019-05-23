extern crate pomelo;
use pomelo::*;

pomelo! {
    %type Foo i8;
    %type Foo i8;
       //~^ ERROR Symbol type already defined
    input ::=;
}

pomelo! {
    %left Foo;
    %left Foo;
       //~^ ERROR Symbol has already been given a precedence
    input ::=;
}

pomelo! {
    %left foo;
       //~^ ERROR Precedence cannot be assigned to a non-terminal
    input ::=;
}
