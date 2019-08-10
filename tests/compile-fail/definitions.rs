extern crate pomelo;
use pomelo::*;

pomelo! {
    %default_type i8;
    %default_type i8;
               //~^ ERROR Default type already defined
    input ::=;
}

pomelo! {
    %extra_argument i8;
    %extra_argument i8;
               //~^ ERROR Extra argument type already defined
    input ::=;
}

pomelo! {
    %extra_token i8;
    %extra_token i8;
            //~^ ERROR Extra token type already defined
    input ::=;
}

pomelo! {
    %error i8;
    %error i8;
        //~^ ERROR Error type already defined
    input ::=;
}

pomelo! {
    %start_symbol input;
    %start_symbol input;
               //~^ ERROR Start symbol already defined
    input ::=;
}

pomelo! {
    %start_symbol Foo;
               //~^ ERROR Start symbol must be a non-terminal
    input ::=;
}

pomelo! {
    %fallback foo Bar;
           //~^ ERROR Fallback must be a token
    input ::=;
}

pomelo! {
    %fallback Foo bar;
               //~^ ERROR Fallback ids must be tokens
    input ::=;
}

pomelo! {
    %fallback Foo Bar;
    %fallback Baz Bar;
               //~^ ERROR More than one fallback assigned to token
    input ::=;
}

pomelo! {
    %wildcard Foo;
    %wildcard Bar;
           //~^ ERROR Wildcard already defined
    input ::=;
}

pomelo! {
    %wildcard foo;
           //~^ ERROR Wildcard must be a token
    input ::=;
}

pomelo! {
    %token_class foo Bar;
              //~^ ERROR token_class must be a token
    input ::=;
}

pomelo! {
    %token_class Foo bar;
                  //~^ ERROR token_class ids must be tokens
    input ::=;
}

pomelo! {
    %token enum Token {};
    %token enum Token {};
             //~^ ERROR token enum already defined
    input ::=;
}

pomelo! {
    %wildcard Foo;
    %type Foo i8;
       //~^ ERROR Wildcard token must not have a type
    input ::=;
}

pomelo! {
    %token enum Token {
        A
     //~^ ERROR Token enum declaration must be empty
    };
    input ::=;
}

pomelo! {
    %parser struct Parser {};
    %parser struct Parser {};
             //~^ ERROR parser struct already defined
    input ::=;
}

pomelo! {
    %parser struct Parser {
        A: ()
     //~^ ERROR Parser struct declaration must be empty
    };
    input ::=;
}

