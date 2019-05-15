use pomelo::*;

//You can use %token to add attributes to the Token enum or to add generic types.
//Generic arguments in Token will apply also to Parser.
pomelo! {
    %include {
        use std::marker::PhantomData;
    }
    %token
        #[derive(Debug, Clone, Copy)]
        pub enum Token<'a, 'b, A, B> {};

    %type Phantom PhantomData<&'b B>;
    %type Terminal &'a A;
    %type input &'a A;

    input ::= Terminal(T) { T }
}

#[test]
fn generic_parse() -> Result<(), ()> {
    use parser::*;
    let mut parse = Parser::new();
    let x = 42;
    parse.parse(Token::<_, u8>::Terminal(&x))?;
    let res = parse.end_of_input()?;
    assert_eq!(res, &42);
    Ok(())
}
