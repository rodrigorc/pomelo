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
    %extra_argument Option<&'a A>;

    input ::= Terminal(T) { *extra = Some(T); }
}

#[test]
fn generic_parse() -> Result<(), String> {
    use parser::*;
    let mut parse = Parser::new(None, SimpleCallback);
    let x = 42;
    parse.parse(Token::<_, u8>::Terminal(&x))?;
    let res = parse.parse_eoi()?;
    assert_eq!(res, Some(&42));
    Ok(())
}
