use pomelo::*;

pomelo! {
    %token_class Number One Two Three;
    %token_class Letter Aaa Bbb Ccc;
    %default_type i32;
    %type Aaa i8;
    %type input Vec<i32>;
    %type list Vec<i32>;

    input ::= list(L) { L }
    list ::= { Vec::new() }
    //Children of Number must have the same type
    list ::= list(mut L) Number(A) { L.push(A); L }
    //Children of Letter need not have the same type
    list ::= list(L) Letter { L }
}

#[test]
fn token_class() -> Result<(), ()> {
    use parser::*;
    let mut parse = Parser::new();
    parse.parse(Token::One(1))?;
    parse.parse(Token::Two(2))?;
    parse.parse(Token::Three(3))?;
    let res = parse.end_of_input()?;
    assert_eq!(res, vec![1, 2, 3]);
    Ok(())
}
