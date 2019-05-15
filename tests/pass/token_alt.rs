use pomelo::*;

pomelo! {
    %default_type i32;
    %type list Vec<i32>;
    %type input Vec<i32>;

    input ::= list(L) { L }
    list ::= { Vec::new() }
    list ::= list(mut L) One|Two|Three(A) { L.push(A); L }
}

#[test]
fn token_alt() -> Result<(), ()> {
    use parser::*;
    let mut parse = Parser::new();
    parse.parse(Token::One(1))?;
    parse.parse(Token::Two(2))?;
    parse.parse(Token::Three(3))?;
    let res = parse.end_of_input()?;
    assert_eq!(res, vec![1, 2, 3]);
    Ok(())
}
