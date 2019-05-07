use super::*;

pomelo! {
    %default_type i32;
    %extra_argument Vec<i32>;
    %type list Vec<i32>;

    input ::= list(L) { *extra = L; }
    list ::= { Vec::new() }
    list ::= list(mut L) One|Two|Three(A) { L.push(A); L }
}

#[test]
fn token_alt() -> Result<(), String> {
    use pomelo::*;
    let mut parse = Parser::new(Vec::new(), SimpleCallback);
    parse.parse(Token::One(1))?;
    parse.parse(Token::Two(2))?;
    parse.parse(Token::Three(3))?;
    let res = parse.parse_eoi()?;
    assert_eq!(res, vec![1, 2, 3]);
    Ok(())
}
