use pomelo::*;

pomelo! {
    %syntax_error { Err(()) }
    %type input i32;
    %type Two i32;
    input ::= One Two?(X) Three Two?(Y) Four end? { X.unwrap_or(1) + Y.unwrap_or(1) }
    end ::= End;
}

use parser::*;

#[test]
fn without_optional() -> Result<(), ()> {
    let mut parse = Parser::new();
    parse.parse(Token::One)?;
    parse.parse(Token::Three)?;
    parse.parse(Token::Four)?;
    let res = parse.end_of_input()?;
    assert_eq!(res, 2);
    Ok(())
}

#[test]
fn with_optional() -> Result<(), ()> {
    let mut parse = Parser::new();
    parse.parse(Token::One)?;
    parse.parse(Token::Two(42))?;
    parse.parse(Token::Three)?;
    parse.parse(Token::Two(24))?;
    parse.parse(Token::Four)?;
    parse.parse(Token::End)?;
    let res = parse.end_of_input()?;
    assert_eq!(res, 42 + 24);
    Ok(())
}
