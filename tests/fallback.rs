use pomelo::*;

pomelo! {
    %fallback Fallback One Two Three;

    input ::= tokens;
    tokens ::= Fallback Two Fallback;
    tokens ::= Three Two One;
}


#[test]
fn fallback() -> Result<(), String> {
    use parser::*;
    let mut p = Parser::new((), SimpleCallback);
    p.parse(Token::One)?;
    p.parse(Token::Two)?;
    p.parse(Token::Three)?;
    p.end_of_input()?;
    Ok(())
}
