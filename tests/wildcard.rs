use pomelo::*;

pomelo! {
    %wildcard WC;

    input ::= One Two WC;
    input ::= One Two Three;
}

#[test]
fn wildcard() -> Result<(), String> {
    use parser::*;
    let mut p = Parser::new((), SimpleCallback);
    p.parse(Token::One)?;
    p.parse(Token::Two)?;
    p.parse(Token::One)?;
    p.parse_eoi()?;
    Ok(())
}
