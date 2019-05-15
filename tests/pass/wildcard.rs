use pomelo::*;

pomelo! {
    %wildcard WC;
    %type One u8;

    input ::= One Two WC;
    input ::= One Two Three;
}

#[test]
fn wildcard() -> Result<(), ()> {
    use parser::*;
    let mut p = Parser::new();
    p.parse(Token::One(0))?;
    p.parse(Token::Two)?;
    p.parse(Token::One(0))?;
    p.end_of_input()?;
    Ok(())
}
