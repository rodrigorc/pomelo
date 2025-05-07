use pomelo::*;

pomelo! {
    %extra_argument String;
    %syntax_error {
        extra.push('0');
        assert_eq!(token, Some(Token::Two));
        Ok(())
    }
    %token #[derive(Debug, PartialEq)]
           pub enum Token {};

    start ::= lines;
    lines ::= line Eol;
    lines ::= lines line Eol;

    line ::= One Two Three { extra.push('1'); }
}

#[test]
fn error() -> Result<(), ()> {
    use parser::*;
    use Token::*;

    let mut p = Parser::new(String::new());

    for t in [
        One, Two, Three, Eol,
        Two, Eol,
        One, Two, Three, Eol,
    ] {
        p.parse(t)?;
    }
    assert_eq!(p.extra(), "101");
    //no EOI here, the parser never ends

    Ok(())
}
