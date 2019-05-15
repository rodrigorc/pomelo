use pomelo::*;

pomelo! {
    %extra_argument String;

    start ::= lines;
    lines ::= line Eol;
    lines ::= lines line Eol;

    line ::= One Two Three { extra.push('1'); }
    line ::= error { extra.push('0'); }
}

#[test]
fn error() -> Result<(), ()> {
    use parser::*;
    use Token::*;

    let mut p = Parser::new(String::new());

    for t in vec![
        One, Two, Three, Eol,
        Two, Eol,
        One, Two, Three, Eol,
        One, One, Eol,
        One, Two, Three, Eol,
    ] {
        p.parse(t)?;
    }
    assert_eq!(p.extra(), "10101");
    //no EOI here, the parser never ends

    Ok(())
}
