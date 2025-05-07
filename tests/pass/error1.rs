use pomelo::*;

pomelo! {
    %extra_argument String;
    %syntax_error { extra.push('X'); Ok(()) }

    start ::= lines;
    lines ::= line;
    lines ::= lines line0;

    line0 ::= error Eol { extra.push('0'); }
    line0 ::= line Eol;
    line ::= One Two Three { extra.push('1'); }
}

#[rustfmt::skip]
#[test]
fn error() -> Result<(), ()> {
    use parser::*;
    use Token::*;

    let mut p = Parser::new(String::new());

    for t in [
        One, Two, Three, Eol,
        Two, Eol,
        One, Two, Three, Eol,
        //One, One, One, Eol,
        One, One, One, One, One, One, One, One, One, Eol,
        One, Two, Three, Eol,
    ] {
        p.parse(t)?;
    }
    assert_eq!(p.extra(), "1X01X01");
    //no EOI here, the parser never ends

    Ok(())
}
