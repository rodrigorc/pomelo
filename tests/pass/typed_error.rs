use pomelo::*;

pomelo! {
    %type error char;
    %extra_argument String;
    %syntax_error { extra.push('X'); Ok('0') }

    start ::= lines;
    lines ::= line;
    lines ::= lines line0;

    line0 ::= error(E) Eol { extra.push(E); }
    line0 ::= line Eol;
    line ::= One Two Three { extra.push('1'); }
}

#[rustfmt::skip]
#[test]
fn typed_error() -> Result<(), ()> {
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
