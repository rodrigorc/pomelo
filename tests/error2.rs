use pomelo::*;

pomelo! {
    %extra_argument String;

    start ::= lines;
    lines ::= line Eol;
    lines ::= lines line Eol;

    line ::= One Two Three { extra.push('1'); }
}

#[test]
fn error() -> Result<(), String> {
    use parser::*;
    use Token::*;

    let mut p = Parser::new(String::new(), SimpleCallback);

    for t in vec![
        One, Two, Three, Eol,
        Two, Eol,
        One, Two, Three, Eol,
    ] {
        match p.parse(t) {
            Ok(_) => {}
            Err(_) => break
        }
    }
    assert_eq!(p.extra(), "1");
    //no EOI here, the parser never ends

    Ok(())
}
