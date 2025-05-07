use pomelo::*;

pomelo! {
    %extra_argument String;
    %syntax_error {
        let tok = expected.next().unwrap();
        extra.push_str(tok.name);
        assert!(tok.token.is_some());
        Ok(())
    }

    start ::= lines;
    lines ::= line;
    lines ::= lines line0;

    line0 ::= error Eol { }
    line0 ::= line Eol;
    line ::= One Two Three { }
}

pomelo! {
    %module parser2;
    %extra_argument String;
    %syntax_error {
        for tok in expected {
            extra.push_str(tok.name);
            assert!(tok.token.is_some());
        }
        Ok(())
    }

    start ::= lines;
    lines ::= line;
    lines ::= lines line0;

    line0 ::= line Eol;
    line ::= One { }
    line ::= Two { }
    line ::= Three { }
}

#[rustfmt::skip]
#[test]
fn expected_tokens() -> Result<(), ()> {
    let mut p = parser::Parser::new(String::new());

    {
        use parser::Token::*;
        for t in [
            One, Two, Three, Eol, /* expected One here */ Two, Eol, One, Two, Three, Eol,
            //One, One, One, Eol,
            One, /* expected Two here */ One, One, One, One, One, One, One, One, Eol, One, Two,
            /* expected Three here */ Eol,
        ] {
            p.parse(t)?;
        }
    }

    assert_eq!(p.extra(), "OneTwoThree");
    //no EOI here, the parser never ends

    let mut p = parser2::Parser::new(String::new());

    {
        use parser2::Token::*;
        for t in [One, Eol, Eol, Two, Eol, Eol, Three, Eol] {
            p.parse(t)?;
        }
    }

    assert_eq!(p.extra(), "OneTwoThree");
    //no EOI here, the parser never ends

    Ok(())
}
