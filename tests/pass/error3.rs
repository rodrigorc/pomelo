use pomelo::*;

pomelo! {
    %extra_argument String;
    %error String;
    %parse_fail {
        "Parse error".to_string()
    }
    %type Letter char;
    %include {
        fn try_code(c: char) -> Result<char, String> {
            if c == 'C' {
                Err("see".to_string())
            } else {
                Ok(c)
            }
        }
    }

    start ::= word;
    word ::= Letter(C) { extra.push(try_code(C)?); }
    word ::= word Letter(C) { extra.push(try_code(C)?); }
}

#[test]
fn error() -> Result<(), String> {
    use parser::*;
    use Token::*;

    let mut p = Parser::new(String::new());

    let mut error = String::new();
    for t in vec![
        Letter('A'),
        Letter('B'),
        Letter('C'),
        Letter('D'),
    ] {
        match p.parse(t) {
            Ok(_) => {}
            Err(e) => {
                error = e;
                break;
            }
        }
    }
    assert_eq!(p.extra(), "AB");
    assert_eq!(error, "see");
    //no EOI here, the parser never ends

    Ok(())
}
