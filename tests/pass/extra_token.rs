use pomelo::*;

pomelo! {
    %extra_token usize;
    %type One String;
    %type Two i32;
    %type Three (char, char);
    %type line (usize, String);
    %type lines Vec<(usize, String)>;
    %type input Vec<(usize, String)>;
    %syntax_error {
        let x: usize = token.map(Token::into_extra).unwrap_or(0);
        Ok(())
    }

    input ::= lines;
    lines ::= line(L) { vec![L] }
    lines ::= lines(mut V) Eol(n) line(L) {
        V.push((n, "/".to_string()));
        V.push(L);
        V
    }
    line ::= One((n, X)) {
        (n, X.to_string())
    }
    line ::= Two((n, X)) Two((n1, Y)) {
        if n != n1 {
            return Err(());
        }
        (n, format!("{}, {}", X, Y))
    }
    line ::= Three((n, (X1,X2))) Three((n1, (Y1,Y2))) Three((n2, (Z1,Z2))) {
        if n != n1 || n != n2 {
            return Err(());
        }
        (n, format!("{}{}{}{}{}{}", X1, X2, Y1, Y2, Z1, Z2))
    }
}

#[test]
fn extra_token() -> Result<(), ()> {
    use parser::*;
    let mut parse = Parser::new();
    parse.parse(Token::One((1, "one".to_string())))?;
    parse.parse(Token::Eol(1))?;
    parse.parse(Token::Two((2, 21)))?;
    parse.parse(Token::Two((2, 42)))?;
    parse.parse(Token::Eol(2))?;
    parse.parse(Token::Three((3, ('a', 'b'))))?;
    parse.parse(Token::Three((3, ('c', 'd'))))?;
    parse.parse(Token::Three((3, ('e', 'f'))))?;
    let res = parse.end_of_input()?;
    #[rustfmt::skip]
    assert_eq!(res, vec![
        (1, "one"), (1, "/"),
        (2, "21, 42"), (2, "/"),
        (3, "abcdef"),
    ].into_iter().map(|(n, s)| (n, s.to_string())).collect::<Vec<_>>());
    Ok(())
}
