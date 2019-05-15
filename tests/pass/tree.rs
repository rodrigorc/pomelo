use pomelo::*;
use super::toy_lexer;

pomelo! {
    %error String;
    %parse_fail {
        "Parse error".to_string()
    }
    %include {
        use super::toy_lexer::{self, TestTree, TestToken};
        use pomelo::*;

        fn char_to_token(c: char) -> Result<Token, String> {
            let tk = match c {
                '+' => Token::Plus,
                '-' => Token::Minus,
                '(' => Token::LParen,
                ')' => Token::RParen,
                '*' => Token::Mult,
                '^' => Token::Pow,
                tok => return Err(format!("unexpected token '{}'", tok)),
            };
            Ok(tk)
        }

        pub fn parse_tree(input: &str) -> Result<TestTree, String> {
            let mut p = Parser::new();
            for tok in toy_lexer::tokenize(input) {
                let tok = match tok {
                    TestToken::Number(i) => Token::Integer(i),
                    TestToken::Punct(c) => char_to_token(c)?,
                    tok => return Err(format!("unexpected token '{:?}'", tok)),
                };
                p.parse(tok)?;
            }
            Ok(p.end_of_input()?)
        }
        pub fn parse_tree2(input: &str) -> Result<TestTree, String> {
            use proc_macro2;
            let tokstream = input.parse().map_err(|e: proc_macro2::LexError| "lexer error")?;
            let mut p = Parser::new();

            lexer::parse(tokstream, |tk| {
                let tk = match tk {
                    proc_macro2::TokenTree::Punct(p) => char_to_token(p.as_char())?,
                    proc_macro2::TokenTree::Literal(l) => Token::Integer(l.to_string().parse().unwrap()),
                    proc_macro2::TokenTree::Ident(i) => panic!(),
                    proc_macro2::TokenTree::Group(g) => panic!(),
                };
                p.parse(tk)?;
                Ok::<(), String>(())
            })?;
            Ok(p.end_of_input()?)
        }
    }
    %type input TestTree;
    %type tree TestTree;
    %type Integer i32;
    %left Plus Minus;
    %left Mult;
    %nonassoc Unary;
    %right Pow;

    input ::= tree(A) { A }

    tree ::= Integer(I) { TestTree::Integer(I) }
    tree ::= LParen tree(A) RParen { A }
    tree ::= tree(A) Plus tree(B) { TestTree::Binary('+', Box::new(A), Box::new(B)) }
    tree ::= tree(A) Minus tree(B) { TestTree::Binary('-', Box::new(A), Box::new(B)) }
    tree ::= tree(A) Mult tree(B) { TestTree::Binary('*', Box::new(A), Box::new(B)) }
    tree ::= tree(A) Pow tree(B) { TestTree::Binary('^', Box::new(A), Box::new(B)) }
    tree ::= Minus tree(A) { TestTree::Unary('<', Box::new(A)) } [Unary]
    tree ::= Plus tree(A) { TestTree::Unary('>', Box::new(A)) } [Unary]
}

use parser::{parse_tree, parse_tree2};

fn compare_tree(s: &str, t: &str) -> Result<(), String> {
    let tree = parse_tree(s)?;
    assert_eq!(tree.to_string(), t);

    let tree = parse_tree2(s)?;
    assert_eq!(tree.to_string(), t);

    Ok(())
}

#[test]
fn tree_basic() -> Result<(), String> {
    compare_tree("1 + 2 - 3 + 4", "+ - + 1 2 3 4")
}

#[test]
fn tree_with_paren() -> Result<(), String> {
    compare_tree("1 + (2 - 3) + 4", "+ + 1 - 2 3 4")
}

#[test]
fn tree_precedence() -> Result<(), String> {
    compare_tree("1 * (2 + 3)", "* 1 + 2 3")?;
    compare_tree("1 * 2 + 3", "+ * 1 2 3")?;
    compare_tree("1 + 2 * 3", "+ 1 * 2 3")
}

#[test]
fn tree_right() -> Result<(), String> {
    compare_tree("1 ^ 2 ^ 3", "^ 1 ^ 2 3")
}

#[test]
fn tree_unary_prec() -> Result<(), String> {
    compare_tree("-1 * 2", "* < 1 2")?;
    compare_tree("2 +-1 * -+2", "+ 2 * < 1 < > 2")?;
    compare_tree("-(2 + 3)", "< + 2 3")
}

