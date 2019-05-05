use super::*;

pomelo! {
    %extra_argument Option<TestTree>;
    %include {
        use super::*;
        use super::lexer::{self, TestTree, TestToken};
        pub fn parse_tree(input: &str) -> Result<TestTree, String> {
            let mut p = Parser::new(None, SimpleCallback);
            for tok in lexer::tokenize(input) {
                let tok = match tok {
                    TestToken::Number(i) => Token::Integer(i),
                    TestToken::Punct('+') => Token::Plus,
                    TestToken::Punct('-') => Token::Minus,
                    TestToken::Punct('(') => Token::LParen,
                    TestToken::Punct(')') => Token::RParen,
                    TestToken::Punct('*') => Token::Mult,
                    TestToken::Punct('^') => Token::Pow,
                    tok => return Err(format!("unexpected token '{:?}'", tok)),
                };
                p.parse(tok)?;
            }
            Ok(p.parse_eoi()?.unwrap())
        }
    }
    %type tree TestTree;
    %type Integer i32;
    %left Plus Minus;
    %left Mult;
    %nonassoc Unary;
    %right Pow;

    input ::= tree(A) { *extra = Some(A) }

    tree ::= Integer(I) { TestTree::Integer(I) }
    tree ::= LParen tree(A) RParen { A }
    tree ::= tree(A) Plus tree(B) { TestTree::Binary('+', Box::new(A), Box::new(B)) }
    tree ::= tree(A) Minus tree(B) { TestTree::Binary('-', Box::new(A), Box::new(B)) }
    tree ::= tree(A) Mult tree(B) { TestTree::Binary('*', Box::new(A), Box::new(B)) }
    tree ::= tree(A) Pow tree(B) { TestTree::Binary('^', Box::new(A), Box::new(B)) }
    tree ::= Minus tree(A) { TestTree::Unary('<', Box::new(A)) } [Unary]
    tree ::= Plus tree(A) { TestTree::Unary('>', Box::new(A)) } [Unary]
}

use self::parser::parse_tree;

#[test]
fn tree_basic() -> Result<(), String> {
    let tree = parse_tree("1 + 2 - 3 + 4")?;
    assert_eq!(tree.to_string(), "+ - + 1 2 3 4");
    Ok(())
}

#[test]
fn tree_with_paren() -> Result<(), String> {
    let tree = parse_tree("1 + (2 - 3) + 4")?;
    assert_eq!(tree.to_string(), "+ + 1 - 2 3 4");
    Ok(())
}

#[test]
fn tree_precedence() -> Result<(), String> {
    let tree = parse_tree("1 * (2 + 3)")?;
    assert_eq!(tree.to_string(), "* 1 + 2 3");
    let tree = parse_tree("1 * 2 + 3")?;
    assert_eq!(tree.to_string(), "+ * 1 2 3");
    let tree = parse_tree("1 + 2 * 3")?;
    assert_eq!(tree.to_string(), "+ 1 * 2 3");
    Ok(())
}

#[test]
fn tree_right() -> Result<(), String> {
    let tree = parse_tree("1 ^ 2 ^ 3")?;
    assert_eq!(tree.to_string(), "^ 1 ^ 2 3");
    Ok(())
}

#[test]
fn tree_unary_prec() -> Result<(), String> {
    let tree = parse_tree("-1 * 2")?;
    assert_eq!(tree.to_string(), "* < 1 2");
    let tree = parse_tree("2 +-1 * -+2")?;
    assert_eq!(tree.to_string(), "+ 2 * < 1 < > 2");
    let tree = parse_tree("-(2 + 3)")?;
    assert_eq!(tree.to_string(), "< + 2 3");
    Ok(())
}

