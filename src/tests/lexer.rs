use super::*;

#[derive(Debug)]
pub enum TestToken {
    Number(i32),
    Alpha(String),
    Punct(char),
}

pub fn tokenize(input: &str) -> Vec<TestToken> {
    use self::TestToken::*;
    let mut res = Vec::new();
    let mut prev = None;
    for c in input.chars() {
        let next = match c {
            'a'..='z' | 'A'..='Z' => {
                Some(Alpha(c.to_string()))
            }
            '0'..='9' => {
                Some(Number(c as i32 - '0' as i32))
            }
            ' ' | '\r' | '\n' | '\t' => {
                None
            }
            c => {
                Some(Punct(c))
            }
        };
        prev = match (prev, next) {
            (None, b) => b,
            (Some(a), None) => { res.push(a); None }
            (Some(a), Some(b)) => Some(match (a, b) {
                (Alpha(a), Alpha(b)) => Alpha(a + &b),
                (Number(a), Number(b)) => Number(10*a + b),
                (a, b) => { res.push(a); b }
            })
        }
    }
    if let Some(a) = prev.take() {
        res.push(a);
    }
    res
}

#[allow(unused)]
#[derive(Debug)]
pub enum TestTree {
    Integer(i32),
    Ident(String),
    Unary(char, Box<TestTree>),
    Binary(char, Box<TestTree>, Box<TestTree>),
    Group(char, char, Vec<TestTree>),
}

impl std::fmt::Display for TestTree {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        use self::TestTree::*;
        match self {
            Integer(i) => write!(fmt, "{}", i)?,
            Ident(s) => write!(fmt, "{}", s)?,
            Unary(c, a) => write!(fmt, "{} {}", c, a)?,
            Binary(c, a, b) => write!(fmt, "{} {} {}", c, a, b)?,
            Group(c1, c2, v) => {
                write!(fmt, "{}", c1)?;
                for a in v {
                    write!(fmt, " {}", a)?;
                }
                write!(fmt, " {}", c2)?;
            }
        }
        Ok(())
    }
}
