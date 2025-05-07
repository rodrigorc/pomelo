use std::io::{self, BufRead, ErrorKind, Read};
use std::str::FromStr;

use super::parser;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum CharKind {
    Number,
    Alpha,
    Punct,
    String,
    Comment,
}

pub struct Lexer<R> {
    rdr: R,
    current: Option<(CharKind, Vec<u8>)>,
}

impl CharKind {
    fn of(b: u8) -> Option<CharKind> {
        match b {
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => Some(CharKind::Alpha),
            b'0'..=b'9' => Some(CharKind::Number),
            b' ' | b'\r' | b'\n' | b'\t' => None,
            //any other ASCII character is a punct
            x if x < 0x80 => Some(CharKind::Punct),
            //non ASCII characters are considered letters for tokenization purposes
            _ => Some(CharKind::Alpha),
        }
    }
}

impl<R: BufRead> Lexer<R> {
    pub fn new(rdr: R) -> Self {
        Lexer { rdr, current: None }
    }
    fn next_priv(&mut self) -> io::Result<Option<(CharKind, Vec<u8>)>> {
        let mut reply = None;
        while reply.is_none() {
            let b = match self.rdr.by_ref().bytes().next() {
                Some(b) => b?,
                None => {
                    //EOF: if there is a current token, return it now
                    let res = self.current.take();
                    return Ok(res);
                }
            };
            let k2 = CharKind::of(b);
            self.current = match (self.current.take(), k2) {
                (None, None) => None,
                (None, Some(k2)) => Some((k2, vec![b])),
                (Some((k1, mut bs)), t2) => {
                    //extend a Number or Alpha, but not a Punct
                    if Some(k1) == t2 && k1 != CharKind::Punct {
                        bs.push(b);
                        Some((k1, bs))
                    } else {
                        //check special Puncts
                        if k1 == CharKind::Punct && bs[0] == b'"' {
                            //string
                            let text = if b != b'"' {
                                let mut text = vec![b];
                                self.rdr.by_ref().read_until(b'"', &mut text)?;
                                if text.pop().unwrap() != b'"' {
                                    return Err(ErrorKind::InvalidInput.into());
                                }
                                text
                            } else {
                                vec![]
                            };
                            reply = Some((CharKind::String, text));
                            None
                        } else if k1 == CharKind::Punct && bs[0] == b'/' && b == b'/' {
                            //comment
                            let mut text = vec![];
                            self.rdr.by_ref().read_until(b'\n', &mut text)?;
                            reply = Some((CharKind::Comment, text));
                            None
                        } else {
                            //The current token is returned and the new lookahead is stored
                            reply = Some((k1, bs));
                            t2.map(|k2| (k2, vec![b]))
                        }
                    }
                }
            }
        }
        Ok(reply)
    }
    fn next_token(&mut self) -> io::Result<Option<parser::Token>> {
        loop {
            let token = self.next_priv()?;
            let token = match token {
                None => None,
                Some((kind, s)) => {
                    let reply = match kind {
                        CharKind::Comment => continue,
                        CharKind::Number => {
                            let s = String::from_utf8(s).map_err(|_| ErrorKind::InvalidInput)?;
                            parser::Token::Number(
                                i64::from_str(&s).map_err(|_| ErrorKind::InvalidInput)?,
                            )
                        }
                        CharKind::Alpha => match &s[..] {
                            b"fn" => parser::Token::Fn,
                            b"var" => parser::Token::Var,
                            b"if" => parser::Token::If,
                            b"else" => parser::Token::Else,
                            b"while" => parser::Token::While,
                            b"return" => parser::Token::Return,
                            b"continue" => parser::Token::Continue,
                            b"break" => parser::Token::Break,
                            b"and" => parser::Token::And,
                            b"or" => parser::Token::Or,
                            b"not" => parser::Token::Not,
                            _ => {
                                let s =
                                    String::from_utf8(s).map_err(|_| ErrorKind::InvalidInput)?;
                                parser::Token::Ident(s)
                            }
                        },
                        CharKind::String => {
                            let s = String::from_utf8(s).map_err(|_| ErrorKind::InvalidInput)?;
                            parser::Token::String(s)
                        }
                        CharKind::Punct => {
                            let s = s[0];
                            //First check for two-char Puncts
                            let tt = if let Some((CharKind::Punct, n)) = &self.current {
                                let n = n[0];
                                match (s, n) {
                                    (b'=', b'=') => Some(parser::Token::Equal),
                                    (b'!', b'=') => Some(parser::Token::NotEqual),
                                    (b'<', b'=') => Some(parser::Token::LessEq),
                                    (b'>', b'=') => Some(parser::Token::GreaterEq),
                                    _ => None,
                                }
                            } else {
                                None
                            };
                            if tt.is_some() {
                                self.current = None;
                                return Ok(tt);
                            }
                            match s {
                                b'(' => parser::Token::LParen,
                                b')' => parser::Token::RParen,
                                b'{' => parser::Token::LBrace,
                                b'}' => parser::Token::RBrace,
                                b',' => parser::Token::Comma,
                                b';' => parser::Token::Semicolon,
                                b'=' => parser::Token::Assign,
                                b'+' => parser::Token::Plus,
                                b'-' => parser::Token::Minus,
                                b'*' => parser::Token::Mult,
                                b'/' => parser::Token::Div,
                                b'<' => parser::Token::Less,
                                b'>' => parser::Token::Greater,
                                _ => return Err(ErrorKind::InvalidInput.into()),
                            }
                        }
                    };
                    Some(reply)
                }
            };
            break Ok(token);
        }
    }
}

impl<R: BufRead> Iterator for Lexer<R> {
    type Item = io::Result<parser::Token>;
    fn next(&mut self) -> Option<Self::Item> {
        self.next_token().transpose()
    }
}
