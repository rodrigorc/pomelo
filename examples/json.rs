use pomelo::*;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub enum JObject {
    JDict(HashMap<String, JObject>),
    JArray(Vec<JObject>),
    JNumber(i64),
    JString(String),
    JBool(bool),
    JNull,
}

impl std::str::FromStr for JObject {
    type Err = String;
    fn from_str(input: &str) -> Result<JObject, String> {
        let mut p = json::Parser::new();
        let tok_stream = input.parse().map_err(|_| "Lexer Error")?;
        lexer::parse::<String, _>(tok_stream, |tk| {
            use proc_macro2::TokenTree;
            let tk = match tk {
                TokenTree::Punct(p) => match p.as_char() {
                    '{' => json::Token::LBrace,
                    '}' => json::Token::RBrace,
                    '[' => json::Token::LBracket,
                    ']' => json::Token::RBracket,
                    ',' => json::Token::Comma,
                    ':' => json::Token::Colon,
                    c => { return Err(format!("Invalid character '{}'", c)); }
                }
                TokenTree::Literal(l) => {
                    let s = l.to_string();
                    if s.starts_with('"') && s.ends_with('"') {
                        let bs = s.into_bytes();
                        let s = std::str::from_utf8(&bs[1..bs.len()-1]).unwrap().to_string();
                        json::Token::JString(s)
                    } else {
                        let i = s.parse().map_err(|_| "Invalid integer value")?;
                        json::Token::JNumber(i)
                    }
                }
                TokenTree::Ident(i) => {
                    let s = i.to_string();
                    if s == "true" {
                        json::Token::JBool(true)
                    } else if s == "false" {
                        json::Token::JBool(false)
                    } else if s == "null" {
                        json::Token::JNull
                    } else {
                        return Err(format!("Invalid token '{}'", s));
                    }
                }
                _ => unimplemented!()
            };
            p.parse(tk).map_err(|_| "Parser error")?;
            Ok(())
        })?;
        let j = p.end_of_input().map_err(|_| "Parser error")?;
        Ok(j)
    }
}

pomelo! {
    %module json;
    %include {
        use super::JObject;
        use std::collections::HashMap;
    }
    %token #[derive(Debug)] pub enum Token {};
    %type start JObject;
    %type jobject JObject;
    %type jdict JObject;
    %type jarray JObject;
    %type JNumber i64;
    %type JString String;
    %type JBool bool;
    %type jobject_list Vec<JObject>;
    %type jitem_list HashMap<String, JObject>;
    %type jitem (String, JObject);

    start ::= jobject(J) { J }

    jobject ::= jdict(D) { D }
    jobject ::= jarray(A) { A }
    jobject ::= JNumber(N) { JObject::JNumber(N) }
    jobject ::= JString(S) { JObject::JString(S) }
    jobject ::= JBool(B) { JObject::JBool(B) }
    jobject ::= JNull { JObject::JNull }

    jdict ::= LBrace RBrace { JObject::JDict(HashMap::new()) }
    jdict ::= LBrace jitem_list(D) RBrace { JObject::JDict(D) }

    jarray ::= LBracket RBracket { JObject::JArray(Vec::new()) }
    jarray ::= LBracket jobject_list(A) RBracket { JObject::JArray(A) }

    jobject_list ::= jobject(J) { vec![J] }
    jobject_list ::= jobject_list(mut A) Comma jobject(J) { A.push(J); A }

    jitem_list ::= jitem((K,V)) { let mut d = HashMap::new(); d.insert(K, V); d }
    jitem_list ::= jitem_list(mut A) Comma jitem((K,V)) { A.insert(K, V); A }
    jitem ::= JString(K) Colon jobject(V) { (K, V) }
}

fn main() {
    let args = std::env::args().skip(1);

    for arg in args {
        println!("arg: '{}'", arg);
        match arg.parse() {
            Ok::<JObject,_>(j) => println!("JSON: '{:#?}'", j),
            Err(e) => println!("Err: '{:#?}'", e)
        }
    }
}
