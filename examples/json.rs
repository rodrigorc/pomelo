///! Example of how to use Logos with Pomelo.
///! You can use separated enums for the output of Logos and the input of Pomelo
///! and do a match, or with a bit of imagination you can use the same enum for both!

use pomelo::pomelo;
use std::collections::HashMap;
use logos::Logos;

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
        let mut lex = json::Token::lexer(input);

        while let Some(tk) = lex.next() {
            p.parse(tk).map_err(|_| format!(r#"Parser error at: {:?} "{}""#, lex.span(), lex.slice()))?;
        }
        let j = p.end_of_input().map_err(|_| "Parser error: unexpected EOF")?;
        Ok(j)
    }
}

pomelo! {
    %module json;
    %include {
        use super::JObject;
        use std::collections::HashMap;
        use logos::{Logos, Lexer};

        fn parse_number(lex: &Lexer<Token>) -> Result<i64, std::num::ParseIntError> {
            let s = lex.slice();
            s.parse()
        }
        fn parse_string(lex: &Lexer<Token>) -> String {
            let s = lex.slice();
            String::from(&s[1 .. s.len() - 1])
        }
    }
    %token #[derive(Debug, Logos)] pub enum Token { };

    %type 
        #[error]
        #[regex(r"[ \t\r\n\f]+", logos::skip)]
        Error;
    %type #[token("{")] LBrace;
    %type #[token("}")] RBrace;
    %type #[token("[")] LBracket;
    %type #[token("]")] RBracket;
    %type #[token(",")] Comma;
    %type #[token(":")] Colon;
    %type #[regex("[0-9]+", parse_number)] JNumber i64;
    %type #[regex(r#""([^"]|\\")*""#, parse_string)] JString String;
    %type #[token("null")] JNull;
    %type #[token("true")] JTrue;
    %type #[token("false")] JFalse;

    %type start JObject;
    %type jobject JObject;
    %type jdict JObject;
    %type jarray JObject;
    %type jobject_list Vec<JObject>;
    %type jitem_list HashMap<String, JObject>;
    %type jitem (String, JObject);

    start ::= jobject(J) { J }

    jobject ::= jdict(D) { D }
    jobject ::= jarray(A) { A }
    jobject ::= JNumber(N) { JObject::JNumber(N) }
    jobject ::= JString(S) { JObject::JString(S) }
    jobject ::= JTrue { JObject::JBool(true) }
    jobject ::= JFalse { JObject::JBool(false) }
    jobject ::= JNull { JObject::JNull }

    jdict ::= LBrace jitem_list?(D) RBrace { JObject::JDict(D.unwrap_or_else(HashMap::new)) }

    jarray ::= LBracket jobject_list?(A) RBracket { JObject::JArray(A.unwrap_or_else(Vec::new)) }

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
            Err(e) => println!("Err: '{}'", e)
        }
    }
}
