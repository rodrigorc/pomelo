#![allow(unused_imports)]
#[macro_use]
extern crate pomelo_impl;

pub trait PomeloCallback<Extra> {
    fn syntax_error(&mut self, extra: &mut Extra);
    fn parse_fail(&mut self, extra: &mut Extra);
    fn parse_accept(&mut self, extra: &mut Extra);
}

#[macro_export]
macro_rules! pomelo {
    ($($body:tt)*) => {
        use PomeloCallback;
        #[allow(unused)]
        #[derive(__pomelo_impl)]
        enum ProceduralMasqueradeDummyType {
            Input = (0,stringify!( { $($body)* })).0
        }
    };
}

#[cfg(test)]
mod tests {

    pomelo! {
        %token
            #[derive(Debug)]
            pub enum Token<'a> { };

        %type IValue i32;
        %type SValue &'a str;
        %type expr i32;
        %left Plus Minus;
        %left Neg;
        %extra_argument i32;
        %start_symbol input;

        input ::= expr(A)               { *extra = A; }
        expr ::= expr(A) Plus expr(B)   { A + B }
        expr ::= expr(A) Minus expr(B)  { A - B }
        expr ::= Minus expr(A) [Neg]    { -A }
        expr ::= IValue(A)              { A }
        expr ::= SValue(S)              { S.len() as i32 }
    }

    struct TestCB;
    impl PomeloCallback<i32> for TestCB {
        fn syntax_error(&mut self, _extra: &mut i32) {
            println!("Syntax error");
        }
        fn parse_fail(&mut self, extra: &mut i32) {
            *extra = -1;
            println!("Parse failed");
        }
        fn parse_accept(&mut self, extra: &mut i32) {
            println!("Parse accepted: {}", *extra);
        }
    }

    #[test]
    fn it_works() {
        use self::parser::*;
        let x = String::from("abc");
        let mut p = Parser::new(0, TestCB);
        println!("t={:?}", Token::Plus);
        p.parse(Token::IValue(2));
        p.parse(Token::Plus);
        p.parse(Token::IValue(4));
        p.parse(Token::Plus);
        p.parse(Token::Minus);
        p.parse(Token::IValue(1));
        p.parse(Token::Minus);
        p.parse(Token::SValue(&x));
        p.parse_eoi();
        let r = p.into_extra();
        println!("RES {}", r);
        assert!(r == 2);
    }
}
