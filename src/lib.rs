#![allow(unused_imports)]
#[macro_use]
extern crate pomelo_impl;

#[macro_export]
macro_rules! pomelo {
    ($($body:tt)*) => {
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
        %type IValue i32;
        %type expr i32;
        %left Plus Minus;
        %extra_argument i32;

        input <- expr(A) => { *extra = A; }
        expr <- expr(A) Plus expr(B) => { A + B }
        expr <- expr(A) Minus expr(B) => { A - B }
        expr <- IValue(A) => { A }
    }

    #[test]
    fn it_works() {
        use self::parser::*;
        let mut p = Parser::new(0);
        p.parse(Token::IValue(2));
        p.parse(Token::Plus);
        p.parse(Token::IValue(4));
        p.parse(Token::Minus);
        p.parse(Token::IValue(1));
        p.parse(Token::Minus);
        p.parse(Token::IValue(0));
        p.parse_eoi();
        let r = p.into_extra();
        println!("RES {}", r);
        assert!(r == 5);
    }
}
