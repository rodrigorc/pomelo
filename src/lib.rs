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

pub enum Foo {
}

#[cfg(test)]
mod tests {

    pomelo! {
        %type IValue i32;
        %type expr i32;
        %left Plus Minus;
        //%extra_argument ();

        input <- expr(A) => { println!("RES = {}", A) }
        expr <- expr(A) Plus expr(B) => { A + B }
        expr <- expr(A) Minus expr(B) => { A - B }
        expr <- IValue(A) => { A }
    }

    #[test]
    fn it_works() {
        use self::parser::*;
        let mut p = Parser::new(());
        p.parse(Token::IValue(2));
        p.parse(Token::Plus);
        p.parse(Token::IValue(4));
        p.parse(Token::Plus);
        p.parse(Token::IValue(7));
        p.parse(Token::EOI);
    }
}
