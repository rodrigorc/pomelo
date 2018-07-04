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
        %type IVALUE Vec<Vec<i32>>;
        %type expr i32;
        %type FVALUE i32;
        //%left PLUS MINUS;

        //expr -> IVALUE|FVALUE(A) => { A }
        //expr -> expr(A) PLUS expr(B) => { A + B }
        expr -> LPAREN expr RPAREN;
        expr -> LPAREN expr RPAREN => {
            A + 1;
            A
        }
    }

    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
