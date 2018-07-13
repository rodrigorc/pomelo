#[allow(unused_imports)]
#[macro_use]
extern crate pomelo_impl;

pub trait PomeloCallback<Extra> {
    type Error;
    fn parse_accept(&mut self, _extra: &mut Extra) -> Result<(), Self::Error> {
        Ok(())
    }
    fn syntax_error(&mut self, _extra: &mut Extra) {
    }
    fn parse_fail(&mut self, _extra: &mut Extra) -> Self::Error;
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
            //#[derive(Debug)]
            pub enum Token<'a, 'b: 'a, T: 'a + 'b>
                where T: ::std::fmt::Display { };

        %type PHANTOM1 ::std::marker::PhantomData<&'a T>;
        %type PHANTOM2 ::std::marker::PhantomData<&'b T>;
        %type IValue i32;
        %type SValue T;
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
        expr ::= SValue(S)              { S.to_string().len() as i32 }
    }

    struct TestCB;
    impl PomeloCallback<i32> for TestCB {
        type Error = String;
        fn parse_accept(&mut self, extra: &mut i32) -> Result<(), Self::Error> {
            println!("Parse accepted: {}", *extra);
            Ok(())
        }
        fn parse_fail(&mut self, extra: &mut i32) -> Self::Error {
            *extra = -1;
            println!("Parse failed");
            "Parse failed!".to_string()
        }
        fn syntax_error(&mut self, _extra: &mut i32) {
            println!("Syntax error");
        }
    }

    #[test]
    fn it_works() -> Result<(), String> {
        use self::parser::*;
        let x = String::from("abc");
        let mut p = Parser::new(0, TestCB);
        //println!("t={:?}", Token::Plus);
        let toks = vec![
            Token::IValue(2),
            Token::Plus,
            Token::IValue(4),
            Token::Plus,
            Token::Minus,
            Token::IValue(1),
            Token::Minus,
            Token::SValue(&x[..]),
        ];
        for tok in toks.into_iter() {
            p = p.parse(tok)?;
        }
        for i in 0..10000000 {
            p = p.parse(Token::Plus)?;
            p = p.parse(Token::IValue(i))?;
            p = p.parse(Token::Minus)?;
            p = p.parse(Token::IValue(i))?;
        }
        let r = p.parse_eoi()?;
        println!("RES {}", r);
        assert!(r == 2);
        Ok(())
    }
}
