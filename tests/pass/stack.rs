use pomelo::*;

pomelo! {
    %include {
        struct Stack<T> {
            data: Vec<T>
        }
        impl<T> Stack<T> {
            fn new() -> Stack<T> {
                Stack {
                    data: Vec::with_capacity(32)
                }
            }
            fn push(&mut self, t: T) {
                self.data.push(t);
                println!("{}", self.data.len());
            }
            fn pop(&mut self) -> Option<T> {
                self.data.pop()
            }
            fn last(&self) -> Option<&T> {
                self.data.last()
            }
            fn is_empty(&self) -> bool {
                self.data.is_empty()
            }
            fn clear(&mut self) {
                self.data.clear();
            }
            fn len(&self) -> usize {
                self.data.len()
            }
        }
    }
    %stack_overflow {
        let tok = match token {
            Some(Token::One(x)) => x,
            _ => unreachable!(),
        };
        assert_eq!(tok, 31);
        assert_eq!(*extra, 31);
        *extra = -1;
        "stack overflow"
    }
    %stack_size 32 Stack;
    %extra_argument i32;
    %error &'static str;
    %type One i32;
    %token #[derive(Debug)] pub enum Token {};
    input ::= list;
    list ::= one;
    list ::= one list; // right recursion, bad! causes stack overflow
    one ::= One { *extra += 1; }
}

use parser::*;

#[test]
fn stack() -> Result<(), ()> {
    let mut p = Parser::new(0);
    for i in 0..1000 {
        match p.parse(Token::One(i)) {
            Ok(_) => {}
            Err(e) => {
                assert_eq!(*p.extra(), -1);
                assert_eq!(e, "stack overflow");
                return Ok(());
            }
        }
    }
    assert!(false);
    Ok(())
    
}
