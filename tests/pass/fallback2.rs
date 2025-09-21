use pomelo::*;

pomelo! {
    %verbose;
    %include {
        #[derive(Default, Debug)]
        pub struct Counter {
            pub plus: usize,
            pub mul: usize,
        }
    }
    %extra_argument Counter;
    s ::= e;
    e ::= t;
    e ::= e PLUS t { extra.plus += 1; }
    t ::= f;
    t ::= t MUL f { extra.mul += 1; }
    f ::= ID;
    f ::= LP e RP;
    // A fallback should not change the applied rule, if it is valid in the first place.
    %fallback MUL PLUS;
}

use parser::*;

#[test]
fn bug() {
    let v = vec![
        Token::ID,
        Token::PLUS,
        Token::LP,
        Token::ID,
        Token::PLUS,
        Token::LP,
        Token::ID,
        Token::MUL,
        Token::ID,
        Token::RP,
        Token::RP,
    ];
    let mut parser = Parser::new(Counter::default());
    for t in v {
        parser.parse(t).unwrap();
    }
    let (_, extra) = parser.end_of_input().unwrap();
    assert_eq!(extra.plus, 2);
    assert_eq!(extra.mul, 1);
}
