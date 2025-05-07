use pomelo::*;

pomelo! {
    %module orange;
    start ::= ;
}

#[test]
fn test() {
    let _: orange::Token;
}
