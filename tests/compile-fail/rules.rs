extern crate pomelo;
use pomelo::*;

pomelo! {
    input ::= foo;
           //~^ ERROR Nonterminal has no rules
}

pomelo! {
    input ::= ;
    Foo ::= ;
 //~^ ERROR LHS of rule must be non-terminal
}

pomelo! {
    input ::= A|B|c;
               //~^ ERROR Cannot form a compound containing a non-terminal
}

pomelo! {
    input ::= A [foo];
               //~^ ERROR The precedence symbol must be a token
}

fn main() {}
