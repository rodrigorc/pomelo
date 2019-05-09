extern crate pomelo as pm;

use pm::*;

pomelo! {
    input ::= foo;
    foo ::= input;
     //~^ ERROR start symbol on the RHS of a rule
}

