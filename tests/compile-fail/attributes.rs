extern crate pomelo;
use pomelo::*;

pomelo! {
    //Attributes only in termninals
    %type #[doc("foo")] A;
    %type #[doc("foo")] B i8;

    %type #[doc("foo")] x i8;
       //~^ ERROR Non terminal symbol cannot have attributes
    input ::= ;
}

fn main() {}
