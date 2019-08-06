use pomelo::*;

pomelo! {
    %include {
        //This use should not affect the generated code in any way
        #[allow(unused_imports)]
        use std::io::Result;
    }
    %error String;
    start ::= ;
}
