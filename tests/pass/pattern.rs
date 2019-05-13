use pomelo::*;

pomelo! {
    %type One (i32, u8);
    %type Two String;

    //You can use irrefutable patterns in the LHS rules
    input ::= One((I, U)) Two(mut S) {
        let _i : i32 = I;
        let _u : u8 = U;
        S.push('x');
    }
    //You can ignore typed tokens in LHS rules
    input ::= Two One;
}
