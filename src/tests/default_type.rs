use super::*;

pomelo! {
    %default_type Option<i32>;

    input ::= Terminal(T) { let _x : Option<i32> = T; }
}
