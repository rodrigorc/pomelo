use pomelo::*;

pomelo! {
    %module A;
    %parser pub struct Parser<'a, 'b> {};
    %extra_argument (Vec<&'a i32>, &'b str);
    %type Index &'a i32;
    %token pub enum Token<'a> {};

    reference ::= Index(i) {
        println!("{}", extra.1);
        extra.0.push(i);
    }
}

pomelo! {
    %module B;
    %include {
        use std::fmt::Debug;
    }
    %parser pub struct Parser<A, B, C>
        where A: Debug,
              B: Debug + Default
        {};
    %extra_argument Vec<(A, B)>;
    %token pub enum Token<A, C> {};
    %type Index (A, C);

    input ::= Index(i) {
        println!("{:?}", extra);
        extra.push((i.0, B::default()));
    }
}
