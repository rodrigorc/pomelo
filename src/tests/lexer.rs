use super::PomeloCallback;

pomelo! {
    input ::= ;
    input ::= token_list;
    token_list ::= token;
    token_list ::= token_list sep_list token;

    sep_list ::= Space;
    sep_list ::= sep_list Space;

    token ::= keyword;
    token ::= punct;

    punct ::= Punct;
    keyword ::= AlphaNumChar;
    keyword ::= keyword AlphaNumChar;
}
