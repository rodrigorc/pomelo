use pomelo::*;

pomelo! {
    %type input String;
    %type number String;
    %type Number String;

    input ::= number;
    number ::= Number;
    number ::= LParen Number RParen;
}
