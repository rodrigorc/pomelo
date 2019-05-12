use pomelo::*;

pomelo! {
    //By default the start symbol is the LHS of the first rule
    %start_symbol start;

    nostart ::= ;
    start ::= nostart;
}
