pub use syn::{Ident, Type};
pub use proc_macro2::{Group, TokenStream};

#[derive(Debug, Copy, Clone)]
pub enum Associativity {
    Left,
    Right,
    None,
}

#[derive(Debug)]
pub enum Decl {
    Type(Ident, Type),
    Assoc(Associativity, Vec<Ident>),
    DefaultType(Type),
    ExtraArgument(Type),
    StartSymbol(Ident),
    Fallback(Ident, Vec<Ident>),
    Wildcard(Ident),
    TokenClass(Ident, Vec<Ident>),
    Rule {
        lhs: Ident,
        rhs: Vec<(Vec<Ident>, Option<Ident>)>,
        action: Option<Group>,
        prec: Option<Ident>,
    }
}

