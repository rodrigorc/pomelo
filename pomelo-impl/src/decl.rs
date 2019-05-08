use syn::{Ident, Type, Item, ItemEnum, Block, Pat};

#[derive(Debug, Copy, Clone)]
pub enum Associativity {
    Left,
    Right,
    None,
}

#[derive(Debug)]
pub enum Decl {
    Include(Vec<Item>),
    Type(Ident, Type),
    Assoc(Associativity, Vec<Ident>),
    DefaultType(Type),
    ExtraArgument(Type),
    StartSymbol(Ident),
    Fallback(Ident, Vec<Ident>),
    Wildcard(Ident),
    TokenClass(Ident, Vec<Ident>),
    Token(ItemEnum),
    Rule {
        lhs: Ident,
        rhs: Vec<(Vec<Ident>, Option<Pat>)>,
        action: Option<Block>,
        prec: Option<Ident>,
    }
}

