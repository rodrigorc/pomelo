use syn::{Ident, Type, Item, ItemEnum, Block, Pat};

#[derive(Debug, Copy, Clone)]
pub enum Associativity {
    Left,
    Right,
    None,
}

#[derive(Debug)]
pub enum Decl {
    Module(Ident),
    Include(Vec<Item>),
    SyntaxError(Block),
    ParseFail(Block),
    StackOverflow(Block),
    Type(Ident, Type),
    Assoc(Associativity, Vec<Ident>),
    DefaultType(Type),
    ExtraArgument(Type),
    Error(Type),
    StartSymbol(Ident),
    Fallback(Ident, Vec<Ident>),
    Wildcard(Ident),
    TokenClass(Ident, Vec<Ident>),
    Token(ItemEnum),
    ExtraToken(Type),
    StackSize(usize, Option<Type>),
    Verbose,
    Rule {
        lhs: Ident,
        rhs: Vec<(Vec<Ident>, bool, Option<Pat>)>,
        action: Option<Block>,
        prec: Option<Ident>,
    }
}

