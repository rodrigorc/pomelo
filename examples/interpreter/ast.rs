#![allow(dead_code)]

#[rustfmt::skip]
#[derive(Debug)]
pub enum BinOp {
    Plus, Minus,
    Mult, Div,
    Equal, NotEqual,
    And, Or,
    Less, Greater, LessEq, GreaterEq,
    Assign,
}

#[derive(Debug)]
pub enum UnaOp {
    Neg,
    Not,
}

#[derive(Debug)]
pub enum Expr {
    Number(i64),
    String(String),
    Variable(String),
    BinaryOp(BinOp, Box<(Expr, Expr)>),
    UnaryOp(UnaOp, Box<Expr>),
    Call(String, Vec<Expr>),
}

#[derive(Debug)]
pub enum Stmt {
    Expr(Expr),
    Block(Vec<Stmt>),
    If(Expr, Box<(Stmt, Option<Stmt>)>),
    While(Expr, Box<Stmt>),
    Return(Option<Expr>),
    Break,
    Continue,
}

#[derive(Debug)]
pub struct Function {
    name: String,
    args: Vec<String>,
    code: Vec<Stmt>,
}

#[derive(Debug)]
pub struct Variable {
    name: String,
    ini: Expr,
}

#[derive(Debug)]
pub struct Program {
    funcs: Vec<Function>,
    vars: Vec<Variable>,
}

impl Function {
    pub fn new(name: String, args: Vec<String>, code: Vec<Stmt>) -> Function {
        Function { name, args, code }
    }
}

impl Variable {
    pub fn new(name: String, ini: Expr) -> Variable {
        Variable { name, ini }
    }
}

impl Program {
    pub fn new() -> Program {
        Program {
            funcs: Vec::new(),
            vars: Vec::new(),
        }
    }
    pub fn add_function(&mut self, f: Function) {
        self.funcs.push(f);
    }
    pub fn add_variable(&mut self, v: Variable) {
        self.vars.push(v);
    }
}
