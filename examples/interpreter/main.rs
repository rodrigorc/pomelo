use std::fs::File;
use std::io::{self, BufReader, ErrorKind};

mod lexer;
use lexer::Lexer;

mod parser;

mod ast;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 2 {
        eprintln!("Syntax: {} <program>", args[0]);
        return;
    }
    match main2(&args[1]) {
        Ok(_) => (),
        Err(e) => {
            eprintln!("Error: {}", e);
        }
    }
}

fn main2(file: &str) -> io::Result<()> {
    let file = File::open(file)?;
    let file = BufReader::new(file);
    let lex = Lexer::new(file);

    let mut parser = parser::Parser::new(ast::Program::new());
    for token in lex {
        let token = token?;
        parser.parse(token).map_err(|_| ErrorKind::InvalidInput)?;
    }
    let prg = parser.end_of_input().map_err(|_| ErrorKind::InvalidInput)?;
    println!("{:#?}", prg);
    Ok(())
}
