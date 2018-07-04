#![allow(unused_imports)]
extern crate proc_macro;
extern crate proc_macro2;
#[macro_use]
extern crate syn;
#[macro_use]
extern crate quote;

use quote::ToTokens;

use proc_macro2::{TokenTree, TokenStream, Spacing, Delimiter, Group};
use syn::{Ident, Type};

use syn::buffer::{Cursor, TokenBuffer};
use syn::synom::Synom;

/// From procedural_masquerade
#[doc(hidden)]
fn _extract_input(derive_input: &str) -> &str {
    let mut input = derive_input;

    for expected in &["#[allow(unused)]", "enum", "ProceduralMasqueradeDummyType", "{", "Input", "=", "(0,", "stringify!", "("] {
        input = input.trim_left();
        assert!(input.starts_with(expected), "expected prefix {:?} not found in {:?}", expected, derive_input);
        input = &input[expected.len()..];
    }

    for expected in [")", ").0,", "}"].iter().rev() {
        input = input.trim_right();
        assert!(input.ends_with(expected), "expected suffix {:?} not found in {:?}", expected, derive_input);
        let end = input.len() - expected.len();
        input = &input[..end];
    }

    input
}



#[proc_macro_derive(__pomelo_impl)]
pub fn __pomelo_structs_and_impls(input: proc_macro::TokenStream) -> proc_macro::TokenStream {

    let s = input.to_string();
    let input = _extract_input(&s);

    let input : TokenTree = syn::parse_str(input).expect("Syntax error in pomelo! body");

    let buffer = TokenBuffer::new2(input.into_token_stream());
    let cursor = buffer.begin();
    let (rules, cursor) = parse_pomelo(cursor).unwrap();
    println!("RULES {:?}\nREST {}", rules, cursor.token_stream());

    let mut expanded = TokenStream::new();
    if let Decl::Type(ref id, ref _ty) = rules[0] {
        expanded.extend(quote! {
            struct #id
        });
        expanded.extend(quote! {  {}; });
    }
    //println!("OUT: {}", expanded);
    expanded.into()
}

#[derive(Debug)]
enum AssocType {
    Left, Right, None
}

#[derive(Debug)]
enum Decl {
    Type(Ident, Type),
    Assoc(AssocType, Vec<Ident>),
    Rule {
        lhs: Ident,
        rhs: Vec<Ident>,
        action: Option<Group>,
    }
}

named!{parse_declaration -> Decl,
    alt!(
        do_parse!(
            punct!(%) >> keyword!(type) >> ident: syn!(Ident) >> typ: syn!(Type) >> punct!(;) >>
            (Decl::Type(ident, typ))
        )
        |
        do_parse!(
            punct!(%) >> custom_keyword!(left) >> toks: many0!(syn!(Ident)) >> punct!(;) >>
            (Decl::Assoc(AssocType::Left, toks))
        )
        |
        do_parse!(
            punct!(%) >> custom_keyword!(right) >> toks: many0!(syn!(Ident)) >> punct!(;) >>
            (Decl::Assoc(AssocType::Right, toks))
        )
        |
        do_parse!(
            punct!(%) >> custom_keyword!(nonassoc) >> toks: many0!(syn!(Ident)) >> punct!(;) >>
            (Decl::Assoc(AssocType::None, toks))
        )
        |
        do_parse!(
            lhs: syn!(Ident) >>
            punct!(->) >>
            rhs: many0!(syn!(Ident)) >>
            action: alt!(
                do_parse!(
                    punct!(=>) >>
                    action: syn!(Group) >>
                    (Some(action))
                )
                |
                punct!(;) => { |_| None }
            ) >>
            (Decl::Rule { lhs, rhs, action })
        )
    )
}

named!{parse_pomelo -> Vec<Decl>,
    map!(braces!(many0!(parse_declaration)), |(_,r)| r)
}

