#![recursion_limit="256"]
extern crate proc_macro;
extern crate proc_macro2;
#[macro_use]
extern crate syn;
#[macro_use]
extern crate quote;

mod decl;
mod parser;

use decl::*;

use syn::{Ident, Type, token};
use syn::parse::{Parse, Result, Error, ParseStream};
use syn::punctuated::Punctuated;

#[proc_macro]
pub fn pomelo_impl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let Decls(decls) = parse_macro_input!(input);
    let lemon = parser::Lemon::new_from_decls(decls);
    let expanded = lemon.and_then(|mut l| l.build());

    match expanded {
        Ok(expanded) =>  {
            let x = quote!{
                mod pomelo {
                    #expanded
                }
            };
            x.into()
        }
        Err(e) => {
            e.to_compile_error().into()
        }
    }
}

struct Decls(Vec<Decl>);

impl Parse for Decls {
    fn parse(input: ParseStream) -> Result<Decls> {
        let mut decls = Vec::new();
        while !input.is_empty() {
            decls.push(input.parse()?);
        }
        Ok(Decls(decls))
    }
}

mod kw {
    custom_keyword!(include);
    custom_keyword!(left);
    custom_keyword!(right);
    custom_keyword!(nonassoc);
    custom_keyword!(default_type);
    custom_keyword!(extra_argument);
    custom_keyword!(start_symbol);
    custom_keyword!(fallback);
    custom_keyword!(wildcard);
    custom_keyword!(token_class);
    custom_keyword!(token);
}

impl Parse for Decl {
    fn parse(input: ParseStream) -> Result<Decl> {
        if input.peek(Token![%]) {
            input.parse::<Token![%]>()?;
            let lookahead = input.lookahead1();
            if lookahead.peek(Token![type]) {
                // %type ident type;
                input.parse::<Token![type]>()?;
                let ident = input.parse::<Ident>()?;
                let typ = input.parse::<Type>()?;
                input.parse::<Token![;]>()?;
                Ok(Decl::Type(ident, typ))
            } else if lookahead.peek(kw::include) {
                // %include { rust-code } [;]
                input.parse::<kw::include>()?;
                let code;
                braced!(code in input);
                let mut items = Vec::new();
                while !code.is_empty() {
                    items.push(code.parse()?);
                }
                if input.peek(Token![;]) {
                    input.parse::<Token![;]>()?;
                }
                Ok(Decl::Include(items))
            } else if lookahead.peek(kw::left) {
                // %left token1 token2 ... ;
                input.parse::<kw::left>()?;
                let mut toks = Vec::new();
                while !input.peek(Token![;]) {
                    toks.push(input.parse()?);
                }
                input.parse::<Token![;]>()?;
                Ok(Decl::Assoc(Associativity::Left, toks))
            } else if lookahead.peek(kw::right) {
                // %right token1 token2 ... ;
                input.parse::<kw::right>()?;
                let mut toks = Vec::new();
                while !input.peek(Token![;]) {
                    toks.push(input.parse()?);
                }
                input.parse::<Token![;]>()?;
                Ok(Decl::Assoc(Associativity::Right, toks))
            } else if lookahead.peek(kw::nonassoc) {
                // %nonassoc token1 token2 ... ;
                input.parse::<kw::nonassoc>()?;
                let mut toks = Vec::new();
                while !input.peek(Token![;]) {
                    toks.push(input.parse()?);
                }
                input.parse::<Token![;]>()?;
                Ok(Decl::Assoc(Associativity::None, toks))
            } else if lookahead.peek(kw::default_type) {
                // %default_type type;
                input.parse::<kw::default_type>()?;
                let typ = input.parse()?;
                input.parse::<Token![;]>()?;
                Ok(Decl::DefaultType(typ))
            } else if lookahead.peek(kw::extra_argument) {
                // %extra_argument type;
                input.parse::<kw::extra_argument>()?;
                let typ = input.parse()?;
                input.parse::<Token![;]>()?;
                Ok(Decl::ExtraArgument(typ))
            } else if lookahead.peek(kw::start_symbol) {
                // %start_symbol id;
                input.parse::<kw::start_symbol>()?;
                let id = input.parse()?;
                input.parse::<Token![;]>()?;
                Ok(Decl::StartSymbol(id))
            } else if lookahead.peek(kw::fallback) {
                // %fallback id_fall id1 id2 ... ;
                input.parse::<kw::fallback>()?;
                let fallback = input.parse()?;
                let mut ids = Vec::new();
                while !input.peek(Token![;]) {
                    ids.push(input.parse()?);
                }
                input.parse::<Token![;]>()?;
                Ok(Decl::Fallback(fallback, ids))
            } else if lookahead.peek(kw::wildcard) {
                // %wildcard id;
                input.parse::<kw::wildcard>()?;
                let id = input.parse()?;
                input.parse::<Token![;]>()?;
                Ok(Decl::Wildcard(id))
            } else if lookahead.peek(kw::token_class) {
                // %token_class tk id1 id2... ;
                input.parse::<kw::token_class>()?;
                let tk = input.parse()?;
                let mut ids = Vec::new();
                while !input.peek(Token![;]) {
                    ids.push(input.parse()?);
                }
                input.parse::<Token![;]>()?;
                Ok(Decl::TokenClass(tk, ids))
            } else if lookahead.peek(kw::token) {
                // %token enum;
                input.parse::<kw::token>()?;
                let e = input.parse()?;
                input.parse::<Token![;]>()?;
                Ok(Decl::Token(e))
            } else {
                Err(lookahead.error())
            }
        } else {
            // rule: id ::= rhs1 rhs2 ... [ { code } ] [[precedence]] [;]
            // rhs:  id1|id2[(alias)]
            let lhs = input.parse::<Ident>().map_err(|e| Error::new(e.span(), "% or identifier expected"))?;
            input.parse::<Token![::]>()?;
            input.parse::<Token![=]>()?;
            let mut rhs = Vec::new();
            loop {
                let lookahead = input.lookahead1();
                if !lookahead.peek(Ident) {
                    break;
                }
                //rhs
                let toks = Punctuated::<Ident, Token![|]>::parse_separated_nonempty(input)?;
                let toks = toks.into_iter().collect();
                let alias = if input.peek(token::Paren) {
                    let sub;
                    parenthesized!(sub in input);
                    Some(sub.parse()?)
                } else {
                    None
                };
                rhs.push((toks, alias));
            }
            let action = if input.peek(token::Brace) {
                Some(input.parse()?)
            } else {
                None
            };
            let prec = if input.peek(token::Bracket) {
                let sub;
                bracketed!(sub in input);
                Some(sub.parse()?)
            } else {
                None
            };
            if input.peek(Token![;]) {
                input.parse::<Token![;]>()?;
            }
            Ok(Decl::Rule {
                lhs,
                rhs,
                action,
                prec,
            })
        }
    }
}
