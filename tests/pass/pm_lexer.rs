use proc_macro2::{Delimiter, TokenStream, TokenTree};

pub enum PmToken {
    Char(char),
    Literal(String),
}

pub fn parse<E, F>(toks: TokenStream, mut f: F) -> Result<(), E>
where
    F: FnMut(PmToken) -> Result<(), E>,
{
    parse2(toks, &mut f)
}

fn parse2<E>(toks: TokenStream, f: &mut impl FnMut(PmToken) -> Result<(), E>) -> Result<(), E> {
    for tk in toks {
        match tk {
            TokenTree::Group(g) => {
                let (l, r) = match g.delimiter() {
                    Delimiter::Parenthesis => ('(', ')'),
                    Delimiter::Brace => ('{', '}'),
                    Delimiter::Bracket => ('[', ']'),
                    Delimiter::None => (' ', ' '),
                };
                if l != ' ' {
                    f(PmToken::Char(l))?;
                }
                parse2(g.stream(), f)?;
                if r != ' ' {
                    f(PmToken::Char(r))?;
                }
            }
            TokenTree::Punct(p) => {
                let c = p.as_char();
                f(PmToken::Char(c))?;
            }
            TokenTree::Literal(l) => {
                f(PmToken::Literal(l.to_string()))?;
            }
            _ => panic!(),
        }
    }
    Ok(())
}
