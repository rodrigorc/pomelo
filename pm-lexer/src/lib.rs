use proc_macro2::{Delimiter, Punct, Spacing, TokenStream, TokenTree};

pub fn parse<E, F>(toks: TokenStream, mut f: F) -> Result<(), E>
where
    F: FnMut(&TokenTree) -> Result<(), E>,
{
    parse2(toks, &mut f)
}

fn parse2<E>(toks: TokenStream, f: &mut impl FnMut(&TokenTree) -> Result<(), E>) -> Result<(), E> {
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
                    f(&TokenTree::Punct(Punct::new(l, Spacing::Alone)))?;
                }
                parse2(g.stream(), f)?;
                if r != ' ' {
                    f(&TokenTree::Punct(Punct::new(r, Spacing::Alone)))?;
                }
            }
            tt => {
                f(&tt)?;
            }
        }
    }
    Ok(())
}
