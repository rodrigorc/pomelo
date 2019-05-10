use proc_macro2::{TokenTree, TokenStream, Punct, Spacing};

pub fn parse<E>(toks: TokenStream, mut f: impl FnMut(&TokenTree) -> Result<(), E>) -> Result<(), E> {
    parse2(toks, &mut f)
}

fn parse2<E>(toks: TokenStream, f: &mut impl FnMut(&TokenTree) -> Result<(), E>)  -> Result<(), E> {
    for tk in toks {
        match tk {
            TokenTree::Group(g) => {
                f(&TokenTree::Punct(Punct::new('(', Spacing::Alone)))?;
                parse2(g.stream(), f)?;
                f(&TokenTree::Punct(Punct::new(')', Spacing::Alone)))?;
            }
            tt => { f(&tt)?; }
        }
    }
    Ok(())
}
