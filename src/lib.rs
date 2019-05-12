pub trait PomeloCallback<Extra> {
    /// Type of the error value.
    type Error;
    /// This is called when a irreducible parser error happens. Current `Parser::parse()` will
    /// return with `Err(e)` being `e` the value returned here.
    fn parse_fail(&mut self, _extra: &mut Extra) -> Self::Error;
    /// This is called when the parser reduces the start token.
    /// The value returned from this function is returned from `Parser::parse_eoi()`.
    fn parse_accept(&mut self, _extra: &mut Extra) -> Result<(), Self::Error> {
        Ok(())
    }
    /// This is called when a syntax error happens. If there are rules that consume
    /// the `error` token, then the parser can still recover.
    fn syntax_error(&mut self, _extra: &mut Extra) {
    }
}

/// This type provides a generic blanket implementation for `PomeloCallback<E>` that just returns a
/// static error message when it fails.
pub struct SimpleCallback;

impl<E> PomeloCallback<E> for SimpleCallback {
    type Error = &'static str;
    fn parse_fail(&mut self, _extra: &mut E) -> Self::Error {
        "Parse failure"
    }
}

#[doc(hidden)]
pub use pomelo_impl::pomelo_impl;

/// TODO macro documentation.
#[macro_export]
macro_rules! pomelo { ($($t:tt)* ) => ( pomelo_impl!{$($t)*} ) }

#[cfg(feature = "lexer")]
pub mod lexer;
