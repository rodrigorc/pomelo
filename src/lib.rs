#[doc(hidden)]
pub use pomelo_impl::pomelo_impl;

/// TODO macro documentation.
#[macro_export]
macro_rules! pomelo { ($($t:tt)* ) => ( pomelo_impl!{$($t)*} ) }

#[cfg(feature = "lexer")]
pub mod lexer;
