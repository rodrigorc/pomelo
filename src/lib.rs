#[allow(unused_imports)]
#[macro_use]
extern crate pomelo_impl;

pub trait PomeloCallback<Extra> {
    type Error;
    fn parse_accept(&mut self, _extra: &mut Extra) -> Result<(), Self::Error> {
        Ok(())
    }
    fn syntax_error(&mut self, _extra: &mut Extra) {
    }
    fn parse_fail(&mut self, _extra: &mut Extra) -> Self::Error;
}

pub use pomelo_impl::pomelo;

#[cfg(test)]
mod tests;
