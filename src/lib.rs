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

#[macro_export]
macro_rules! pomelo {
    ($($body:tt)*) => {
        #[allow(unused)]
        #[derive(__pomelo_impl)]
        enum ProceduralMasqueradeDummyType {
            Input = (0,stringify!( { $($body)* })).0
        }
    };
}

#[cfg(test)]
mod tests;
