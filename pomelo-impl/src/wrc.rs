use std::rc::{Rc, Weak};

//Like Weak, but cannot be null
#[derive(Debug)]
pub struct WRc<T: ?Sized> {
    w: Weak<T>
}

impl<T: ?Sized> Clone for WRc<T> {
    fn clone(&self) -> WRc<T> {
        let w = self.w.clone();
        WRc { w }
    }
}

impl<'a, T: ?Sized> From<&'a Rc<T>> for WRc<T> {
    fn from(rc: &'a Rc<T>) -> WRc<T> {
        let w = Rc::downgrade(rc);
        WRc { w }
    }
}

impl<T: ?Sized> From<Rc<T>> for WRc<T> {
    fn from(rc: Rc<T>) -> WRc<T> {
        let w = Rc::downgrade(&rc);
        WRc { w }
    }
}

impl<T: ?Sized> From<Weak<T>> for WRc<T> {
    fn from(w: Weak<T>) -> WRc<T> {
        WRc { w }
    }
}

impl<T: ?Sized> WRc<T> {
    pub fn upgrade(&self) -> Rc<T> {
        self.w.upgrade().unwrap()
    }
}

