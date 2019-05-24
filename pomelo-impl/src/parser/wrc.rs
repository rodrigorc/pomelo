use std::rc::{Rc, Weak};
use std::cell::{RefCell, Ref, RefMut};

//A reference-counted RefCell
pub type RCell<T> = Rc<RefCell<T>>;

//Like Weak<RefCell>, but cannot be null
#[derive(Debug)]
pub struct WRCell<T> {
    w: Weak<RefCell<T>>
}

impl<T> Clone for WRCell<T> {
    fn clone(&self) -> WRCell<T> {
        let w = self.w.clone();
        WRCell { w }
    }
}

impl<'a, T> From<&'a RCell<T>> for WRCell<T> {
    fn from(rc: &'a RCell<T>) -> WRCell<T> {
        let w = RCell::downgrade(rc);
        WRCell { w }
    }
}

impl<T> From<RCell<T>> for WRCell<T> {
    fn from(rc: RCell<T>) -> WRCell<T> {
        let w = RCell::downgrade(&rc);
        WRCell { w }
    }
}

impl<T> WRCell<T> {
    pub fn upgrade(&self) -> RCell<T> {
        self.w.upgrade().unwrap()
    }
    pub fn borrow(&self) -> RCellRef<T> {
        let p = self.w.upgrade().unwrap();
        let raw = &*p as *const RefCell<T>;
        let r = unsafe { (*raw).borrow() };
        RCellRef { _p: p, r }
    }
    pub fn borrow_mut(&self) -> RCellRefMut<T> {
        let p = self.upgrade();
        let raw = &*p as *const RefCell<T>;
        let r = unsafe { (*raw).borrow_mut() };
        RCellRefMut { _p: p, r }
    }
}

impl<T> PartialEq for WRCell<T> {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.w.upgrade().unwrap(), &other.w.upgrade().unwrap())
    }
}

impl <T> Eq for WRCell<T> {}

//this wraps an RC and a borrow, the borrow cannot be out of scope while
//the RC is alive, so it is effectively 'static
pub struct RCellRef<T: 'static> {
    _p: RCell<T>,
    r: Ref<'static, T>,
}

impl<T> std::ops::Deref for RCellRef<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.r
    }
}

pub struct RCellRefMut<T: 'static> {
    _p: RCell<T>,
    r: RefMut<'static, T>,
}

impl<T> std::ops::Deref for RCellRefMut<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.r
    }
}

impl<T> std::ops::DerefMut for RCellRefMut<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.r
    }
}

