use std::borrow::Borrow;
use std::cell::{Ref, RefCell, RefMut};

#[derive(Debug, Clone)]
pub struct VecRef<T> {
    data: Vec<RefCell<T>>,
}

impl<T> VecRef<T> {
    pub fn new() -> VecRef<T> {
        VecRef { data: Vec::new() }
    }
    pub fn push(&mut self, t: T) -> VecRefId<T> {
        let id = self.data.len();
        self.data.push(RefCell::new(t));
        VecRefId {
            id,
            _pd: std::marker::PhantomData,
        }
    }
    pub fn get(&self, id: impl Borrow<VecRefId<T>>) -> Ref<T> {
        self.data[id.borrow().id].borrow()
    }
    pub fn get_mut(&self, id: impl Borrow<VecRefId<T>>) -> RefMut<T> {
        self.data[id.borrow().id].borrow_mut()
    }
}

#[derive(Debug)]
pub struct VecRefId<T> {
    id: usize,
    _pd: std::marker::PhantomData<T>,
}

impl<T> Copy for VecRefId<T> {}

impl<T> Clone for VecRefId<T> {
    fn clone(&self) -> Self {
        VecRefId {
            id: self.id,
            _pd: std::marker::PhantomData,
        }
    }
}
impl<T> PartialEq for VecRefId<T> {
    fn eq(&self, o: &Self) -> bool {
        self.id == o.id
    }
}

impl<T> Eq for VecRefId<T> {}

impl<T> std::hash::Hash for VecRefId<T> {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        self.id.hash(h)
    }
}

impl<T> VecRefId<T> {
    pub fn dangling() -> VecRefId<T> {
        VecRefId {
            id: std::usize::MAX,
            _pd: std::marker::PhantomData,
        }
    }
}
