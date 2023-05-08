use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use super::DebugWith;

impl<DB, T: DebugWith<DB>> DebugWith<DB> for &T {
    fn fmt(&self, db: &DB, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        T::fmt(*self, db, f)
    }
}

impl<DB, T: DebugWith<DB>> DebugWith<DB> for &mut T {
    fn fmt(&self, db: &DB, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        T::fmt(*self, db, f)
    }
}

impl<DB, T: DebugWith<DB>> DebugWith<DB> for Box<T> {
    fn fmt(&self, db: &DB, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        T::fmt(&**self, db, f)
    }
}

impl<DB, T: DebugWith<DB>> DebugWith<DB> for std::rc::Rc<T> {
    fn fmt(&self, db: &DB, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        T::fmt(&**self, db, f)
    }
}

impl<DB, T: DebugWith<DB>> DebugWith<DB> for std::sync::Arc<T> {
    fn fmt(&self, db: &DB, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        T::fmt(&**self, db, f)
    }
}

impl<DB, T: DebugWith<DB>, const N: usize> DebugWith<DB> for [T; N] {
    fn fmt(&self, db: &DB, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut list = f.debug_list();
        for value in self.iter() {
            list.entry(&value.debug(db));
        }
        list.finish()
    }
}

impl<DB, T: DebugWith<DB>> DebugWith<DB> for [T] {
    fn fmt(&self, db: &DB, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut list = f.debug_list();
        for value in self.iter() {
            list.entry(&value.debug(db));
        }
        list.finish()
    }
}

impl<DB, T: DebugWith<DB>> DebugWith<DB> for Vec<T> {
    fn fmt(&self, db: &DB, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut list = f.debug_list();
        for value in self.iter() {
            list.entry(&value.debug(db));
        }
        list.finish()
    }
}

impl<DB, T: DebugWith<DB>> DebugWith<DB> for BTreeSet<T> {
    fn fmt(&self, db: &DB, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut set = f.debug_set();
        for value in self.iter() {
            set.entry(&value.debug(db));
        }
        set.finish()
    }
}

impl<DB, T: DebugWith<DB>> DebugWith<DB> for HashSet<T> {
    fn fmt(&self, db: &DB, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut set = f.debug_set();
        for value in self.iter() {
            set.entry(&value.debug(db));
        }
        set.finish()
    }
}

impl<DB, T: DebugWith<DB>, V: DebugWith<DB>> DebugWith<DB> for BTreeMap<T, V> {
    fn fmt(&self, db: &DB, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut map = f.debug_map();
        for (key, value) in self.iter() {
            map.entry(&key.debug(db), &value.debug(db));
        }
        map.finish()
    }
}

impl<DB, T: DebugWith<DB>, V: DebugWith<DB>> DebugWith<DB> for HashMap<T, V> {
    fn fmt(&self, db: &DB, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut map = f.debug_map();
        for (key, value) in self.iter() {
            map.entry(&key.debug(db), &value.debug(db));
        }
        map.finish()
    }
}

macro_rules! impl_tuple {
    ($($T:ident)*) => {
        #[allow(unused_variables, non_snake_case, clippy::unused_unit)]
        impl<DB, $($T: DebugWith<DB>),*> DebugWith<DB> for ($($T,)*) {
            fn fmt(&self, db: &DB, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let ($($T,)*) = self;

                let mut tuple = f.debug_tuple("");

                $( tuple.field(&$T.debug(db)); )*

                tuple.finish()
            }
        }
    };
}

impl_tuple!();
impl_tuple!(A);
impl_tuple!(A B);
impl_tuple!(A B C);
impl_tuple!(A B C D);
impl_tuple!(A B C D E);
impl_tuple!(A B C D E F);
impl_tuple!(A B C D E F G);
impl_tuple!(A B C D E F G H);
impl_tuple!(A B C D E F G H I);
impl_tuple!(A B C D E F G H I J);
impl_tuple!(A B C D E F G H I J K);

