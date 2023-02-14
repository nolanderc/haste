use crate::{arena::Arena, Id, ContainerPath};

pub struct InputStorage<T> {
    path: ContainerPath,
    arena: Arena<T>,
}

impl<T: 'static> crate::Container for InputStorage<T> {
    fn new(path: ContainerPath) -> Self {
        Self {
            path,
            arena: Default::default(),
        }
    }
}

impl<T: 'static> crate::DynContainer for InputStorage<T> {
    fn path(&self) -> ContainerPath {
        self.path
    }
}

impl<T: 'static> crate::ElementContainer for InputStorage<T> {
    type Value = T;

    type Ref<'a> = &'a T where T: 'a;

    fn insert(&self, value: T) -> Id {
        let index = self.arena.push(value);
        Id::try_from_usize(index).unwrap()
    }

    fn get_untracked(&self, id: Id) -> Self::Ref<'_> {
        self.arena.get(id.raw.get() as _).unwrap()
    }
}

impl<T: 'static> crate::InputContainer for InputStorage<T> {
    type RefMut<'a> = &'a mut T where T: 'a;

    fn get_mut(&mut self, id: crate::Id) -> Self::RefMut<'_> {
        self.arena.get_mut(id.raw.get() as _).unwrap()
    }
}
