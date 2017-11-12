/// The namespace tree structure storing named ty (sub-namespace) and value
/// objects, providing name resolution.

// TODO: Change raw pointers to `Shared<_>` when stable.

use std::collections::hash_map::{HashMap, Iter as HashMapIter};
use std::ptr::null_mut;
use std::mem::forget;
use super::{Path, ValPath};
use self::ResolveError::*;

/// The preparatory namespace tree with some name queries waiting to be
/// resolved.
#[derive(Debug)]
pub struct PreNameSp<'t, T, V> {
    root: *mut Node<'t, T, V>,
}

/// The final namespace tree with all name queries resolved.
#[derive(Debug)]
pub struct NameSp<'t, T, V>(Box<Node<'t, T, V>>);

/// The pointer to a (sub-)namespace on a namespace tree.
#[derive(Debug, Clone)]
pub struct NameSpPtr<'a, 't: 'a, T: 'a, V: 'a> {
    root: &'a Node<'t, T, V>,
    cur:  &'a Node<'t, T, V>,
}

#[derive(Debug)]
struct NameSpMutPtr<'t, T, V> {
    root: *mut Node<'t, T, V>,
    cur:  *mut Node<'t, T, V>,
}

#[derive(Debug)]
enum ResolveState<P, T> {
    Waiting { path: P, visiting: bool },
    /// `None` for that error has been emitted before.
    Done    (Option<T>),
}

#[derive(Debug)]
struct UseNameState<'t, T, V> {
    as_sub: ResolveState<Path<'t>, *mut Node<'t, T, V>>,
    as_val: ResolveState<ValPath<'t>, *mut V>,
}

#[derive(Debug)]
enum UseSpaceState<'t, T, V> {
    Waiting { path: Path<'t>, visiting: bool },
    Resolved{ sub: *mut Node<'t, T, V> },
}

#[derive(Debug)]
pub enum ResolveError<'t> {
    Cycle,
    NotFound      (&'t str),
    TooManySupers { nth: usize },
    /// Current name resolving is skipped due to a previous error.
    Skip          { name: &'t str, prev: Box<ResolveError<'t>> },
}

#[derive(Debug)]
struct Node<'t, T, V> {
    /// The pointer to the father node.
    father:      *mut Node<'t, T, V>,
    /// Sub namespaces. May be `mod`, `struct` or a block.
    subs:        HashMap<&'t str, *mut Node<'t, T, V>>,
    /// Namespaces imported by `use ...::*`. When the namespace is frozen
    /// (`NameSp`), it must all hold `Resolved`.
    use_spaces:  Vec<UseSpaceState<'t, T, V>>,
    /// Names imported by `use`. When the namespace is frozen (`NameSp`), it
    /// must be empty and all names will be added into `subs` or `values`.
    use_names:   HashMap<&'t str, UseNameState<'t, T, V>>,
    /// Information of this namespace.
    info:        T,
    /// Values in this namespace.
    values:      HashMap<&'t str, V>,
}

pub struct SubIter<'a, 't: 'a, T: 'a, V: 'a> {
    root: &'a Node<'t, T, V>,
    iter: HashMapIter<'a, &'t str, *mut Node<'t, T, V>>,
}

impl<'t, T, V> Clone for NameSpMutPtr<'t, T, V> {
    fn clone(&self) -> Self {
        NameSpMutPtr { root: self.root, cur: self.cur }
    }
}

impl<'t, T, V> NameSpMutPtr<'t, T, V> {
    pub fn root(&self) -> Self {
        NameSpMutPtr { root: self.root, cur: self.root }
    }

    pub fn father(&self) -> Option<Self> {
        unsafe {
            (*self.cur).father.as_mut()
                .map(|cur| NameSpMutPtr { root: self.root, cur })
        }
    }

    fn move_to(&self, ptr: *mut Node<'t, T, V>) -> Self {
        NameSpMutPtr { root: self.root, cur: ptr }
    }

    unsafe fn walk_resolve(
        &mut self,
        path: &Path<'t>,
    ) -> Result<Self, ResolveError<'t>> {
        let mut c = self.clone();
        let comps = match *path {
            Path::Absolute{ ref comps } => {
                c = c.root();
                comps
            },
            Path::Relative{ supers, ref comps } => {
                for nth in 0..supers {
                    c = c.father() // None in the root namespace
                        .ok_or(TooManySupers { nth })?;
                }
                comps
            },
        };
        for &name in comps.iter() {
            match c.resolve_sub(name) {
                Ok(Some(sub)) =>
                    c = sub,
                Ok(None) =>
                    return Err(NotFound(name)),
                Err(prev) =>
                    return Err(Skip { name, prev: Box::new(prev) }),
            }
        }
        Ok(c)
    }

    /// Resolve usings of the namespace tree.
    unsafe fn resolve_tree(mut self) -> Vec<ResolveError<'t>> {
        let node = &mut *self.cur;
        let mut errs = vec![];
        { // TODO: ugly
            let mut f = |e: Option<ResolveError<'t>>| if let Some(e) = e {
                errs.push(e)
            };
            for st in node.use_names.values_mut() {
                f(self.resolve_use_name_as_sub(st).err());
                f(self.resolve_use_name_as_val(st).err());
            }
            for st in node.use_spaces.iter_mut() {
                f(self.resolve_use_space(st).err());
            }
            for &sub in node.subs.values() {
                self.move_to(sub).resolve_tree().into_iter();
            }
        }
        errs
    }

    /// Resolve a name of sub namespace.
    unsafe fn resolve_sub(
        &mut self,
        name: &'t str,
    ) -> Result<Option<Self>, ResolveError<'t>> {
        match (*self.cur).subs.get(name) {
            Some(&psub) => Ok(Some(self.move_to(psub))),
            None => match (*self.cur).use_names.get_mut(name) {
                Some(st) => self.resolve_use_name_as_sub(st),
                None => unimplemented!(),
            },
        }
    }

    unsafe fn resolve_val(
        self,
        name: &'t str,
    ) -> Result<Option<*mut V>, ResolveError<'t>> {
        // (*self.cur).values.get(name) // 0. current
        //     .or_else(|| (*self.cur).use_names.get_mut(name) // 1. use name
        //                     .and_then(|st| self.resolve_use_name_as_val(st)))
        unimplemented!()
    }

    unsafe fn resolve_use_name_as_sub<'a>(
        &mut self,
        st: *mut UseNameState<'t, T, V>, // may not have unique access (cycle)
    ) -> Result<Option<Self>, ResolveError<'t>> {
        use self::ResolveState::*;
        let (path, visiting): (_, *mut bool) = match (*st).as_sub {
            Done(None) =>
                return Ok(None),
            Done(Some(pos)) =>
                return Ok(Some(self.move_to(pos))),
            Waiting{ ref path, ref mut visiting } =>
                (path, visiting),
        };
        if *visiting {
            (*st).as_sub = Done(None);
            Err(ResolveError::Cycle)
        } else { // TODO: ugly
            *visiting = true;
            let ret = self.walk_resolve(path);
            *visiting = false;
            (*st).as_sub = Done(None);
            let target = ret?;
            (*st).as_sub = Done(Some(target.cur));
            Ok(Some(target))
        }
    }

    unsafe fn resolve_use_name_as_val<'a>(
        &mut self,
        st: *mut UseNameState<'t, T, V>, // may not have unique access (cycle)
    ) -> Result<Option<*mut V>, ResolveError<'t>> {
        use self::ResolveState::*;
        let (path, visiting): (_, *mut bool) = match (*st).as_val {
            Done(None) =>
                return Ok(None),
            Done(Some(pos)) =>
                return Ok(Some(pos)),
            Waiting{ ref path, ref mut visiting } =>
                (path, visiting),
        };
        if *visiting {
            (*st).as_val = Done(None);
            Err(ResolveError::Cycle)
        } else { // TODO: ugly
            *visiting = true;
            let ret = self.walk_resolve(&path.0)
                .and_then(|ori_ns| ori_ns.resolve_val(path.1));
            *visiting = false;
            (*st).as_val = Done(None);
            let opt_ptr = ret?;
            (*st).as_val = Done(opt_ptr);
            Ok(opt_ptr)
        }
    }

    unsafe fn resolve_use_space(
        &mut self,
        st: &mut UseSpaceState<'t, T, V>,
    ) -> Result<(), ResolveError<'t>> {
        unimplemented!()
    }
}

impl<'a, 't: 'a, T: 'a, V: 'a> Iterator for SubIter<'a, 't, T, V> {
    type Item = (&'t str, NameSpPtr<'a, 't, T, V>);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
            .map(|(&name, &p)| unsafe {
                let cur = p.as_ref().unwrap(); // not null
                (name, NameSpPtr{ root: self.root, cur })
            })
    }
}

impl<'t, T, V> PreNameSp<'t, T, V> {
    /// Create an empty namespace with custom infomation `T`.
    pub fn new(info: T) -> Self {
        let node = Box::new(Node {
            father:      null_mut(),
            subs:        HashMap::new(),
            use_spaces:  vec![],
            use_names:   HashMap::new(),
            info,
            values:      HashMap::new(),
        });
        PreNameSp { root: Box::into_raw(node) }
    }

    /// Add a sub-namespace and return the old one with the same name (if any).
    pub fn add_sub(
        &mut self,
        name: &'t str,
        sub: PreNameSp<'t, T, V>,
    ) -> Option<PreNameSp<'t, T, V>> {
        unsafe {
            let psub = sub.root;
            forget(sub);
            (*psub).father = self.root;
            (*self.root).subs
                .insert(name, psub)
                .map(|root| PreNameSp { root })
        }
    }

    /// Add a `use ...::*;` into this namespace.
    pub fn use_space(&mut self, path: Path<'t>) {
        unsafe {
            let st = UseSpaceState::Waiting { path, visiting: false };
            (*self.root).use_spaces.push(st);
        }
    }

    /// Add a `use ... as ...;` into this namespace and return the old one with
    /// the same name (if any).
    pub fn use_name(
        &mut self,
        path: ValPath<'t>,
    ) -> Option<ValPath<'t>> {
        use self::ResolveState::*;
        unsafe {
            let name = path.1;
            let st = UseNameState {
                as_sub: Waiting { path: path.0.clone(), visiting: false },
                as_val: Waiting { path, visiting: false },
             };
            (*self.root).use_names.insert(name, st)
                .map(|st| match st.as_val {
                    Waiting { path, .. } => path,
                    _ => unreachable!(), // `PreNameSp` must hold `Waiting`
                })
        }
    }

    /// Consume the namespace builder, resolve all name queries and return a
    /// frozen namespace structure.
    pub fn resolve(self) -> (NameSp<'t, T, V>, Vec<ResolveError<'t>>) {
        unsafe {
            let root = self.root;
            forget(self);
            let errs = (NameSpMutPtr { root, cur: root }).resolve_tree();
            (NameSp(Box::from_raw(root)), errs)
        }
    }
}

impl<'t, T, V> Drop for PreNameSp<'t, T, V> {
    fn drop(&mut self) {
        unsafe { drop(NameSp(Box::from_raw(self.root))); }
    }
}

impl<'t, T, V> NameSp<'t, T, V> {
    pub fn root<'a>(&'a self) -> NameSpPtr<'a, 't, T, V> {
        NameSpPtr { root: &self.0, cur: &self.0 }
    }
}

impl<'a, 't, T, V> NameSpPtr<'a, 't, T, V> {
    /// Get the custom information `T` of this namespace.
    pub fn info(&self) -> &'a T {
        &self.cur.info
    }

    /// Get the value with `name` in this namespace.
    pub fn get_value(&self, name: &'t str) -> Option<&'a V> {
        self.cur.values.get(name)
    }

    /// Get an iterator over all values in this namespace.
    pub fn values(&self) -> HashMapIter<'a, &'t str, V> {
        self.cur.values.iter()
    }

    /// Get the ty(sub) with `name` in this namespace.
    pub fn get_sub(&self, name: &'t str) -> Option<NameSpPtr<'a, 't, T, V>> {
        self.cur.subs.get(name)
            .map(|p| unsafe {
                let cur = p.as_ref().unwrap(); // not null
                NameSpPtr { root: self.root, cur }
            })
    }

    pub fn subs(&self) -> SubIter<'a, 't, T, V> {
        SubIter { root: self.root, iter: self.cur.subs.iter() }
    }

    /// Get the father namespace (if any).
    pub fn get_father(&self) -> Option<NameSpPtr<'a, 't, T, V>> {
        unsafe {
            self.cur.father.as_ref()
                .map(|cur| NameSpPtr { root: self.root, cur })
        }
    }

    pub fn walk(&self, path: &Path<'t>) -> NameSpPtr<'a, 't, T, V> {
        unimplemented!()
    }
}

impl<'t, T, V> Drop for NameSp<'t, T, V> {
    fn drop(&mut self) {
        for &p in self.0.subs.values() {
            unsafe { drop(Box::from_raw(p)) }
        }
    }
}
