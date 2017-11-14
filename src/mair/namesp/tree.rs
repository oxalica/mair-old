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

type SubResolveState<'t, T, V> = ResolveState<Path<'t>, *mut Node<'t, T, V>>;
type ValResolveState<'t, V> = ResolveState<ValPath<'t>, *mut V>;

#[derive(Debug)]
struct UseNameState<'t, T, V> {
    as_sub: SubResolveState<'t, T, V>,
    as_val: ValResolveState<'t, V>,
}

#[derive(Debug)]
pub enum ResolveError<'t> {
    Cycle,
    NotFound      (&'t str),
    TooManySupers { nth: usize },
    /// Current name resolving is skipped due to a previous error.
    Skip          { name: &'t str, prev: Option<Box<ResolveError<'t>>> },
    /// The error is already emitted before.
    Emitted,
}
type ResolveRet<'t, T> = Result<T, ResolveError<'t>>;

#[derive(Debug)]
struct Node<'t, T, V> {
    /// The pointer to the father node.
    father:      *mut Node<'t, T, V>,
    /// Sub namespaces. May be `mod`, `struct` or a block.
    subs:        HashMap<&'t str, *mut Node<'t, T, V>>,
    space_lock:  bool,
    /// Namespaces imported by `use ...::*`. When the namespace is frozen
    /// (`NameSp`), it must all hold `Resolved`.
    use_spaces:  Vec<SubResolveState<'t, T, V>>,
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
    ) -> ResolveRet<'t, Self> {
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
            c = c.resolve_sub(name)
                .map_err(|e| {
                    ResolveError::Skip { name, prev: Some(Box::new(e)) }
                })?;
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
            for st in &mut node.use_names.values_mut() {
                f(self.resolve_use_name_as_sub(st).err());
                f(self.resolve_use_name_as_val(st).err());
            }
            for st in &mut node.use_spaces {
                f(self.resolve_use_space(st).err());
            }
            for &sub in node.subs.values() {
                self.move_to(sub).resolve_tree().into_iter();
            }
        }
        errs
    }

    unsafe fn resolve_sub(&mut self, name: &'t str) -> ResolveRet<'t, Self> {
        match (*self.cur).subs.get(name) {
            Some(&psub) => Ok(self.move_to(psub)),
            None => match (*self.cur).use_names.get_mut(name) {
                Some(st) => self.resolve_use_name_as_sub(st),
                None => {
                    self.with_spaces(|mut sp| {
                        match sp.resolve_sub(name) {
                            Err(ResolveError::NotFound(_)) => Ok(None),
                            ret => ret.map(Some),
                        }
                    })?.ok_or_else(|| ResolveError::NotFound(name))
                },
            },
        }
    }

    unsafe fn resolve_val(&mut self, name: &'t str) -> ResolveRet<'t, *mut V> {
        match (*self.cur).values.get_mut(name) {
            Some(v) => Ok(v),
            None => match (*self.cur).use_names.get_mut(name) {
                Some(st) => self.resolve_use_name_as_val(st),
                None => {
                    self.with_spaces(|mut sp| {
                        match sp.resolve_val(name) {
                            Err(ResolveError::NotFound(_)) => Ok(None),
                            ret => ret.map(Some),
                        }
                    })?.ok_or_else(|| ResolveError::NotFound(name))
                },
            },
        }
    }

    unsafe fn resolve_use_name_as_sub(
        &mut self,
        st: *mut UseNameState<'t, T, V>, // may not have unique access (cycle)
    ) -> ResolveRet<'t, Self> {
        use self::ResolveState::*;
        let (path, visiting): (_, *mut bool) = match (*st).as_sub {
            Done(None) =>
                return Err(Emitted),
            Done(Some(pos)) =>
                return Ok(self.move_to(pos)),
            Waiting{ ref path, ref mut visiting } =>
                (path, visiting),
        };
        if *visiting {
            (*st).as_sub = Done(None);
            Err(ResolveError::Cycle)
        } else {
            *visiting = true;
            let ret = self.walk_resolve(path);
            *visiting = false;
            (*st).as_sub = Done(ret.as_ref().ok().map(|tag| tag.cur));
            ret
        }
    }

    unsafe fn resolve_use_name_as_val(
        &mut self,
        st: *mut UseNameState<'t, T, V>, // may not have unique access (cycle)
    ) -> ResolveRet<'t, *mut V> {
        use self::ResolveState::*;
        let (path, visiting): (_, *mut bool) = match (*st).as_val {
            Done(None) =>
                return Err(Emitted),
            Done(Some(pos)) =>
                return Ok(pos),
            Waiting{ ref path, ref mut visiting } =>
                (path, visiting),
        };
        if *visiting {
            (*st).as_val = Done(None);
            Err(ResolveError::Cycle)
        } else {
            *visiting = true;
            let ret = self.walk_resolve(&path.0)
                .and_then(|mut ori_ns| ori_ns.resolve_val(path.1));
            *visiting = false;
            (*st).as_val = Done(ret.as_ref().ok().cloned());
            ret
        }
    }

    unsafe fn resolve_use_space(
        &mut self,
        st: *mut SubResolveState<'t, T, V>,
    ) -> ResolveRet<'t, Option<Self>> {
        use self::ResolveState::*;
        let (path, visiting): (_, *mut bool) = match *st {
            Done(None) =>
                return Ok(None),
            Done(Some(pos)) =>
                return Ok(Some(self.move_to(pos))),
            Waiting{ ref path, ref mut visiting } =>
                (path, visiting),
        };
        if *visiting { // skip namespaces visiting instead of `Err`
            Ok(None)
        } else {
            *visiting = true;
            let ret = self.walk_resolve(path);
            *visiting = false;
            *st = Done(ret.as_ref().ok().map(|tag| tag.cur));
            ret.map(Some)
        }
    }

    unsafe fn with_spaces<R, F>(
        &mut self,
        mut f: F,
    ) -> ResolveRet<'t, Option<R>>
    where F: FnMut(Self) -> ResolveRet<'t, Option<R>> {
        (*self.cur).space_lock = true;
        for st in &mut (*self.cur).use_spaces {
            if let Some(sp) = self.resolve_use_space(st)? {
                if !(*sp.cur).space_lock { // `a` use `b::*`, `b` use `a::*`
                                           // then skip
                    if let Some(ret) = f(sp)? {
                        return Ok(Some(ret));
                    }
                }
            }
        }
        Ok(None)
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
            space_lock:  false,
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
            let st = ResolveState::Waiting { path, visiting: false };
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

    /// Consume the namespace builder, resolve all name required by `use`s and
    /// return a frozen namespace structure.
    pub fn resolve_uses(self) -> (NameSp<'t, T, V>, Vec<ResolveError<'t>>) {
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
    pub fn get_sub(&self, name: &'t str) -> Option<Self> {
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
    pub fn get_father(&self) -> Option<Self> {
        unsafe {
            self.cur.father.as_ref()
                .map(|cur| NameSpPtr { root: self.root, cur })
        }
    }

    unsafe fn to_mut_ptr(&self) -> NameSpMutPtr<'t, T, V> {
        NameSpMutPtr {
            root: self.root as *const _ as *mut _,
            cur:  self.cur as *const _ as *mut _,
        }
    }

    /// Resolve a path to a sub-namespace (or ty).
    pub fn resolve_sub(&self, path: &Path<'t>) -> ResolveRet<'t, Self> {
        unsafe {
            self.to_mut_ptr()
                .walk_resolve(path)
                .map(|NameSpMutPtr { root, cur }| {
                    NameSpPtr { root: &*root, cur: &*cur }
                })
        }
    }

    /// Resolve a path to a sub-namespace (or ty).
    pub fn resolve_val(&self, path: &ValPath<'t>) -> ResolveRet<'t, &'a V> {
        unsafe {
            self.to_mut_ptr()
                .walk_resolve(&path.0)
                .and_then(|mut sp| sp.resolve_val(path.1))
                .map(|pv| &*pv)
        }
    }
}

impl<'t, T, V> Drop for NameSp<'t, T, V> {
    fn drop(&mut self) {
        for &p in self.0.subs.values() {
            unsafe { drop(Box::from_raw(p)) }
        }
    }
}
