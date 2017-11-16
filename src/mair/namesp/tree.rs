/// The namespace tree structure storing named ty (sub-namespace) and value
/// objects, providing name resolution.

use std::collections::hash_map::{HashMap, Iter as HashMapIter};
use std::cell::{Cell, RefCell};
use super::{Path, ValPath};
use self::ResolveError::*;

/// The mutable namespace tree with unresolved `use`s.
#[derive(Debug)]
pub struct PreNameSp<'a, 't: 'a, T: 'a, V: 'a> {
    root: Box<Node<'a, 't, T, V>>,
}

/// The immutable namespace tree with all `use`s resolved.
/// It's just a container to store the structure (to extend lifetime).
/// Methods should be invoked through `NameSpPtr` instead of `NameSp`.
#[derive(Debug, Default)]
pub struct NameSp<'a, 't: 'a, T: 'a, V: 'a>(Option<Box<Node<'a, 't, T, V>>>);

/// The pointer to a namespace on an immutable namespace tree.
#[derive(Debug)]
pub struct NameSpPtr<'a, 't: 'a, T: 'a, V: 'a> {
    root:   &'a Node<'a, 't, T, V>,
    cur:    &'a Node<'a, 't, T, V>,
}

#[derive(Debug)]
enum ResolveState<P, T> {
    Waiting { path: P, visiting: bool },
    Resolved(T),
    Unresolved,
}

type SubResolveState<'a, 't: 'a, T: 'a, V: 'a> =
    ResolveState<Path<'t>, &'a Node<'a, 't, T, V>>;
type ValResolveState<'a, 't: 'a, V: 'a> =
    ResolveState<ValPath<'t>, &'a V>;

#[derive(Debug)]
struct UseNameState<'a, 't: 'a, T: 'a, V: 'a> {
    as_sub: RefCell<SubResolveState<'a, 't, T, V>>,
    as_val: RefCell<ValResolveState<'a, 't, V>>,
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
struct Node<'a, 't: 'a, T: 'a, V: 'a> {
    father:     Option<&'a Node<'a, 't, T, V>>,
    /// Sub namespaces owned by this namespace.
    subs:       HashMap<&'t str, Box<Node<'a, 't, T, V>>>,
    /// The flag set when finding names through `use_space`.
    space_lock: Cell<bool>,
    /// Namespaces imported by `use ...::*`. When the namespace is frozen
    /// (`NameSp`), it must not hold `Waiting`.
    use_spaces: Vec<RefCell<SubResolveState<'a, 't, T, V>>>,
    /// Names imported by `use`.  When the namespace is frozen (`NameSp`), it
    /// must not hold `Waiting`.
    use_names:  HashMap<&'t str, UseNameState<'a, 't, T, V>>,
    /// Information of this namespace.
    info:       T,
    /// Values owned by this namespace.
    values:     HashMap<&'t str, V>,
}

#[derive(Debug)]
pub struct SubIter<'a, 't: 'a, T: 'a, V: 'a> {
    root: &'a Node<'a, 't, T, V>,
    iter: HashMapIter<'a, &'t str, Box<Node<'a, 't, T, V>>>,
}
#[derive(Debug)]
pub struct ValIter<'a, 't: 'a, V: 'a> {
    iter: HashMapIter<'a, &'t str, V>,
}

impl<'a, 't: 'a, T: 'a, V: 'a> Iterator for SubIter<'a, 't, T, V> {
    type Item = (&'t str, NameSpPtr<'a, 't, T, V>);
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
            .map(|(&name, cur)| (name, NameSpPtr { root: self.root, cur }))
    }
}

impl<'a, 't: 'a, V: 'a> Iterator for ValIter<'a, 't, V> {
    type Item = (&'t str, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
            .map(|(&name, v)| (name, v))
    }
}

impl<'a, 't: 'a, T: 'a, V: 'a> Clone for NameSpPtr<'a, 't, T, V> {
    fn clone(&self) -> Self {
        NameSpPtr{ root: self.root, cur: self.cur }
    }
}

impl<'a, 't: 'a, T: 'a, V: 'a> NameSp<'a, 't, T, V> {
    pub fn new() -> Self {
        NameSp(None)
    }
}

impl<'a, 't: 'a, T: 'a, V: 'a> NameSpPtr<'a, 't, T, V> {
    fn move_to(&self, target: &'a Node<'a, 't, T, V>) -> Self {
        NameSpPtr { root: self.root, cur: target }
    }

    /// Get a pointer to the root namespace.
    pub fn get_root(&self) -> Self {
        self.move_to(self.root)
    }

    /// Get a pointer to the namespace which owned this namespace (if any).
    pub fn get_father(&self) -> Option<Self> {
        self.cur.father
            .as_ref()
            .map(|r| self.move_to(r))
    }

    /// Get the custom information `T` of this namespace.
    pub fn get_info(&self) -> &'a T {
        &self.cur.info
    }

    /// Get an iterator over all sub-namespaces owned by this namespace.
    pub fn subs(&self) -> SubIter<'a, 't, T, V> {
        SubIter { root: self.root, iter: self.cur.subs.iter() }
    }

    /// Get an iterator over all values owned by this namespace.
    pub fn values(&self) -> ValIter<'a, 't, V> {
        ValIter { iter: self.cur.values.iter() }
    }

    /// DFS to resolve all use names in the sub-tree of this namespace.
    fn resolve_all(&self) -> Vec<ResolveError<'t>> {
        let mut errs = vec![];
        for st in self.cur.use_names.values() {
            errs.extend(self.resolve_sub_path(&st.as_sub).err());
            errs.extend(self.resolve_val_path(&st.as_val).err());
        }
        for st in &self.cur.use_spaces {
            errs.extend(self.resolve_sub_path(st).err());
        }
        for sub in self.cur.subs.values() {
            errs.extend(self.move_to(sub).resolve_all());
        }
        errs
    }

    /// Resolve a path from this namespace. (Recursive)
    fn walk_resolve(&self, path: &Path<'t>) -> ResolveRet<'t, Self> {
        let mut c: Self = self.clone();
        let comps = match *path {
            Path::Absolute{ ref comps } => {
                c = c.get_root();
                comps
            },
            Path::Relative{ supers, ref comps } => {
                for nth in 0..supers {
                    c = c.get_father() // None in the root namespace
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

    /// Resolve a sub-namespace name in this namespace. (Recursive)
    fn resolve_sub(&self, name: &'t str) -> ResolveRet<'t, Self> {
        let node = self.cur;
        match node.subs.get(name) {
            Some(sub) => Ok(self.move_to(sub)),
            None => match node.use_names.get(name) {
                Some(st) => self.resolve_sub_path(&st.as_sub),
                None => {
                    self.with_spaces(|sp| {
                        match sp.resolve_sub(name) {
                            Err(ResolveError::NotFound(_)) => Ok(None),
                            ret => ret.map(Some),
                        }
                    })?.ok_or_else(|| ResolveError::NotFound(name))
                },
            },
        }
    }

    /// Resolve a value name in this namespace. (Recursive)
    fn resolve_val(&self, name: &'t str) -> ResolveRet<'t, &'a V> {
        let node = self.cur;
        match node.values.get(name) {
            Some(v) => Ok(v),
            None => match node.use_names.get(name) {
                Some(st) => self.resolve_val_path(&st.as_val),
                None => {
                    self.with_spaces(|sp| {
                        match sp.resolve_val(name) {
                            Err(ResolveError::NotFound(_)) => Ok(None),
                            ret => ret.map(Some),
                        }
                    })?.ok_or_else(|| ResolveError::NotFound(name))
                },
            },
        }
    }

    /// Resolve a `use`-sub-namespace and store the result. (Recursive)
    fn resolve_sub_path(
        &self,
        st: &RefCell<SubResolveState<'a, 't, T, V>>,
    ) -> ResolveRet<'t, Self> {
        use self::ResolveState::*;
        match *st.borrow_mut() {
            Resolved(r) => return Ok(self.move_to(r)),
            Unresolved => return Err(ResolveError::Emitted), // ^- alive in 'a
            Waiting{ visiting: true, .. } => return Err(ResolveError::Cycle),
            Waiting{ ref mut visiting, .. } => *visiting = true,
        }
        let _elder = st.borrow(); // make it live longer than `path` below
        let path = match *_elder {
            Waiting{ ref path, .. } => path,
            _ => unreachable!(), // checked before
        };
        let ret = self.walk_resolve(path);
        *st.borrow_mut() = match ret {
            Ok(ref sub) => Resolved(sub.cur),
            Err(_) => Unresolved,
        };
        ret
    }

    /// Resolve a `use`-value and store the result. (Recursive)
    fn resolve_val_path(
        &self,
        st: &RefCell<ValResolveState<'a, 't, V>>,
    ) -> ResolveRet<'t, &'a V> {
        use self::ResolveState::*;
        match *st.borrow_mut() {
            Resolved(r) => return Ok(r),
            Unresolved => return Err(ResolveError::Emitted),
            Waiting{ visiting: true, .. } => return Err(ResolveError::Cycle),
            Waiting{ ref mut visiting, .. } => *visiting = true,
        }
        let _elder = st.borrow(); // make it live longer than `path` below
        let (path, name) = match *_elder {
            Waiting{ ref path, .. } => (&path.0, path.1),
            _ => unreachable!(), // checked before
        };
        let ret = self.walk_resolve(path)
            .and_then(|sub| sub.resolve_val(name));
        *st.borrow_mut() = match ret {
            Ok(r) => Resolved(r),
            Err(_) => Unresolved,
        };
        ret
    }

    /// Do something with namespaces imported by `use`-space. (Recursive)
    fn with_spaces<R, F>(&self, mut f: F) -> ResolveRet<'t, Option<R>>
    where F: FnMut(Self) -> ResolveRet<'t, Option<R>> {
        let node = self.cur;
        node.space_lock.set(true);
        for st in &node.use_spaces {
            let sub = self.resolve_sub_path(st)?;
            // If `a` use `b::*` and `b` use `a::*`, skip
            if !sub.cur.space_lock.get() {
                if let Some(ret) = f(sub)? {
                    return Ok(Some(ret));
                }
            }
        }
        Ok(None)
    }

    /// Resolve a path to a namespace. It can only be invoked after all `use`s
    /// are resolved. So if error occurs, it must be `NotFound`.
    pub fn query_sub(&self, path: &Path<'t>) -> ResolveRet<'t, Self> {
        self.walk_resolve(path)
    }

    /// Resolve a path to a value. It can only be invoked after all `use`s are
    /// resolved.
    pub fn query_val(&self, path: &ValPath<'t>) -> ResolveRet<'t, &'a V> {
        self.walk_resolve(&path.0)
            .and_then(|sub| sub.resolve_val(path.1))
    }
}

impl<'a, 't: 'a, T: 'a, V: 'a> PreNameSp<'a, 't, T, V> {
    /// Create an empty namespace with custom infomation `T`.
    pub fn new(info: T) -> Self {
        PreNameSp { root: Box::new(Node {
            father:      None,
            subs:        HashMap::new(),
            space_lock:  Cell::new(false),
            use_spaces:  vec![],
            use_names:   HashMap::new(),
            info,
            values:      HashMap::new(),
        }) }
    }

    /// Add a sub-namespace and return the old one with the same name (if any).
    pub fn add_sub(
        &mut self,
        name: &'t str,
        sub: PreNameSp<'a, 't, T, V>,
    ) -> Option<PreNameSp<'a,'t, T, V>> {
        self.root.subs
            .insert(name, sub.root)
            .map(|root| PreNameSp { root })
    }

    /// Add a `use ...::*;` into this namespace.
    pub fn use_space(&mut self, path: Path<'t>) {
        self.root.use_spaces
            .push(RefCell::new(
                ResolveState::Waiting { path, visiting: false }
            ));
    }

    /// Add a `use ... as ...;` into this namespace and return the old one with
    /// the same name (if any).
    pub fn use_name(
        &mut self,
        path: ValPath<'t>,
    ) -> Option<ValPath<'t>> {
        use self::ResolveState::*;
        let name = path.1;
        let st = UseNameState {
            as_sub: RefCell::new(Waiting {
                path: path.0.clone(),
                visiting: false,
            }),
            as_val: RefCell::new(Waiting {
                path,
                visiting: false,
            }),
        };
        self.root.use_names
            .insert(name, st)
            .map(|st| match st.as_val.into_inner() {
                Waiting { path, .. } => path,
                _ => unreachable!(), // no resolutions in `PreNameSp`
            })
    }

    /// Consume the `PreNameSp`, resolve all name required by `use`s and return
    /// a frozen namespace structure.
    pub fn resolve_uses(
        self,
        container: &'a mut NameSp<'a, 't, T, V>,
    ) -> (NameSpPtr<'a, 't, T, V>, Vec<ResolveError<'t>>) {
        container.0 = Some(self.root);
        let r = container.0.as_ref().unwrap(); // get reference living in 'a
        let p = NameSpPtr { root: r, cur: r };
        let errs = p.resolve_all();
        (p, errs)
    }
}
