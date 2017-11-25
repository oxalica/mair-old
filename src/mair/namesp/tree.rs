//! The namespace tree structure storing named ty (sub-namespace) and value
//! objects, providing name resolution.

// FIXME: macro catch_into! requires feature(catch_expr)
#![cfg_attr(feature="clippy", allow(redundant_closure_call))]

use std::collections::hash_map::{HashMap, Iter as HashMapIter};
use std::cell::{Cell, RefCell};
use super::{Path, ValPath};
use self::ResolveErrorKind::*;

/// The mutable namespace tree with unresolved `use`s.
#[derive(Debug)]
pub struct PreNameSp<'a, 't: 'a, T: 'a, V: 'a> {
    root: Box<Node<'a, 't, T, V>>,
}

/// The immutable namespace tree with all `use`s resolved.
/// It's just a container to store the structure (to extend lifetime).
/// Methods should be invoked through `NameSpPtr` instead of `NameSp`.
#[derive(Debug)]
pub struct NameSp<'a, 't: 'a, T: 'a, V: 'a>(Option<Box<Node<'a, 't, T, V>>>);

/// The pointer to a namespace on an immutable namespace tree.
#[derive(Debug)]
pub struct NameSpPtr<'a, 't: 'a, T: 'a, V: 'a> {
    root:   &'a Node<'a, 't, T, V>,
    cur:    &'a Node<'a, 't, T, V>,
}

#[derive(Debug)]
enum ResolveState<P, T> {
    Waiting   (P),
    Resolved  (T),
    Unresolved,
}

impl<P, T: Clone> ResolveState<P, T> {
    fn do_resolve<F>(&mut self, f: F) -> Option<T>
    where F: FnOnce(P) -> Option<T> {
        use self::ResolveState::*;
        use std::mem::replace;
        let (ret, new_st) = match replace(self, Unresolved) {
            Resolved(t) => (Some(t.clone()), Resolved(t)),
            Unresolved => (None, Unresolved),
            Waiting(p) => match f(p) {
                Some(t) => (Some(t.clone()), Resolved(t)),
                None => (None, Unresolved),
            },
        };
        *self = new_st;
        ret
    }
}

type SubResolveState<'a, 't: 'a, T: 'a, V: 'a> =
    ResolveState<Path<'t>, NameSpPtr<'a, 't, T, V>>;
type ValResolveState<'a, 't: 'a, V: 'a> =
    ResolveState<ValPath<'t>, &'a V>;

#[derive(Debug)]
struct UseNameState<'a, 't: 'a, T: 'a, V: 'a> {
    as_sub: RefCell<SubResolveState<'a, 't, T, V>>,
    as_val: RefCell<ValResolveState<'a, 't, V>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct ResolveError<'t> {
    pos:  &'t str,
    kind: ResolveErrorKind<'t>,
}
type Errs<'t> = Vec<ResolveError<'t>>;

macro_rules! catch_into {
    ($v:expr; $($t:tt)*) => {
        (|| { $($t)* })()
            .map(Some)
            .unwrap_or_else(|e| {
                $v.push(e);
                None
            })
    };
}

#[derive(Debug, PartialEq, Eq)]
pub enum ResolveErrorKind<'t> {
    Cycle,
    NotFound,
    TooManySupers,
    /// Current name resolving is skipped due to a previous error.
    Skip,
    Ambiguous     { sp_names: Vec<&'t str> },
}
type ResolveRet<'t, T> = Result<T, ResolveError<'t>>;

#[derive(Debug)]
struct Node<'a, 't: 'a, T: 'a, V: 'a> {
    father:     Cell<Option<&'a Node<'a, 't, T, V>>>,
    /// Sub namespaces owned by this namespace.
    subs:       HashMap<&'t str, Box<Node<'a, 't, T, V>>>,
    /// The flag set when finding names through `use_space`.
    space_lock: Cell<bool>,
    /// Namespaces imported by `use ...::*`. When the namespace is frozen
    /// (`NameSp`), it must not hold `Waiting`.
    use_spaces: Vec<(&'t str, RefCell<SubResolveState<'a, 't, T, V>>)>,
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

impl<'a, 't: 'a, T: 'a, V: 'a> PartialEq for NameSpPtr<'a, 't, T, V> {
    fn eq(&self, rhs: &Self) -> bool {
        self.cur as *const _ == rhs.cur
    }
}

impl<'a, 't: 'a, T: 'a, V: 'a> Eq for NameSpPtr<'a, 't, T, V> {}

impl<'a, 't: 'a, T: 'a, V: 'a> NameSp<'a, 't, T, V> {
    pub fn new() -> Self {
        NameSp(None)
    }
}

// FIXME: Cannot derive `Default` due to rust-lang/rust#26925
impl<'a, 't: 'a, T: 'a, V: 'a> Default for NameSp<'a, 't, T, V> {
    fn default() -> Self {
        NameSp::new()
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
            .get()
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

    /// DFS to set all `father` fields of the namespace tree.
    fn set_fathers(&self) {
        for (_, sub) in self.subs() {
            sub.cur.father.set(Some(self.cur));
            sub.set_fathers();
        }
    }

    /// DFS to resolve all use names in the sub-tree of this namespace.
    fn resolve_all(&self, errs: &mut Errs<'t>) {
        for st in self.cur.use_names.values() {
            self.resolve_sub_path(&mut st.as_sub.borrow_mut(), errs);
            self.resolve_val_path(&mut st.as_val.borrow_mut(), errs);
        }
        for &(_, ref st) in &self.cur.use_spaces {
            self.resolve_sub_path(&mut st.borrow_mut(), errs);
        }
        for sub in self.cur.subs.values() {
            self.move_to(sub).resolve_all(errs);
        }
    }

    /// Resolve a path from this namespace. (Recursive)
    fn walk_resolve(
        &self,
        path: &Path<'t>,
        errs: &mut Errs<'t>,
    ) -> Option<Self> {
        catch_into! { errs;
            let mut c: Self = self.clone();
            let comps = match *path {
                Path::Absolute{ ref comps } => {
                    c = c.get_root();
                    comps
                },
                Path::Relative{ ref supers, ref comps } => {
                    for pos in supers {
                        c = c.get_father() // None in the root namespace
                            .ok_or(ResolveError { pos, kind: TooManySupers })?;
                    }
                    comps
                },
            };
            for &name in comps.iter() {
                c = c.resolve_sub(name, errs)
                    .ok_or(ResolveError { pos: name, kind: Skip })?;
            }
            Ok(c)
        }
    }

    /// Resolve a sub-namespace name in this namespace. (Recursive)
    /// Return None if `NotFound`, without pushing it to `errs`.
    fn resolve_sub(&self, name: &'t str, errs: &mut Errs<'t>) -> Option<Self> {
        None.or_else(|| {
                self.cur.subs.get(name)
                    .map(|sub| self.move_to(sub))
            })
            .or_else(|| {
                self.cur.use_names.get(name)
                    .and_then(|st| catch_into! { errs;
                        st.as_sub.try_borrow_mut()
                            .map_err(|_| ResolveError { pos:  name
                                                      , kind: Cycle })
                    })
                    .and_then(|mut st| self.resolve_sub_path(&mut st, errs))
            })
            .or_else(|| {
                self.resolve_in_spaces(name, errs, |sp: Self, errs| {
                    sp.resolve_sub(name, errs)
                })
            })
    }

    /// Resolve a value name in this namespace. (Recursive)
    /// Return None if `NotFound`, without pushing it to `errs`.
    fn resolve_val(
        &self,
        name: &'t str,
        errs: &mut Errs<'t>,
    ) -> Option<&'a V> {
        None.or_else(|| {
                self.cur.subs.get(name)
                    .map(|sub| self.move_to(sub))
                    .and_then(|sub| sub.resolve_val(name, errs))
            })
            .or_else(|| {
                self.cur.use_names.get(name)
                    .and_then(|st| catch_into! { errs;
                        st.as_sub.try_borrow_mut()
                            .map_err(|_| ResolveError { pos:  name
                                                      , kind: Cycle })
                    })
                    .and_then(|mut st| self.resolve_sub_path(&mut st, errs))
                    .and_then(|sub| sub.resolve_val(name, errs))
            })
            .or_else(|| {
                self.resolve_in_spaces(name, errs, |sp: Self, errs| {
                    sp.resolve_sub(name, errs)
                        .and_then(|sub| sub.resolve_val(name, errs))
                })
            })
    }

    /// Resolve a `use`-sub-namespace and store the result. (Recursive)
    fn resolve_sub_path(
        &self,
        st:   &mut SubResolveState<'a, 't, T, V>,
        errs: &mut Errs<'t>,
    ) -> Option<Self> {
        st.do_resolve(|path| self.walk_resolve(&path, errs))
    }

    /// Resolve a `use`-value and store the result. (Recursive)
    fn resolve_val_path(
        &self,
        st:   &mut ValResolveState<'a, 't, V>,
        errs: &mut Errs<'t>,
    ) -> Option<&'a V> {
        st.do_resolve(|(path, name)| {
            self.walk_resolve(&path, errs)
                .and_then(|sub| sub.resolve_val(name, errs))
        })
    }

    /// Resolve a name in namespaces imported by `use`-space. (Recursive)
    fn resolve_in_spaces<R, F>(
        &self,
        name:  &'t str,
        errs:  &mut Errs<'t>,
        mut f: F,
    ) -> Option<R>
    where F: FnMut(Self, &mut Errs<'t>) -> Option<R> {
        self.cur.space_lock.set(true);
        let (sp_names, mut founds): (Vec<_>, Vec<_>) =
            self.cur.use_spaces.iter()
                .filter_map(|&(sp_name, ref st)| {
                    st.try_borrow_mut().ok()
                        .and_then(|mut st| self.resolve_sub_path(&mut st, errs))
                        .and_then(|sub| {
                            if !sub.cur.space_lock.get() {
                                f(sub, errs)
                                    .map(|r| (sp_name, r))
                            } else {
                                None
                            }
                        })
                })
                .unzip();
        self.cur.space_lock.set(false);
        match founds.len() {
            0 => None,
            1 => Some(founds.pop().unwrap()),
            _ => {
                errs.push(ResolveError {
                    pos: name,
                    kind: Ambiguous { sp_names },
                });
                None
            },
        }
    }

    /// Resolve a path to a namespace. It can only be invoked after all `use`s
    /// are resolved. So if error occurs, it must be `NotFound`.
    pub fn query_sub(&self, path: &Path<'t>) -> ResolveRet<'t, Self> {
        unimplemented!()
    }

    /// Resolve a path to a value. It can only be invoked after all `use`s are
    /// resolved.
    pub fn query_val(&self, path: &ValPath<'t>) -> ResolveRet<'t, &'a V> {
        unimplemented!()
    }
}

impl<'a, 't: 'a, T: 'a, V: 'a> PreNameSp<'a, 't, T, V> {
    /// Create an empty namespace with custom infomation `T`.
    pub fn new(info: T) -> Self {
        PreNameSp { root: Box::new(Node {
            father:      Cell::new(None),
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

    /// Add a value and return the old one with the same name (if any).
    pub fn add_value(&mut self, name: &'t str, value: V) -> Option<V> {
        self.root.values
            .insert(name, value)
    }

    /// Add a `use ...::*;` into this namespace. `name` is the identifier used
    /// in error reporting.
    pub fn use_space(&mut self, name: &'t str, path: Path<'t>) {
        self.root.use_spaces
            .push((name, RefCell::new(ResolveState::Waiting(path))));
    }

    /// Add a `use ... as ...;` into this namespace and return the old one with
    /// the same name (if any).
    pub fn use_name(
        &mut self,
        name: &'t str,
        path: ValPath<'t>,
    ) -> Option<ValPath<'t>> {
        use self::ResolveState::*;
        let sub_path = path.0.clone().push(path.1);
        let st = UseNameState {
            as_sub: RefCell::new(Waiting(sub_path)),
            as_val: RefCell::new(Waiting(path)),
        };
        self.root.use_names
            .insert(name, st)
            .map(|st| match st.as_val.into_inner() {
                Waiting(path) => path,
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
        p.set_fathers();
        let mut errs = vec![];
        p.resolve_all(&mut errs);
        (p, errs)
    }
}
