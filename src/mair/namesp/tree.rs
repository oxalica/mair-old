//! The namespace tree structure storing named ty (sub-namespace) and value
//! objects, providing name resolution.

// FIXME: macro catch_into! requires feature(catch_expr)
#![cfg_attr(feature="clippy", allow(redundant_closure_call))]

use std::collections::hash_map::{HashMap, Iter as HashMapIter};
use std::cell::{Cell, RefCell};
use std::convert::From;
use super::{Path, ValPath};
use self::HardError::*;
use self::Maybe::*;

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
enum UseST<'a, 't: 'a, T: 'a, V: 'a> {
    Waiting      { path: Path<'t>, name: &'t str },
    PathErr,
    PathNotFound { name: &'t str },
    PathResolved { subsp: NameSpPtr<'a, 't, T, V>
                 , name:  &'t str
                 , sub:   RefCell<Option<Option<NameSpPtr<'a, 't, T, V>>>>
                 , val:   RefCell<Option<Option<&'a V>>> },
}
type UseSTCell<'a, 't: 'a, T: 'a, V: 'a> =
    RefCell<UseST<'a, 't, T, V>>;

#[derive(Debug)]
enum UseSpaceST<'a, 't: 'a, T: 'a, V: 'a> {
    Waiting      (Path<'t>),
    PathErr,
    PathNotFound { name: &'t str },
    Resolved     (NameSpPtr<'a, 't, T, V>),
}
type UseSpaceList<'a, 't: 'a, T: 'a, V: 'a> =
    Vec<(&'t str, UseSpaceST<'a, 't, T, V>)>;

impl<'a, 't: 'a, T: 'a, V: 'a> UseST<'a, 't, T, V> {
    fn as_sub(&self, alias: &'t str)
            -> ResolveRet<'t, Option<NameSpPtr<'a, 't, T, V>>> {
        use self::UseST::*;

        match *self {
            PathResolved{ ref sub, ref subsp, name, .. } => {
                match sub.try_borrow_mut() {
                    Err(_) =>
                        Err(Cycle { begin: Some(alias), steps: vec![] }),
                    Ok(mut st) => {
                        if let Some(ref sub) = *st {
                            return Ok(sub.clone());
                        }
                        let (store, ret) = match subsp.resolve_sub(name) {
                            Ok(Found(s)) => (Some(s.clone()), Ok(Some(s))),
                            Ok(NotFound(_)) => (None, Ok(None)),
                            Err(e) => (None, Err(e)),
                        };
                        *st = Some(store);
                        ret
                    },
                }
            },
            PathErr | PathNotFound{ .. } =>
                Ok(None),
            Waiting{ .. } =>
                panic!("Resolve name before resolving path"),
        }
    }

    fn as_val(&self, alias: &'t str) -> ResolveRet<'t, Option<&'a V>> {
        use self::UseST::*;

        match *self {
            PathResolved{ ref val, ref subsp, name, .. } => {
                match val.try_borrow_mut() {
                    Err(_) =>
                        Err(Cycle { begin: Some(alias), steps: vec![] }),
                    Ok(mut st) => {
                        if let Some(v) = *st {
                            return Ok(v);
                        }
                        let (store, ret) = match subsp.resolve_val(name) {
                            Ok(Found(v)) => (Some(v), Ok(Some(v))),
                            Ok(NotFound(_)) => (None, Ok(None)),
                            Err(e) => (None, Err(e)),
                        };
                        *st = Some(store);
                        ret
                    },
                }
            },
            PathErr | PathNotFound{ .. } =>
                Ok(None),
            Waiting{ .. } =>
                panic!("Resolve name before resolving path"),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ResolveError<'t> {
    NotFound      { name: &'t str },
    TooManySupers { super_pos: &'t str },
    UseNothing    { name: &'t str },
    Ambiguous     { name: &'t str, sp_names: Vec<&'t str> },
    Cycle         { steps: Vec<(&'t str, &'t str)> },
}

#[derive(Debug, PartialEq, Eq)]
enum HardError<'t> {
    TooManySupers { super_pos: &'t str },
    Ambiguous     { name:     &'t str
                  , sp_names: Vec<&'t str> },
    Cycle         { begin: Option<&'t str>
                  , steps: Vec<(&'t str, &'t str)> },
}

impl<'t> From<HardError<'t>> for ResolveError<'t> {
    fn from(err: HardError<'t>) -> Self {
        use self::ResolveError as R;

        match err {
            TooManySupers{ super_pos } =>
                R::TooManySupers { super_pos },
            Ambiguous{ name, sp_names } =>
                R::Ambiguous { name, sp_names },
            Cycle{ steps, begin: None } =>
                R::Cycle { steps },
            Cycle{ begin: Some(_), .. } =>
                panic!("Unclosed cycle"),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Maybe<'t, T> {
    NotFound(&'t str),
    Found   (T),
}

// FIXME: Use struct overloading `?`. `rust-lang/rust#42327`
type ResolveRet<'t, T> = Result<T, HardError<'t>>;
type SoftResolveRet<'t, T> = ResolveRet<'t, Maybe<'t, T>>;

trait ResolveRetExt<'t> {
    fn or_cycle(self, name: &'t str, target: &'t str) -> Self;
}

impl<'t, T> ResolveRetExt<'t> for ResolveRet<'t, T> {
    fn or_cycle(self, name: &'t str, target: &'t str) -> Self {
        fn str_eqeqeq(a: &str, b: &str) -> bool {
            a.as_ptr() == b.as_ptr() && a.len() == b.len()
        }
        match self {
            Err(Cycle { begin: Some(begin), mut steps }) => {
                steps.push((name, target));
                if str_eqeqeq(begin, name) { // close the cycle
                    Err(Cycle { begin: None, steps })
                } else {
                    Err(Cycle { begin: Some(begin), steps })
                }
            },
            c => c,
        }
    }
}

#[derive(Debug)]
struct Node<'a, 't: 'a, T: 'a, V: 'a> {
    father:     Cell<Option<&'a Node<'a, 't, T, V>>>,
    /// Sub namespaces owned by this namespace.
    subs:       HashMap<&'t str, Box<Node<'a, 't, T, V>>>,
    /// Namespaces imported by `use ...::*`.
    use_spaces: RefCell<UseSpaceList<'a, 't, T, V>>,
    /// Names imported by `use`.
    use_names:  HashMap<&'t str, (&'t str, UseSTCell<'a, 't, T, V>)>,
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

    /// DFS to resolve all queries.
    fn resolve_all(&self, errs: &mut Vec<ResolveError<'t>>) {
        use self::ResolveError as R;

        for &(name, ref stc) in self.cur.use_names.values() {
            use self::UseST::PathResolved;
            use self::ResolveError as R;

            errs.extend(self.resolve_usest_path(name, stc).err().map(R::from));
            errs.extend(stc.borrow().as_sub(name).err().map(R::from));
            errs.extend(stc.borrow().as_val(name).err().map(R::from));

            if let PathResolved { name, ref sub, ref val, .. } = *stc.borrow() {
                if let (&Some(None), &Some(None)) =
                        (&*sub.borrow(), &*val.borrow()) {
                    errs.push(R::UseNothing { name });
                }
            }
        }
        let ret = self.resolve_in_spaces::<(), _>(
            "",
            &mut self.cur.use_spaces.borrow_mut(),
            |_, _| Ok(NotFound("")),
        );
        match ret {
            Ok(NotFound("")) => (),
            _ => unreachable!(),
        }
        for &(_, ref st) in &*self.cur.use_spaces.borrow() {
            if let UseSpaceST::PathNotFound { name } = *st {
                errs.push(R::NotFound { name })
            }
        }
        for sub in self.cur.subs.values() {
            self.move_to(sub).resolve_all(errs);
        }
    }

    /// Resolve a path from this namespace.
    fn walk_resolve(&self, path: &Path<'t>) -> SoftResolveRet<'t, Self> {
        let mut c = self.clone();
        let comps = match *path {
            Path::Absolute{ ref comps } => {
                c = c.get_root();
                comps
            },
            Path::Relative{ ref supers, ref comps } => {
                for super_pos in supers {
                    c = c.get_father() // None in the root namespace
                        .ok_or(TooManySupers { super_pos })?;
                }
                comps
            },
        };
        for &name in comps.iter() {
            match c.resolve_sub(name)? {
                Found(sub) => c = sub,
                NotFound(name) => return Ok(NotFound(name)),
            }
        }
        Ok(Found(c))
    }

    /// Resolve a sub-namespace name in this namespace.
    fn resolve_sub(&self, name: &'t str) -> SoftResolveRet<'t, Self> {
        if let Some(sub) = self.cur.subs.get(name) {
            return Ok(Found(self.move_to(sub)));
        }
        if let Some(sub) = self.resolve_in_uses(name, UseST::as_sub)? {
            return Ok(Found(sub));
        }
        self.resolve_in_spaces(
            name,
            &mut self.cur.use_spaces.borrow_mut(),
            Self::resolve_sub,
        )
    }

    /// Resolve a value name in this namespace.
    fn resolve_val(&self, name: &'t str) -> SoftResolveRet<'t, &'a V> {
        if let Some(v) = self.cur.values.get(name) {
            return Ok(Found(v));
        }
        if let Some(v) = self.resolve_in_uses(name, UseST::as_val)? {
            return Ok(Found(v));
        }
        self.resolve_in_spaces(
            name,
            &mut self.cur.use_spaces.borrow_mut(),
            Self::resolve_val,
        )
    }

    fn resolve_in_uses<F, R>(
        &self,
        name: &'t str,
        f:    F,
    ) -> ResolveRet<'t, Option<R>>
    where F: FnOnce(&UseST<'a, 't, T, V>, &'t str)
                -> ResolveRet<'t, Option<R>> {
        match self.cur.use_names.get(name) {
            None => Ok(None),
            Some(&(target, ref stc)) => {
                self.resolve_usest_path(target, stc)
                    .and_then(|()| f(&stc.borrow(), name))
                    .or_cycle(name, target)
            },
        }
    }

    /// Resolve the path component of `use`.
    fn resolve_usest_path(
        &self,
        alias: &'t str,
        stc:   &UseSTCell<'a, 't, T, V>,
    ) -> ResolveRet<'t, ()> {
        use std::mem::replace;
        use self::UseST::*;

        match *stc.borrow() {
            Waiting{ .. } => (),
            _ => return Ok(()),
        }
        match stc.try_borrow_mut() {
            Err(_) => Err(Cycle { begin: Some(alias), steps: vec![] }),
            Ok(mut st) => match replace(&mut *st, PathErr) {
                Waiting { path, name } => {
                    let new_st = match self.walk_resolve(&path)? {
                        Found(subsp) =>
                            PathResolved { subsp, name
                                         , sub: RefCell::new(None)
                                         , val: RefCell::new(None) },
                        NotFound(name) =>
                            PathNotFound { name },
                    };
                    *st = new_st;
                    Ok(())
                },
                _ => unreachable!(), // checked
            },
        }
    }

    /// Resolve a name in namespaces imported by `use`-space.
    fn resolve_in_spaces<R, F>(
        &self,
        name:   &'t str,
        spaces: &mut UseSpaceList<'a, 't, T, V>,
        mut f:  F,
    ) -> SoftResolveRet<'t, R>
    where F: FnMut(&Self, &'t str) -> SoftResolveRet<'t, R> {
        use std::mem::replace;
        use self::UseSpaceST::*;

        let mut found = None;
        let mut sp_names = vec![];
        for &mut (sp_name, ref mut st) in spaces {
            let new_st = match replace(st, PathErr) {
                Waiting(path) => match self.walk_resolve(&path)? {
                    NotFound(name) => PathNotFound { name },
                    Found(sub) => Resolved(sub),
                },
                c => c,
            };
            *st = new_st;

            if let Resolved(ref subsp) = *st {
                if subsp.cur.use_spaces.try_borrow_mut().is_ok() {
                    if let Found(sub) = f(subsp, name)? {
                        found = Some(sub);
                        sp_names.push(sp_name);
                    }
                }
            }
        }
        match (found, sp_names.len()) {
            (None, _) => Ok(NotFound(name)),
            (Some(r), 1) => Ok(Found(r)),
            (Some(_), _) => Err(Ambiguous { name, sp_names }),
        }
    }

    /// Resolve a path to a namespace. It can only be invoked after all `use`s
    /// are resolved. So if error occurs, it must be `NotFound`.
    pub fn query_sub(
        &self,
        path: &Path<'t>,
    ) -> Result<Self, ResolveError<'t>> {
        use self::ResolveError as R;
        match self.walk_resolve(path) {
            Ok(Found(sub)) => Ok(sub),
            Ok(NotFound(name)) => Err(R::NotFound { name }),
            Err(he) => Err(R::from(he)),
        }
    }

    /// Resolve a path to a value. It can only be invoked after all `use`s are
    /// resolved.
    pub fn query_val(
        &self,
        path: &ValPath<'t>,
    ) -> Result<&'a V, ResolveError<'t>> {
        use self::ResolveError as R;
        match self.walk_resolve(&path.0) {
            Ok(Found(sub)) => match sub.resolve_val(path.1) {
                Ok(Found(v)) => Ok(v),
                Ok(NotFound(name)) => Err(R::NotFound { name }),
                Err(he) => Err(R::from(he)),
            },
            Ok(NotFound(name)) => Err(R::NotFound { name }),
            Err(he) => Err(R::from(he)),
        }
    }
}

impl<'a, 't: 'a, T: 'a, V: 'a> PreNameSp<'a, 't, T, V> {
    /// Create an empty namespace with custom infomation `T`.
    pub fn new(info: T) -> Self {
        PreNameSp { root: Box::new(Node {
            father:      Cell::new(None),
            subs:        HashMap::new(),
            use_spaces:  RefCell::new(vec![]),
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

    /// Add a `use ...::*;` into this namespace. `pos` is the identifier used
    /// in error reporting.
    pub fn use_space(&mut self, pos: &'t str, path: Path<'t>) {
        self.root.use_spaces.borrow_mut()
            .push((pos, UseSpaceST::Waiting(path)));
    }

    /// Add a `use ... as ...;` into this namespace and return the old one with
    /// the same name (if any).
    pub fn use_name(
        &mut self,
        name: &'t str,
        path: ValPath<'t>,
    ) -> Option<ValPath<'t>> {
        use self::UseST::Waiting;
        let stc = RefCell::new(Waiting {
            path: path.0,
            name: path.1,
        });
        self.root.use_names
            .insert(name, (name, stc))
            .map(|(_, oldstc)| match oldstc.into_inner() {
                Waiting { path, name } => (path, name),
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
