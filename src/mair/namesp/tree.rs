//! The namespace tree structure storing named ty (sub-namespace) and value
//! objects, providing name resolution.

// FIXME: Cannot derive `Clone` due to rust-lang/rust#26925
#![cfg_attr(feature="clippy", allow(expl_impl_clone_on_copy))]

use std::collections::hash_map::{HashMap, Iter as HashMapIter};
use std::cell::{Cell, RefCell};
use std::convert::{From, Into};
use std::marker::PhantomData;
use std::ops::Deref;
use std::fmt;
use super::run_once::{RunOnce, Runner};
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
#[derive(Debug)]
pub struct NameSp<'a, 't: 'a, T: 'a, V: 'a>(Option<Box<Node<'a, 't, T, V>>>);

impl<'a, 't: 'a, T: 'a, V: 'a> Clone for NameSpPtr<'a, 't, T, V> {
    fn clone(&self) -> Self {
        NameSpPtr { root: self.root, cur: self.cur }
    }
}

impl<'a, 't: 'a, T: 'a, V: 'a> Copy for NameSpPtr<'a, 't, T, V> {}

impl<'a, 't: 'a, T: 'a, V: 'a> PartialEq for NameSpPtr<'a, 't, T, V> {
    fn eq(&self, rhs: &Self) -> bool {
        self.cur as *const _ == rhs.cur
    }
}

impl<'a, 't: 'a, T: 'a, V: 'a> Eq for NameSpPtr<'a, 't, T, V> {}

/// The pointer to a namespace on an immutable namespace tree.
#[derive(Debug)]
pub struct NameSpPtr<'a, 't: 'a, T: 'a, V: 'a> {
    root:   &'a Node<'a, 't, T, V>,
    cur:    &'a Node<'a, 't, T, V>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ResolveError<'t> {
    NotFound      { name: &'t str },
    TooManySupers { super_pos: &'t str },
    UseNothing    { name: &'t str },
    Ambiguous     { name: &'t str, sp_names: Vec<&'t str> },
    Cycle         { steps: Vec<(&'t str, &'t str)> },
}

impl<'t> ResolveError<'t> {
    pub fn get_pos(&self) -> &'t str {
        match *self {
            NotFound { name } |
            TooManySupers { super_pos: name } |
            UseNothing { name } |
            Ambiguous { name, ..} => name,
            Cycle { ref steps } => steps[0].0,
        }
    }
}

type ResolveRet<'t, T> = Result<T, ResolveError<'t>>;

struct StoredResolveRet<'t, T>(Result<T, Cell<Option<ResolveError<'t>>>>);

impl<'t, T: fmt::Debug> fmt::Debug for StoredResolveRet<'t, T> {
    fn fmt(&self, mut f: &mut fmt::Formatter) -> fmt::Result {
        write!(&mut f, "StoredResolveRet(")?;
        match self.0 {
            Ok(ref t) => write!(&mut f, "Ok({:?}))", t),
            Err(ref c) => match c.take() {
                None => write!(&mut f, "None)"),
                Some(e) => {
                    let ret = write!(&mut f, "Some({:?}))", e);
                    c.set(Some(e));     // ^- independent with `self`
                    ret
                },
            },
        }
    }
}

impl<'t, T> Deref for StoredResolveRet<'t, T> {
    type Target = Result<T, Cell<Option<ResolveError<'t>>>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'t, T> From<ResolveRet<'t, T>> for StoredResolveRet<'t, T> {
    fn from(x: ResolveRet<'t, T>) -> Self {
        StoredResolveRet(match x {
            Ok(t) => Ok(t),
            Err(e) => Err(Cell::new(Some(e))),
        })
    }
}

impl<'t, T> StoredResolveRet<'t, T> {
    fn take_err(&self) -> Option<ResolveError<'t>> {
        self.0.as_ref()
            .err()
            .and_then(|e| e.take())
    }
}

trait OptResolveRetExt<'a, 't, T> {
    fn cycle_or_link(&self, name: &'t str, target: &'t str)
            -> ResolveRet<'t, &'a T>;
}

impl<'a, 't, T>
        OptResolveRetExt<'a, 't, T> for Option<&'a StoredResolveRet<'t, T>> {
    fn cycle_or_link(&self, name: &'t str, target: &'t str)
            -> ResolveRet<'t, &'a T> {
        match *self {
            Some(&StoredResolveRet(Ok(ref t))) => Ok(t),
            None => Err(Cycle { steps: vec![(name, target)] }), // start a cycle
            Some(&StoredResolveRet(Err(ref e))) => match e.take() {
                Some(Cycle { mut steps }) =>
                    if str_eqeqeq(steps[0].1, target) {
                        e.set(Some(Cycle { steps })); // find the head of cycle
                        Err(NotFound { name }) // previous error as NotFound
                    } else {
                        steps.push((name, target)); // inside a cycle
                        Err(Cycle { steps })
                    },
                other_err => {
                    e.set(other_err);
                    Err(NotFound { name }) // previous error as NotFound
                },
            },
        }
    }
}

type UseSpaceList<'a, 't: 'a, T: 'a, V: 'a> =
    Vec<(&'t str, RunOnce<UseSpaceResolver<'a, 't, T, V>>)>;

#[derive(Debug)]
struct UseSpaceResolver<'a, 't: 'a, T: 'a, V: 'a> {
    path:   Path<'t>,
    marker: PhantomData<NameSpPtr<'a, 't, T, V>>,
}

impl<'a, 't: 'a, T: 'a, V: 'a> Runner for UseSpaceResolver<'a, 't, T, V> {
    type Arg = NameSpPtr<'a, 't, T, V>;
    type Ret = StoredResolveRet<'t, NameSpPtr<'a, 't, T, V>>;
    fn run(self, sp: Self::Arg) -> Self::Ret {
        sp.walk_resolve(&self.path).into()
    }
}

type UsePathNameST<'a, 't: 'a, T: 'a, V: 'a> =
    RunOnce<UsePathNameResolver<'a, 't, T, V>>;

#[derive(Debug)]
struct UsePathNameResolver<'a, 't: 'a, T: 'a, V: 'a> {
    path:   Path<'t>,
    name:   &'t str,
    marker: PhantomData<NameSpPtr<'a, 't, T, V>>,
}

impl<'a, 't: 'a, T: 'a, V: 'a> Runner for UsePathNameResolver<'a, 't, T, V> {
    type Arg = NameSpPtr<'a, 't, T, V>;
    type Ret = StoredResolveRet<'t, UseNameST<'a, 't, T, V>>;
    fn run(self, sp: Self::Arg) -> Self::Ret {
        sp.walk_resolve(&self.path)
          .map(|sp| UseNameST {
            sp,
            name:   self.name,
            as_sub: RunOnce::new(SubNameResolver { marker: PhantomData }),
            as_val: RunOnce::new(ValNameResolver { marker: PhantomData }),
          })
          .into()
    }
}

#[derive(Debug)]
struct UseNameST<'a, 't: 'a, T: 'a, V: 'a> {
    sp:     NameSpPtr<'a, 't, T, V>,
    name:   &'t str,
    as_sub: RunOnce<SubNameResolver<'a, 't, T, V>>,
    as_val: RunOnce<ValNameResolver<'a, 't, T, V>>,
}

#[derive(Debug)]
struct SubNameResolver<'a, 't: 'a, T: 'a, V: 'a> {
    marker: PhantomData<NameSpPtr<'a, 't, T, V>>,
}

impl<'a, 't: 'a, T: 'a, V: 'a> Runner for SubNameResolver<'a, 't, T, V> {
    type Arg = (NameSpPtr<'a, 't, T, V>, &'t str);
    type Ret = StoredResolveRet<'t, NameSpPtr<'a, 't, T, V>>;
    fn run(self, (sp, name): Self::Arg) -> Self::Ret {
        sp.resolve_sub(name)
          .into()
    }
}

#[derive(Debug)]
struct ValNameResolver<'a, 't: 'a, T: 'a, V: 'a> {
    marker: PhantomData<NameSpPtr<'a, 't, T, V>>,
}

impl<'a, 't: 'a, T: 'a, V: 'a> Runner for ValNameResolver<'a, 't, T, V> {
    type Arg = (NameSpPtr<'a, 't, T, V>, &'t str);
    type Ret = StoredResolveRet<'t, &'a V>;
    fn run(self, (sp, name): Self::Arg) -> Self::Ret {
        sp.resolve_val(name)
          .into()
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
    use_names:  HashMap<&'t str, (&'t str, UsePathNameST<'a, 't, T, V>)>,
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

impl<'a, 't: 'a, T: 'a, V: 'a> Iterator for SubIter<'a, 't, T, V> {
    type Item = (&'t str, NameSpPtr<'a, 't, T, V>);
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
            .map(|(&name, cur)| (name, NameSpPtr { root: self.root, cur }))
    }
}

#[derive(Debug)]
pub struct ValIter<'a, 't: 'a, V: 'a> {
    iter: HashMapIter<'a, &'t str, V>,
}

impl<'a, 't: 'a, V: 'a> Iterator for ValIter<'a, 't, V> {
    type Item = (&'t str, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
            .map(|(&name, v)| (name, v))
    }
}

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
    fn dfs_set_father(&self) {
        for (_, sub) in self.subs() {
            sub.cur.father.set(Some(self.cur));
            sub.dfs_set_father();
        }
    }

    /// DFS to resolve all queries.
    fn dfs_resolve_all(&self) {
        for &(_, ref st) in self.cur.use_names.values() {
            if let Ok(ref nst) = **st.run(self.clone()) {
                nst.as_sub.run((nst.sp, nst.name));
                nst.as_val.run((nst.sp, nst.name));
            }
        }
        for &(_, ref st) in &*self.cur.use_spaces.borrow_mut() {
            st.run(*self);
        }
        for sub in self.cur.subs.values() {
            self.move_to(sub).dfs_resolve_all();
        }
    }

    fn dfs_collect_err(&self, errs: &mut Vec<ResolveError<'t>>) {
        for &(_, ref st) in self.cur.use_names.values() {
            match **st.run(*self) {
                Err(ref c) => errs.extend(c.take()),
                Ok(UseNameST { sp, name, ref as_sub, ref as_val }) =>
                    match as_sub.run((sp, name)).take_err() {
                        Some(NotFound { name }) => {
                            match as_val.run((sp, name)).take_err() {
                                Some(NotFound { name }) =>
                                    errs.push(UseNothing { name }),
                                e => errs.extend(e),
                            }
                        },
                        e => errs.extend(e),
                    },
            }
        }
        for &(_, ref st) in &*self.cur.use_spaces.borrow_mut() {
            errs.extend(st.run(*self).take_err());
        }
        for sub in self.cur.subs.values() {
            self.move_to(sub).dfs_collect_err(errs);
        }
    }

    /// Resolve a path from this namespace.
    fn walk_resolve(&self, path: &Path<'t>) -> ResolveRet<'t, Self> {
        let mut c = *self;
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
            c = c.resolve_sub(name)?;
        }
        Ok(c)
    }

    /// Resolve a sub-namespace name in this namespace.
    fn resolve_sub(&self, name: &'t str) -> ResolveRet<'t, Self> {
        if let Some(sub) = self.cur.subs.get(name) {
            return Ok(self.move_to(sub));
        }
        if let Some(sub) = self.resolve_in_uses(name, |nst| &nst.as_sub)? {
            return Ok(sub);
        }
        if let Ok(mut sts) = self.cur.use_spaces.try_borrow_mut() {
            return self.resolve_in_spaces(&mut *sts, name, Self::resolve_sub);
        }
        Err(NotFound { name })
    }

    /// Resolve a value name in this namespace.
    fn resolve_val(&self, name: &'t str) -> ResolveRet<'t, &'a V> {
        if let Some(v) = self.cur.values.get(name) {
            return Ok(v);
        }
        if let Some(v) = self.resolve_in_uses(name, |nst| &nst.as_val)? {
            return Ok(v);
        }
        if let Ok(mut sts) = self.cur.use_spaces.try_borrow_mut() {
            return self.resolve_in_spaces(&mut *sts, name, Self::resolve_val);
        }
        Err(NotFound { name })
    }

    fn resolve_in_uses<F, Rn, R: Copy>(&self, name: &'t str, selector: F)
            -> ResolveRet<'t, Option<R>>
    where F: for<'r> Fn(&'r UseNameST<'a, 't, T, V>) -> &'r RunOnce<Rn>,
          Rn: Runner<Arg=(Self, &'t str), Ret=StoredResolveRet<'t, R>> {
        let (target, st) = match self.cur.use_names.get(name) {
            None => return Ok(None),
            Some(&(target, ref st)) => (target, st),
        };
        macro_rules! try_fuxk {
            ($e:expr) => {
                match $e {
                    Err(NotFound { .. }) => return Ok(None),
                    Err(e) => return Err(e),
                    Ok(x) => x,
                }
            };
        }
        let nst = try_fuxk!(st.try_run(*self)
                              .cycle_or_link(name, target));
        let ret = try_fuxk!(selector(nst).try_run((nst.sp, nst.name))
                                         .cycle_or_link(name, target));
        Ok(Some(*ret))
    }

    /// Resolve a name in namespaces imported by `use`-space.
    fn resolve_in_spaces<R, F>(
        &self,
        spaces:   &mut UseSpaceList<'a, 't, T, V>,
        name:     &'t str,
        searcher: F,
    ) -> ResolveRet<'t, R>
    where F: Fn(&Self, &'t str) -> ResolveRet<'t, R> {
        let mut found = None;
        let mut sp_names = vec![];
        for &(sp_name, ref st) in & *spaces {
            if let Ok(ref sp) = **st.run(*self) { // `spaces` has unique access
                match searcher(sp, name) {
                    Err(NotFound { .. }) => (),
                    Ok(r) => {
                        found = Some(r);
                        sp_names.push(sp_name);
                    },
                    Err(Ambiguous { sp_names: mut sub_sp_names, .. }) =>
                        sp_names.extend(sub_sp_names),
                    Err(TooManySupers { .. }) |
                    Err(UseNothing { .. }) |
                    Err(Cycle { .. }) => unreachable!(),
                }
            }
        }
        match (found, sp_names.len()) {
            (Some(r), 1) => Ok(r),
            (None, _) => Err(NotFound { name }),
            (Some(_), _) => Err(Ambiguous { name, sp_names }),
        }
    }

    /// Resolve a path to a namespace. It can only be invoked after all `use`s
    /// are resolved.
    pub fn query_sub(&self, path: &Path<'t>) -> ResolveRet<'t, Self> {
        self.walk_resolve(path)
    }

    /// Resolve a path to a value. It can only be invoked after all `use`s are
    /// resolved.
    pub fn query_val(&self, path: &ValPath<'t>) -> ResolveRet<'t, &'a V> {
        self.walk_resolve(&path.0)
            .and_then(|sp| sp.resolve_val(path.1))
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

    /// Add a `use ...::*;` into this namespace. `sp_name` is the identifier
    /// used in error reporting.
    pub fn use_space(&mut self, sp_name: &'t str, path: Path<'t>) {
        self.root.use_spaces.borrow_mut()
            .push((sp_name, RunOnce::new(UseSpaceResolver {
                path,
                marker: PhantomData,
            })));
    }

    /// Add a `use ... as ...;` into this namespace and return the old one with
    /// the same name (if any).
    pub fn use_name(
        &mut self,
        name: &'t str,
        path: ValPath<'t>,
    ) -> Option<ValPath<'t>> {
        let st = RunOnce::new(UsePathNameResolver {
            path:   path.0,
            name:   path.1,
            marker: PhantomData,
        });
        self.root.use_names
            .insert(name, (name, st))
            .map(|(_, oldst)| match oldst.get_runner() {
                Some(UsePathNameResolver { path, name, .. } ) => (path, name),
                _ => unreachable!(), // no resolutions happend in `PreNameSp`
            })
    }

    /// Consume the `PreNameSp`, resolve all name required by `use`s and return
    /// a frozen namespace structure.
    pub fn resolve_uses(
        self,
        container: &'a mut NameSp<'a, 't, T, V>,
    ) -> (NameSpPtr<'a, 't, T, V>, Vec<ResolveError<'t>>) {
        container.0 = Some(self.root);
        let r = container.0.as_ref().unwrap();
        let p = NameSpPtr { root: r, cur: r };
        let mut errs = vec![];
        p.dfs_set_father();
        p.dfs_resolve_all();
        p.dfs_collect_err(&mut errs);
        (p, errs)
    }
}

/// Compare two string slices' location. Return true only if they point to the
/// same memory and have equal lengths.
fn str_eqeqeq(a: &str, b: &str) -> bool {
    a.as_ptr() == b.as_ptr() && a.len() == b.len()
}

#[cfg(test)]
mod tests {
    use super::*;

    type PreSp<'a, 't> = PreNameSp<'a, 't, &'static str, i32>;
    type Sp<'a, 't> = NameSp<'a, 't, &'static str, i32>;

    macro_rules! path {
        (($($sup:tt).*).$($comp:tt).*) => {
            Path::Relative{ supers: vec![$($sup),*], comps: vec![$($comp),*] }
        };
        ($($comp:tt).*) => {
            Path::Absolute{ comps: vec![$($comp),*] }
        };
    }

    macro_rules! valpath {
        ($($t:tt)*) => { path!($($t)*).pop().unwrap() };
    }

    macro_rules! ns {
        (@$pre:ident) => {};
        (@$pre:ident use [$($p:tt)*] as $name:tt; $($t:tt)*) => {
            $pre.use_name($name, path!($($p)*).pop().unwrap());
            ns!(@$pre $($t)*);
        };
        (@$pre:ident useall $name:tt [$($p:tt)*]; $($t:tt)*) => {
            $pre.use_space($name, path!($($p)*));
            ns!(@$pre $($t)*);
        };
        (@$pre:ident $name:tt : ns! { $($sub:tt)* }; $($t:tt)*) => {
            $pre.add_sub($name, ns!($($sub)*));
            ns!(@$pre $($t)*);
        };
        (@$pre:ident $name:tt : $e:expr; $($t:tt)*) => {
            $pre.add_value($name, $e);
            ns!(@$pre $($t)*);
        };
        (<$info:tt> $($t:tt)*) => {{
            let mut pre = PreSp::new($info);
            ns!(@pre $($t)*);
            pre
        }};
    }

    fn sort_errs<'t>(
        s: &str,
        v: Vec<ResolveError<'t>>,
    ) -> Vec<(&'t str, isize, ResolveError<'t>)> {
        use std::mem::discriminant;
        use std::hash::{Hash, Hasher};
        use parse::str_ptr_diff;
        let mut v = v.into_iter()
            .map(|e| {
                let pos = e.get_pos();
                (pos, str_ptr_diff(pos, s), e)
            })
            .collect::<Vec<_>>();
        v.sort_unstable_by_key(|&(_, ipos, ref k)| {
            use std::collections::hash_map::DefaultHasher;
            let mut h = DefaultHasher::new();
            discriminant(k).hash(&mut h);
            (h.finish(), ipos)
        });
        v
    }

    #[test]
    fn basic_test() {
        let mut sp = Sp::new(); // should live longer than `PreNameSp`
        let pre = ns! { <"root">
            useall "useall 1" ["b"];
            use ["a"] as "b";
            "a": ns! { <"mod a">
                "b": 2;
                "c": 3;
            };
            "c": 1;
        };
        let (root, errs) = pre.resolve_uses(&mut sp);
        assert_eq!(errs, vec![]);
        assert_eq!(root.get_root(), root);
        assert_eq!(root.get_father(), None);
        assert_eq!(root.get_info(), &"root");

        let a1 = root.query_sub(&path!("a")).unwrap();
        let a2 = root.query_sub(&path!(()."b")).unwrap();
        let a3 = a1.query_sub(&path!(("sup1")."a")).unwrap();
        assert_eq!(root.query_sub(&path!("c")),
                   Err(NotFound { name: "c" }));
        assert_eq!(a1, a2);
        assert_eq!(a1, a3);
        assert_eq!(a1.get_root(), root);
        assert_eq!(a1.get_father(), Some(root));
        assert_eq!(a1.get_info(), &"mod a");

        assert_eq!(root.subs().collect::<Vec<_>>(), vec![("a", a1)]);
        assert_eq!(root.values().collect::<Vec<_>>(), vec![("c", &1)]);

        assert_eq!(root.query_val(&valpath!("b")), Ok(&2));
        assert_eq!(root.query_val(&valpath!("c")), Ok(&1));
        assert_eq!(root.query_val(&valpath!("a")),
                   Err(NotFound { name: "a" }));
        assert_eq!(a1.query_val(&valpath!("c")), Ok(&1));
        assert_eq!(a1.query_val(&valpath!(()."c")), Ok(&3));
        assert_eq!(a1.query_val(&valpath!(("sup1")."c")), Ok(&1));
        assert_eq!(a1.query_val(&valpath!(("sup1")."a"."x")),
                   Err(NotFound { name: "x" }));
        assert_eq!(a1.query_val(&valpath!(("sup1")."a"."x"."y")),
                   Err(NotFound { name: "x" }));
        assert_eq!(a1.query_val(&valpath!(("sup1"."sup2")."c")),
                   Err(TooManySupers { super_pos: "sup2" }));
    }

    #[test]
    fn useall_cycle_test() {
        let mut sp = Sp::new();
        let pre = ns! { <"root">
            useall "useall 1" ["a"];
            useall "useall 2" ["b"];
            "a": ns! { <"mod a">
                "x": 1;
                "x": ns! { <"mod x">
                    "a": 3;
                };
            };
            "b": ns! { <"mod b">
                useall "useall 3" [];
                "x": 2;
            };
        };
        let (root, errs) = pre.resolve_uses(&mut sp);
        assert_eq!(errs, vec![]);
        assert_eq!(root.query_val(&valpath!(()."x")), Err(
            Ambiguous { name: "x", sp_names: vec!["useall 1", "useall 2"] }
        ));
        let b = root.query_sub(&path!("b")).unwrap();
        let x = root.query_sub(&path!("a"."x")).unwrap();
        assert_eq!(b.query_sub(&path!(()."x")), Ok(x));
    }

    #[test]
    fn cycle1_pos_test() {
        let s = "aa".to_owned();
        let (a0, a1) = (&s[0..1], &s[1..2]);
        let mut sp = Sp::new();
        let pre = ns! { <"root">
            use [a0] as a1;
        };
        let errs = sort_errs(&s, pre.resolve_uses(&mut sp).1);
        assert_eq!(errs, vec![
            ("a", 0, Cycle { steps: vec![("a", "a")] }),
        ]);
        match errs[0].2 {
            Cycle { ref steps } => {
                assert!(str_eqeqeq(steps[0].0, a0));
                assert!(str_eqeqeq(steps[0].1, a1));
            },
            _ => unreachable!(),
        }
    }

    #[test]
    fn cycle2_pos_test() {
        let s = "aabb".to_owned();
        let (a0, a1, b2, b3) = (&s[0..1], &s[1..2], &s[2..3], &s[3..4]);
        let mut sp = Sp::new();
        let pre = ns! { <"root">
            use [a0] as b2;
            use [b3] as a1;
        };
        let errs = sort_errs(&s, pre.resolve_uses(&mut sp).1);
        assert!(
            errs == vec![
                ("a", 0, Cycle { steps: vec![("a", "a"), ("b", "b")] })
            ] ||
            errs == vec![
                ("b", 3, Cycle { steps: vec![("b", "b"), ("a", "a")] })
            ],
            "{:?}", errs
        );
        match (errs[0].1, &errs[0].2) {
            (0, &Cycle { ref steps }) => {
                assert!(str_eqeqeq(steps[0].0, a0));
                assert!(str_eqeqeq(steps[0].1, a1));
                assert!(str_eqeqeq(steps[1].0, b3));
                assert!(str_eqeqeq(steps[1].1, b2));
            },
            (3, &Cycle { ref steps }) => {
                assert!(str_eqeqeq(steps[0].0, b3));
                assert!(str_eqeqeq(steps[0].1, b2));
                assert!(str_eqeqeq(steps[1].0, a0));
                assert!(str_eqeqeq(steps[1].1, a1));
            },
            _ => unreachable!(),
        }
    }
}
