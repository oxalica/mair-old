/// The namespace tree structure storing named ty (sub-namespace) and value
/// objects, providing name resolution.

use std::collections::hash_map::{HashMap, Iter as HashMapIter};
use std::cell::{Cell, RefCell};
use std::marker::PhantomData;
use std::rc::{Rc, Weak};
use super::{Path, ValPath};
use self::ResolveError::*;

/// The mutable namespace tree with unresolved `use`s.
#[derive(Debug)]
pub struct PreNameSp<'t, T, V> {
    root: Rc<NodeCell<'t, T, V>>,
}

/// The immutable namespace tree with all `use`s resolved.
#[derive(Debug)]
pub struct NameSp<'t, T, V>(Rc<NodeCell<'t, T, V>>);

/// The pointer to a (sub-)namespace on a namespace tree.
#[derive(Debug)]
pub struct NameSpPtr<'a, 't, T: 'a, V: 'a> {
    root:   Rc<NodeCell<'t, T, V>>,
    cur:    Rc<NodeCell<'t, T, V>>,
    marker: PhantomData<&'a NameSp<'a, T, V>>,
}

#[derive(Debug)]
enum ResolveState<P, T> {
    Waiting { path: P, visiting: bool },
    Resolved(T),
    Unresolved,
}

type SubResolveState<'t, T, V> =
    ResolveState<Path<'t>, Weak<NodeCell<'t, T, V>>>;
type ValResolveState<'t, V> =
    ResolveState<ValPath<'t>, Weak<V>>;

#[derive(Debug)]
struct UseNameState<'t, T, V> {
    as_sub: RefCell<SubResolveState<'t, T, V>>,
    as_val: RefCell<ValResolveState<'t, V>>,
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
enum OwnOrLink<T> {
    Owned(Rc<T>),
    Link (Weak<T>),
}

impl<T> OwnOrLink<T> {
    fn upgrade(&self) -> Rc<T> {
        match *self {
            OwnOrLink::Owned(ref rc) => Rc::clone(rc),
            OwnOrLink::Link(ref w) => w.upgrade().unwrap(),
        }
    }
}

type NodeCell<'t, T, V> = RefCell<Node<'t, T, V>>;

#[derive(Debug)]
struct Node<'t, T, V> {
    father:     Option<Weak<NodeCell<'t, T, V>>>,
    /// Sub namespaces. May be `mod`, `struct` or a block.
    subs:       HashMap<&'t str, OwnOrLink<NodeCell<'t, T, V>>>,
    space_lock: Cell<bool>,
    /// Namespaces imported by `use ...::*`. When the namespace is frozen
    /// (`NameSp`), it must all hold `Resolved`.
    use_spaces: Vec<RefCell<SubResolveState<'t, T, V>>>,
    /// Names imported by `use`. When the namespace is frozen (`NameSp`), it
    /// must be empty and all names will be added into `subs` or `values`.
    use_names:  HashMap<&'t str, UseNameState<'t, T, V>>,
    /// Information of this namespace.
    info:       T,
    /// Values in this namespace.
    values:     HashMap<&'t str, Rc<V>>,
}

// TODO: `derive(Clone)` cause return type errors (???) but this don't
impl<'a, 't, T: 'a, V: 'a> Clone for NameSpPtr<'a, 't, T, V> {
    fn clone(&self) -> Self {
        NameSpPtr {
            root:   Rc::clone(&self.root),
            cur:    Rc::clone(&self.cur),
            marker: PhantomData,
        }
    }
}

impl<'a, 't, T: 'a, V: 'a> NameSpPtr<'a, 't, T, V> {
    fn move_to(&self, cell: Rc<NodeCell<'t, T, V>>) -> Self {
        NameSpPtr {
            root:   Rc::clone(&self.root),
            cur:    cell,
            marker: PhantomData,
        }
    }

    pub fn get_root(&self) -> Self {
        self.move_to(Rc::clone(&self.root))
    }

    /// The the namespace which owned this namespace (if any).
    pub fn get_father(&self) -> Option<Self> {
        self.cur.borrow().father
            .as_ref()
            .map(|w| self.move_to(w.upgrade().unwrap())) // nodes lives in 'a
    }

    /// Get the custom information `T` of this namespace.
    pub fn get_info(&self) -> &'a T {
        unimplemented!()
    }

    /// Get an iterator over all values owned by this namespace.
    pub fn values(&self) -> HashMapIter<'a, &'t str, V> {
        unimplemented!()
    }

    fn resolve_all(&self) -> Vec<ResolveError<'t>> {
        let node = self.cur.borrow();
        let mut errs = vec![];
        { // TODO: ugly
            let mut f = |e: Option<ResolveError<'t>>| if let Some(e) = e {
                errs.push(e)
            };
            for st in node.use_names.values() {
                f(self.resolve_sub_path(&st.as_sub).err());
                f(self.resolve_val_path(&st.as_val).err());
            }
            for st in &node.use_spaces {
                f(self.resolve_sub_path(st).err());
            }
        }
        for sub in node.subs.values() {
            if let OwnOrLink::Owned(ref child) = *sub {
                errs.append(&mut self.move_to(Rc::clone(child)).resolve_all());
            }
        }
        errs
    }

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

    fn resolve_sub(&self, name: &'t str) -> ResolveRet<'t, Self> {
        let node = self.cur.borrow();
        match node.subs.get(name) {
            Some(sub) => Ok(self.move_to(sub.upgrade())),
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

    fn resolve_val(&self, name: &'t str) -> ResolveRet<'t, Weak<V>> {
        let node = self.cur.borrow();
        match node.values.get(name) {
            Some(v) => Ok(Rc::downgrade(v)),
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

    fn resolve_sub_path(
        &self,
        st: &RefCell<SubResolveState<'t, T, V>>,
    ) -> ResolveRet<'t, Self> {
        use self::ResolveState::*;
        match *st.borrow_mut() {
            Resolved(ref w) => return Ok(self.move_to(w.upgrade().unwrap())),
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
            Ok(ref sub) => Resolved(Rc::downgrade(&sub.cur)),
            Err(_) => Unresolved,
        };
        ret
    }

    fn resolve_val_path(
        &self,
        st: &RefCell<ValResolveState<'t, V>>,
    ) -> ResolveRet<'t, Weak<V>> {
        use self::ResolveState::*;
        match *st.borrow_mut() {
            Resolved(ref w) => return Ok(Weak::clone(w)),
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
            Ok(ref w) => Resolved(Weak::clone(w)),
            Err(_) => Unresolved,
        };
        ret
    }

    fn with_spaces<R, F>(&self, mut f: F) -> ResolveRet<'t, Option<R>>
    where F: FnMut(Self) -> ResolveRet<'t, Option<R>> {
        let node = self.cur.borrow();
        node.space_lock.set(true);
        for st in &node.use_spaces {
            let sub = self.resolve_sub_path(st)?;
            // If `a` use `b::*` and `b` use `a::*`, skip
            if !sub.cur.borrow().space_lock.get() {
                if let Some(ret) = f(sub)? {
                    return Ok(Some(ret));
                }
            }
        }
        Ok(None)
    }

    /// Resolve a path to a namespace.
    pub fn query_sub(&self, path: &Path<'t>) -> ResolveRet<'t, Self> {
        unimplemented!()
    }

    /// Resolve a path to a value.
    pub fn query_val(&self, path: &ValPath<'t>) -> ResolveRet<'t, &'a V> {
        unimplemented!()
    }
}

impl<'t, T, V> PreNameSp<'t, T, V> {
    /// Create an empty namespace with custom infomation `T`.
    pub fn new(info: T) -> Self {
        let node = Node {
            father:      None,
            subs:        HashMap::new(),
            space_lock:  Cell::new(false),
            use_spaces:  vec![],
            use_names:   HashMap::new(),
            info,
            values:      HashMap::new(),
        };
        PreNameSp { root: Rc::new(RefCell::new(node)) }
    }

    /// Add a sub-namespace and return the old one with the same name (if any).
    pub fn add_sub(
        &mut self,
        name: &'t str,
        sub: PreNameSp<'t, T, V>,
    ) -> Option<PreNameSp<'t, T, V>> {
        use self::OwnOrLink::*;
        self.root.borrow_mut().subs
            .insert(name, Owned(sub.root))
            .map(|old| match old {
                Owned(rc) => PreNameSp { root: rc },
                Link(_) => unreachable!(), // no resolutions in `PreNameSp`
            })
    }

    /// Add a `use ...::*;` into this namespace.
    pub fn use_space(&mut self, path: Path<'t>) {
        self.root.borrow_mut().use_spaces
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
        self.root.borrow_mut().use_names
            .insert(name, st)
            .map(|st| match st.as_val.into_inner() {
                Waiting { path, .. } => path,
                _ => unreachable!(), // no resolutions in `PreNameSp`
            })
    }

    /// Consume the `PreNameSp`, resolve all name required by `use`s and return
    /// a frozen namespace structure.
    pub fn resolve_uses(self) -> (NameSp<'t, T, V>, Vec<ResolveError<'t>>) {
        let errs = (NameSpPtr {
            root:   Rc::clone(&self.root),
            cur:    Rc::clone(&self.root),
            marker: PhantomData,
        }).resolve_all();
        (NameSp(self.root), errs)
    }
}

impl<'t, T, V> NameSp<'t, T, V> {
    pub fn root<'a>(&'a self) -> NameSpPtr<'a, 't, T, V> {
        NameSpPtr {
            root:   Rc::clone(&self.0),
            cur:    Rc::clone(&self.0),
            marker: PhantomData,
        }
    }
}
