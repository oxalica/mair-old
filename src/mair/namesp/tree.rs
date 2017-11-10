/// The namespace tree structure storing named ty (sub-namespace) and value
/// objects, providing name resolution.

// TODO: Change raw pointers to `Shared<_>` when stable.

use std::collections::hash_map::{HashMap, Iter as HashMapIter};
use std::ptr::null_mut;
use std::mem::forget;
pub use parse::ast::UsePath as Path;
use self::QueryRet::*;

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
#[derive(Debug)]
pub struct NameSpPtr<'a, 't: 'a, T: 'a, V: 'a>(&'a Node<'t, T, V>);

#[derive(Debug)]
pub enum QueryRet<T> {
    NotFound,
    Just(T),
    Ambig(Vec<T>),
}

type SubQueryRetRaw<'t, T, V> =
    QueryRet<*const Node<'t, T, V>>;
type ValQueryRetRaw<'t, T, V> =
    QueryRet<(*const Node<'t, T, V>, &'t str, *const V)>;
type SubQueryRet<'a, 't: 'a, T: 'a, V: 'a> =
    QueryRet<NameSpPtr<'a, 't, T, V>>;
type ValQueryRet<'a, 't: 'a, T: 'a, V: 'a> =
    QueryRet<(NameSpPtr<'a, 't, T, V>, &'t str, &'a V)>;

impl<T> QueryRet<T> {
    fn map_clone<U, F: FnMut(&T) -> U>(&self, mut f: F) -> QueryRet<U> {
        match *self {
            NotFound => NotFound,
            Just(ref x) => Just(f(x)),
            Ambig(ref xs) => Ambig(xs.iter().map(f).collect()),
        }
    }
}

#[derive(Debug)]
struct Node<'t, T, V> {
    /// The pointer to the father node.
    father:      *mut Node<'t, T, V>,
    /// Sub namespaces. May be `mod`, `struct` or a block.
    subs:        HashMap<&'t str, *mut Node<'t, T, V>>,
    /// Namespaces imported by `use ...::*`.
    use_spaces:  Vec<Path<'t>>,
    /// Names imported by `use`.
    use_names:   HashMap<&'t str, Path<'t>>,
    /// Information of this namespace.
    info:        T,
    /// Values in this namespace.
    values:      HashMap<&'t str, V>,
    /// Sub-namespace (or ty) name queries. When the namespace is frozen
    /// (`NameSp`) , it must hold a `QueryRet` rather than `None`.
    sub_queries: HashMap<Path<'t>, Option<SubQueryRetRaw<'t, T, V>>>,
    /// Value name queries. When the namespace is frozen (`NameSp`), it must
    /// hold a `QueryRet` rather than `None`.
    val_queries: HashMap<Path<'t>, Option<ValQueryRetRaw<'t, T, V>>>,
}

pub struct SubIter<'a, 't: 'a, T: 'a, V: 'a>
    (HashMapIter<'a, &'t str, *mut Node<'t, T, V>>);

impl<'a, 't: 'a, T: 'a, V: 'a> Iterator for SubIter<'a, 't, T, V> {
    type Item = (&'t str, NameSpPtr<'a, 't, T, V>);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
            .map(|(&name, &p)| unsafe {
                (name, NameSpPtr(p.as_ref().unwrap())) // not null
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
            sub_queries: HashMap::new(),
            val_queries: HashMap::new(),
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
        unsafe { (*self.root).use_spaces.push(path); }
    }

    /// Add a `use ... as ...;` into this namespace and return the old one with
    /// the same name (if any).
    pub fn use_name(
        &mut self,
        name: &'t str,
        path: Path<'t>,
    ) -> Option<Path<'t>> {
        unsafe { (*self.root).use_names.insert(name, path) }
    }

    /// Add a sub-namespace (or ty) name query waiting to be resolved before
    /// calling `resolve()`. If there's the same query before, it will do
    /// nothing.
    pub fn add_sub_query(&mut self, path: Path<'t>) {
        unsafe { (*self.root).sub_queries.entry(path).or_insert(None); }
    }

    /// Add a value name query waiting to be resolved before calling
    /// `resolve()`. If there's the same query before, it will do nothing.
    pub fn add_value_query(&mut self, path: Path<'t>) {
        unsafe { (*self.root).val_queries.entry(path).or_insert(None); }
    }

    /// Consume the namespace builder, resolve all name queries and return a
    /// frozen namespace structure.
    pub fn resolve(self) -> NameSp<'t, T, V> {
        unimplemented!()
    }
}

impl<'t, T, V> Drop for PreNameSp<'t, T, V> {
    fn drop(&mut self) {
        unsafe { drop(NameSp(Box::from_raw(self.root))); }
    }
}

impl<'t, T, V> NameSp<'t, T, V> {
    pub fn root<'a>(&'a self) -> NameSpPtr<'a, 't, T, V> {
        NameSpPtr(&self.0)
    }
}

impl<'a, 't, T, V> NameSpPtr<'a, 't, T, V> {
    /// Get the custom information `T` of this namespace.
    pub fn info(&self) -> &'a T {
        &self.0.info
    }

    /// Get the value with `name` in this namespace.
    pub fn get_value(&self, name: &'t str) -> Option<&'a V> {
        self.0.values.get(name)
    }

    /// Get an iterator over all values in this namespace.
    pub fn values(&self) -> HashMapIter<'a, &'t str, V> {
        self.0.values.iter()
    }

    /// Get the ty(sub) with `name` in this namespace.
    pub fn get_sub(&self, name: &'t str) -> Option<NameSpPtr<'a, 't, T, V>> {
        self.0.subs.get(name)
            .map(|p| unsafe {
                NameSpPtr(p.as_ref().unwrap())  // not null
            })
    }

    pub fn subs(&self) -> SubIter<'a, 't, T, V> {
        SubIter(self.0.subs.iter())
    }

    /// Get the father namespace (if any).
    pub fn get_father(&self) -> Option<NameSpPtr<'a, 't, T, V>> {
        unsafe { self.0.father.as_ref().map(NameSpPtr) }
    }

    /// Get the result of a sub-namespace name query stored before.
    pub fn get_sub_query_ret(
        &self,
        path: &Path<'t>,
    ) -> Option<SubQueryRet<'a, 't, T, V>> {
        match self.0.sub_queries.get(path) {
            None => None,
            Some(&Some(ref q)) => Some(q.map_clone(|p| unsafe {
                NameSpPtr(p.as_ref().unwrap()) // not null
            })),
            Some(&None) => unreachable!(), // must hold a `QueryRet`
        }
    }

    /// Get the result of a value name query stored before.
    pub fn get_value_query_ret(
        &self,
        path: &Path<'t>,
    ) -> Option<ValQueryRet<'a, 't, T, V>> {
        match self.0.val_queries.get(path) {
            None => None,
            Some(&Some(ref q)) =>
                Some(q.map_clone(|&(ps, name, pv)| unsafe {
                    (NameSpPtr(ps.as_ref().unwrap()), // not null
                     name,
                     pv.as_ref().unwrap(), // not null
                    )
                })),
            Some(&None) => unreachable!(), // must hold a `QueryRet`
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

