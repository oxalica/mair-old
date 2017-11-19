/// The tree structure of global namespaces and local scopes.

mod tree;

pub use self::tree::{PreNameSp, NameSp, NameSpPtr};

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Path<'a> {
    Absolute{ comps: Vec<&'a str> },
    Relative{ supers: usize, comps: Vec<&'a str> },
}

type ValPath<'a> = (Path<'a>, &'a str);

impl<'a> Path<'a> {
    /// Split out the last component.
    pub fn pop(self) -> Result<ValPath<'a>, Self> {
        match self {
            Path::Absolute{ mut comps } => match comps.pop() {
                Some(last) => Ok((Path::Absolute { comps }, last)),
                None => Err(Path::Absolute { comps }),
            },
            Path::Relative{ supers, mut comps } => match comps.pop() {
                Some(last) => Ok((Path::Relative { supers, comps }, last)),
                None => Err(Path::Relative { supers, comps }),
            }
        }
    }

    /// Push a component to the end of path.
    pub fn push(self, comp: &'a str) -> Self {
        match self {
            Path::Absolute{ mut comps } => {
                comps.push(comp);
                Path::Absolute { comps }
            },
            Path::Relative{ supers, mut comps } => {
                comps.push(comp);
                Path::Relative{ supers, comps }
            },
        }
    }
}
