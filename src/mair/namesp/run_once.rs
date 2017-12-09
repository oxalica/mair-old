use std::cell::UnsafeCell;
use std::fmt;
use self::State::*;

pub trait Runner {
    type Arg;
    type Ret;
    fn run(self, arg: Self::Arg) -> Self::Ret;
}

enum State<R: Runner> {
    Running,
    Thunk(R),
    Value(R::Ret),
}

pub struct RunOnce<R: Runner> {
    st: UnsafeCell<State<R>>,
}

impl<R: Runner> RunOnce<R> {
    pub fn new(runner: R) -> Self {
        RunOnce { st: UnsafeCell::new(Thunk(runner)) }
    }

    pub fn run(&self, arg: R::Arg) -> &R::Ret {
        self.try_run(arg).unwrap()
    }

    pub fn try_run(&self, arg: R::Arg) -> Option<&R::Ret> {
        use std::ptr::replace;
        unsafe {
            match *self.st.get() {
                Value(ref v) => return Some(v),
                Thunk(_) => (),
                Running => return None,
            }
            let v = match replace(self.st.get(), Running) {
                Thunk(f) => f.run(arg),
                _ => impossible(), // checked and locked when `Running`
            };
            *self.st.get() = Value(v);
            match *self.st.get() {
                Value(ref v) => Some(v),
                _ => impossible(), // just set `Value`
            }
        }
    }

    pub fn get_runner(self) -> Option<R> {
        unsafe {
            match self.st.into_inner() {
                Thunk(r) => Some(r),
                Value(_) => None,
                Running => impossible(), // `self` takes ownership
            }
        }
    }
}

impl<R: Runner> fmt::Debug for RunOnce<R>
where R::Ret: fmt::Debug {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        unsafe {
            match *self.st.get() {
                Value(ref v) =>
                    write!(fmt, "RunOnce({:?})", v),
                Thunk(_) =>
                    write!(fmt, "RunOnce(<thunk>)"),
                Running =>
                    write!(fmt, "RunOnce(<running>)"),
            }
        }
    }
}

unsafe fn impossible() -> ! {
    enum Void {}
    match *(1 as *const Void) {}
}
