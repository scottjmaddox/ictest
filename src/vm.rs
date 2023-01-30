use rand::seq::SliceRandom;
use rand::thread_rng;
use std::collections::HashSet;
use std::mem::{align_of, size_of};
use std::ptr;

/// A tagged value or pointer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(C, align(8))]
struct Tagged(*mut ());
const _: () = assert!(size_of::<Tagged>() == 8);
const _: () = assert!(align_of::<Tagged>() == 8);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum Tag {
    /// An unused variable.
    /// This tag should only be used by `Lam::x`, `Dup::a`, or `Dup::b`.
    UnusedVar = 1,
    /// A pointer to a field inside of a `Lam`, `App`, `Sup`, or `Dup` node,
    /// corresponding to a variable use.
    /// This tag should only be used by `Lam::x`, `Dup::a`, or `Dup::b`.
    VarUsePtr = 2,
    /// An unbound variable.
    UnboundVar = 3,
    /// A pointer to a `Lam` node.
    LamPtr = 4,
    /// A pointer to an `App` node.
    AppPtr = 5,
    /// A pointer to a `Sup` node.
    SupPtr = 6,
    /// A pointer to a `Dup` node.
    DupPtr = 7,
}
impl Tag {
    const MASK: u64 = 0b111;
}

impl Tagged {
    #[inline(always)]
    fn new(ptr: *mut (), tag: Tag) -> Self {
        const _: () = assert!(size_of::<*mut ()>() == size_of::<u64>());
        let value = ptr as u64 | tag as u64;
        let tagged = Tagged(value as *mut ());
        debug_assert_eq!(tagged.tag(), tag);
        debug_assert_eq!(tagged.ptr(), ptr);
        tagged
    }

    #[inline(always)]
    fn new_unused_var() -> Self {
        Tagged::new(ptr::null_mut(), Tag::UnusedVar)
    }

    #[inline(always)]
    fn new_unbound_var() -> Self {
        Tagged::new(ptr::null_mut(), Tag::UnboundVar)
    }

    #[inline(always)]
    fn tag(self) -> Tag {
        let value = (self.0 as u64 & Tag::MASK) as u8;
        debug_assert_ne!(value, 0);
        unsafe { std::mem::transmute(value) }
    }

    #[inline(always)]
    fn ptr(self) -> *mut () {
        (self.0 as u64 & !Tag::MASK) as *mut ()
    }

    #[inline(always)]
    unsafe fn read_var_use(self) -> Tagged {
        if self.tag() == Tag::UnusedVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
            Tagged::new_unbound_var()
        } else {
            debug_assert_ne!(self.ptr(), ptr::null_mut());
            debug_assert_eq!(self.tag(), Tag::VarUsePtr);
            let ptr = self.ptr() as *const Tagged;
            ptr.read()
        }
    }

    #[inline(always)]
    unsafe fn read_lam(self) -> Lam {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), Tag::LamPtr);
        let ptr = self.ptr() as *const Lam;
        ptr.read()
    }

    #[inline(always)]
    unsafe fn read_app(self) -> App {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), Tag::AppPtr);
        let ptr = self.ptr() as *const App;
        ptr.read()
    }

    #[inline(always)]
    unsafe fn read_sup(self) -> Sup {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), Tag::SupPtr);
        let ptr = self.ptr() as *const Sup;
        ptr.read()
    }

    #[inline(always)]
    unsafe fn read_dup(self) -> Dup {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), Tag::DupPtr);
        let ptr = self.ptr() as *const Dup;
        ptr.read()
    }

    #[inline(always)]
    unsafe fn maybe_write_var(self, val: Tagged) {
        if self.tag() == Tag::UnusedVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
        } else {
            debug_assert_ne!(self.ptr(), ptr::null_mut());
            debug_assert_eq!(self.tag(), Tag::VarUsePtr);
            let ptr = self.ptr() as *mut Tagged;
            ptr.write(val)
        }
    }

    #[inline(always)]
    unsafe fn maybe_write_lam(self, lam: Lam) {
        if self.tag() == Tag::UnboundVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
        } else {
            debug_assert_ne!(self.ptr(), ptr::null_mut());
            debug_assert_eq!(self.tag(), Tag::LamPtr);
            let ptr = self.ptr() as *mut Lam;
            ptr.write(lam)
        }
    }

    #[inline(always)]
    unsafe fn maybe_write_app(self, app: App) {
        if self.tag() == Tag::UnboundVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
        } else {
            debug_assert_ne!(self.ptr(), ptr::null_mut());
            debug_assert_eq!(self.tag(), Tag::AppPtr);
            let ptr = self.ptr() as *mut App;
            ptr.write(app)
        }
    }

    #[inline(always)]
    unsafe fn maybe_write_sup(self, sup: Sup) {
        if self.tag() == Tag::UnboundVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
        } else {
            debug_assert_ne!(self.ptr(), ptr::null_mut());
            debug_assert_eq!(self.tag(), Tag::SupPtr);
            let ptr = self.ptr() as *mut Sup;
            ptr.write(sup)
        }
    }

    #[inline(always)]
    unsafe fn maybe_write_dup(self, dup: Dup) {
        if self.tag() == Tag::UnboundVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
        } else {
            debug_assert_ne!(self.ptr(), ptr::null_mut());
            debug_assert_eq!(self.tag(), Tag::DupPtr);
            let ptr = self.ptr() as *mut Dup;
            ptr.write(dup)
        }
    }

    #[inline(always)]
    unsafe fn lam_e_var_use_ptr(self) -> Tagged {
        if self.tag() == Tag::UnusedVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
            Tagged::new_unused_var()
        } else {
            debug_assert_ne!(self.ptr(), ptr::null_mut());
            debug_assert_eq!(self.tag(), Tag::LamPtr);
            let lam_raw_ptr = self.ptr() as *mut Lam;
            let ptr = &mut (*lam_raw_ptr).e as *mut _ as *mut ();
            Tagged::new(ptr, Tag::VarUsePtr)
        }
    }

    #[inline(always)]
    unsafe fn app_e2_var_use_ptr(self) -> Tagged {
        if self.tag() == Tag::UnusedVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
            Tagged::new_unused_var()
        } else {
            debug_assert_ne!(self.ptr(), ptr::null_mut());
            debug_assert_eq!(self.tag(), Tag::AppPtr);
            let app_raw_ptr = self.ptr() as *mut App;
            let ptr = &mut (*app_raw_ptr).e2 as *mut _ as *mut ();
            Tagged::new(ptr, Tag::VarUsePtr)
        }
    }

    #[inline(always)]
    unsafe fn sup_e1_var_use_ptr(self) -> Tagged {
        if self.tag() == Tag::UnusedVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
            Tagged::new_unused_var()
        } else {
            debug_assert_ne!(self.ptr(), ptr::null_mut());
            debug_assert_eq!(self.tag(), Tag::SupPtr);
            let sup_raw_ptr = self.ptr() as *mut Sup;
            let ptr = &mut (*sup_raw_ptr).e1 as *mut _ as *mut ();
            Tagged::new(ptr, Tag::VarUsePtr)
        }
    }

    #[inline(always)]
    unsafe fn sup_e2_var_use_ptr(self) -> Tagged {
        if self.tag() == Tag::UnusedVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
            Tagged::new_unused_var()
        } else {
            debug_assert_ne!(self.ptr(), ptr::null_mut());
            debug_assert_eq!(self.tag(), Tag::SupPtr);
            let sup_raw_ptr = self.ptr() as *mut Sup;
            let ptr = &mut (*sup_raw_ptr).e2 as *mut _ as *mut ();
            Tagged::new(ptr, Tag::VarUsePtr)
        }
    }

    #[inline(always)]
    unsafe fn dealloc_lam(self) {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), Tag::LamPtr);
        let ptr = self.ptr() as *mut u8;
        unsafe {
            std::alloc::dealloc(ptr, std::alloc::Layout::new::<Lam>());
        }
    }

    #[inline(always)]
    unsafe fn dealloc_app(self) {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), Tag::AppPtr);
        let ptr = self.ptr() as *mut u8;
        unsafe {
            std::alloc::dealloc(ptr, std::alloc::Layout::new::<App>());
        }
    }

    #[inline(always)]
    unsafe fn dealloc_sup(self) {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), Tag::SupPtr);
        let ptr = self.ptr() as *mut u8;
        unsafe {
            std::alloc::dealloc(ptr, std::alloc::Layout::new::<Sup>());
        }
    }

    #[inline(always)]
    unsafe fn dealloc_dup(self) {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), Tag::DupPtr);
        let ptr = self.ptr() as *mut u8;
        unsafe {
            std::alloc::dealloc(ptr, std::alloc::Layout::new::<Dup>());
        }
    }
}

/// A lambda node, e.g. `(λx e)`.
#[derive(Debug, Clone, Copy)]
#[repr(C, align(8))]
struct Lam {
    x: Tagged,
    e: Tagged,
}
const _: () = assert!(size_of::<Lam>() == 8 * 2);
const _: () = assert!(align_of::<Lam>() == 8);

/// An application node, e.g. `(e1 e2)`.
#[derive(Debug, Clone, Copy)]
#[repr(C, align(8))]
struct App {
    e1: Tagged,
    e2: Tagged,
}
const _: () = assert!(size_of::<App>() == 8 * 2);
const _: () = assert!(align_of::<App>() == 8);

/// A superposition node, e.g. `#l{e1 e2}`.
#[derive(Debug, Clone, Copy)]
#[repr(C, align(8))]
struct Sup {
    l: u64,
    e1: Tagged,
    e2: Tagged,
}
const _: () = assert!(size_of::<Sup>() == 8 * 3);
const _: () = assert!(align_of::<Sup>() == 8);

/// A duplication node, e.g. `dup #l{a b} = e;`
#[derive(Debug, Clone, Copy)]
#[repr(C, align(8))]
struct Dup {
    l: u64,
    a: Tagged,
    b: Tagged,
    e: Tagged,
}
const _: () = assert!(size_of::<Dup>() == 8 * 4);
const _: () = assert!(align_of::<Dup>() == 8);

impl Lam {
    unsafe fn alloc() -> Tagged {
        let ptr = std::alloc::alloc(std::alloc::Layout::new::<Self>()) as *mut ();
        Tagged::new(ptr, Tag::LamPtr)
    }
}

impl App {
    unsafe fn alloc() -> Tagged {
        let ptr = std::alloc::alloc(std::alloc::Layout::new::<Self>()) as *mut ();
        Tagged::new(ptr, Tag::AppPtr)
    }
}

impl Sup {
    unsafe fn alloc() -> Tagged {
        let ptr = std::alloc::alloc(std::alloc::Layout::new::<Self>()) as *mut ();
        Tagged::new(ptr, Tag::SupPtr)
    }
}

impl Dup {
    unsafe fn alloc() -> Tagged {
        let ptr = std::alloc::alloc(std::alloc::Layout::new::<Self>()) as *mut ();
        Tagged::new(ptr, Tag::DupPtr)
    }
}

unsafe fn naive_random_order_reduce(root_ptr_ptr: *mut Tagged) {
    loop {
        let redexes = collect_redexes(root_ptr_ptr);
        if redexes.is_empty() {
            return;
        }
        // select a random redex
        let redex = redexes.choose(&mut rand::thread_rng()).copied().unwrap();
    }
}

unsafe fn collect_redexes(root_ptr_ptr: *mut Tagged) -> Vec<*mut Tagged> {
    let mut visited = HashSet::new();
    let mut redexes = Vec::new();
    let mut stack = vec![root_ptr_ptr];
    while let Some(ptr_ptr) = stack.pop() {
        if visited.contains(&ptr_ptr) {
            continue;
        }
        visited.insert(ptr_ptr);
        let ptr = *ptr_ptr;
        match ptr.tag() {
            Tag::UnusedVar => {}
            Tag::VarUsePtr => {
                stack.push(ptr.ptr() as *const _ as *mut Tagged);
            }
            Tag::UnboundVar => {}
            Tag::LamPtr => {
                let lam = ptr.read_lam();
                stack.push(&lam.x as *const _ as *mut Tagged);
                stack.push(&lam.e as *const _ as *mut Tagged);
            }
            Tag::AppPtr => {
                let app = ptr.read_app();
                match app.e1.tag() {
                    Tag::LamPtr => redexes.push(ptr_ptr),
                    Tag::SupPtr => redexes.push(ptr_ptr),
                    _ => {}
                }
                stack.push(&app.e1 as *const _ as *mut Tagged);
                stack.push(&app.e2 as *const _ as *mut Tagged);
            }
            Tag::SupPtr => {
                let sup = ptr.read_sup();
                stack.push(&sup.e1 as *const _ as *mut Tagged);
                stack.push(&sup.e2 as *const _ as *mut Tagged);
            }
            Tag::DupPtr => {
                let dup = ptr.read_dup();
                match dup.e.tag() {
                    Tag::LamPtr => redexes.push(ptr_ptr),
                    Tag::SupPtr => redexes.push(ptr_ptr),
                    _ => {}
                }
                stack.push(&dup.a as *const _ as *mut Tagged);
                stack.push(&dup.b as *const _ as *mut Tagged);
                stack.push(&dup.e as *const _ as *mut Tagged);
            }
        }
    }
    redexes
}

unsafe fn reduce_redex(ptr_ptr: *mut Tagged) {
    let ptr = *ptr_ptr;
    match ptr.tag() {
        Tag::AppPtr => {
            let app = ptr.read_app();
            match app.e1.tag() {
                Tag::LamPtr => {
                    *ptr_ptr = app_lam_rule(ptr, app, app.e1);
                }
                Tag::SupPtr => {
                    *ptr_ptr = app_sup_rule(ptr, app, app.e1);
                }
                _ => unreachable!(),
            }
        }
        Tag::DupPtr => {
            let dup = ptr.read_dup();
            match dup.e.tag() {
                Tag::LamPtr => dup_lam_rule(ptr, dup, dup.e),
                Tag::SupPtr => dup_sup_rule(ptr, dup, dup.e),
                _ => unreachable!(),
            }
        }
        _ => unreachable!(),
    }
}

unsafe fn app_lam_rule(app_ptr: Tagged, app: App, lam_ptr: Tagged) -> Tagged {
    // (λx e) e2
    // ---------- AppLam
    // x <- e2
    // e

    app_ptr.dealloc_app();
    let lam = lam_ptr.read_lam();
    lam_ptr.dealloc_lam();

    // x <- e2
    debug_assert_eq!(lam.x.read_var_use(), lam_ptr);
    lam.x.maybe_write_var(app.e2);
    // e
    lam.e
}

unsafe fn app_sup_rule(app_ptr: Tagged, app: App, sup_ptr: Tagged) -> Tagged {
    // #l{e1 e2} e3
    // ----------------- AppSup
    // dup #l{a b} = e3
    // #l{(e1 a) (e2 b)}

    let app_sup_e3 = app;
    let sup_e1_e2_ptr = sup_ptr;

    app_ptr.dealloc_app();
    let sup_e1_e2 = sup_e1_e2_ptr.read_sup();
    sup_e1_e2_ptr.dealloc_sup();

    let dup_a_b_ptr = Dup::alloc();
    let app_e1_a_ptr = App::alloc();
    let app_e2_b_ptr = App::alloc();
    let sup_app_app_ptr = Sup::alloc();

    // dup #l{a b} = e3
    dup_a_b_ptr.maybe_write_dup(Dup {
        l: sup_e1_e2.l,
        a: app_e1_a_ptr.app_e2_var_use_ptr(),
        b: app_e2_b_ptr.app_e2_var_use_ptr(),
        e: app_sup_e3.e2,
    });

    // #l{(e1 a) (e2 b)}
    app_e1_a_ptr.maybe_write_app(App {
        e1: sup_e1_e2.e1,
        e2: dup_a_b_ptr,
    });
    app_e2_b_ptr.maybe_write_app(App {
        e1: sup_e1_e2.e2,
        e2: dup_a_b_ptr,
    });
    sup_app_app_ptr.maybe_write_sup(Sup {
        l: sup_e1_e2.l,
        e1: app_e1_a_ptr,
        e2: app_e2_b_ptr,
    });
    sup_app_app_ptr
}

unsafe fn dup_lam_rule(dup_ptr: Tagged, dup: Dup, lam_ptr: Tagged) {
    // dup #l{a b} = (λx e)
    // ------------------ DupLam
    // a <- (λx1 c)
    // b <- (λx2 d)
    // x <- #l{x1,x2}
    // dup #l{c d} = e

    let dup_a_b_ptr = dup_ptr;
    let dup_a_b = dup;
    let lam_x_e_ptr = lam_ptr;

    dup_ptr.dealloc_dup();
    let lam_x_e = lam_ptr.read_lam();
    lam_ptr.dealloc_lam();

    let lam_x1_c_ptr = if dup_a_b.a.tag() == Tag::UnusedVar {
        Tagged::new_unbound_var()
    } else {
        Lam::alloc()
    };
    let lam_x2_d_ptr = if dup_a_b.b.tag() == Tag::UnusedVar {
        Tagged::new_unbound_var()
    } else {
        Lam::alloc()
    };
    let sup_x1_x2_ptr = if lam_x_e.x.tag() == Tag::UnusedVar {
        Tagged::new_unbound_var()
    } else {
        Sup::alloc()
    };
    let dup_c_d_ptr = Dup::alloc();

    // a <- (λx1 c)
    debug_assert_eq!(dup_a_b.a.read_var_use(), dup_a_b_ptr);
    dup_a_b.a.maybe_write_var(lam_x1_c_ptr);
    lam_x1_c_ptr.maybe_write_lam(Lam {
        x: sup_x1_x2_ptr.sup_e1_var_use_ptr(),
        e: dup_c_d_ptr,
    });

    // b <- (λx2 d)
    debug_assert_eq!(dup_a_b.b.read_var_use(), dup_a_b_ptr);
    dup_a_b.b.maybe_write_var(lam_x2_d_ptr);
    lam_x2_d_ptr.maybe_write_lam(Lam {
        x: sup_x1_x2_ptr.sup_e2_var_use_ptr(),
        e: dup_c_d_ptr,
    });

    // x <- #l{x1,x2}
    debug_assert_eq!(lam_x_e.x.read_var_use(), dup_a_b.e);
    lam_x_e.x.maybe_write_var(sup_x1_x2_ptr);
    sup_x1_x2_ptr.maybe_write_sup(Sup {
        l: dup_a_b.l,
        e1: lam_x1_c_ptr,
        e2: lam_x2_d_ptr,
    });

    // dup #l{c d} = e
    dup_c_d_ptr.maybe_write_dup(Dup {
        l: dup_a_b.l,
        a: lam_x1_c_ptr.lam_e_var_use_ptr(),
        b: lam_x2_d_ptr.lam_e_var_use_ptr(),
        e: lam_x_e.e,
    });
}

unsafe fn dup_sup_rule(dup_ptr: Tagged, dup: Dup, sup_ptr: Tagged) {
    // dup #l{a b} = #l{e1 e2}
    // --------------------- DupSupSame
    // a <- e1
    // b <- e2

    // dup #l{a b} = #m{e1 e2}
    // --------------------- DupSupDiff
    // a <- #m{a1 a2}
    // b <- #m{b1 b2}
    // dup #l{a1 b1} = e1
    // dup #l{a2 b2} = e2

    let dup_a_b_ptr = dup_ptr;
    let dup_a_b = dup;
    let sup_e1_e2_ptr = sup_ptr;

    dup_ptr.dealloc_dup();
    let sup_e1_e2 = sup_e1_e2_ptr.read_sup();
    sup_e1_e2_ptr.dealloc_sup();

    if dup_a_b.l == sup_e1_e2.l {
        // a <- e1
        debug_assert_eq!(dup_a_b.a.read_var_use(), dup_a_b_ptr);
        dup_a_b.a.maybe_write_var(sup_e1_e2.e1);
        // b <- e2
        debug_assert_eq!(dup_a_b.a.read_var_use(), dup_a_b_ptr);
        dup_a_b.b.maybe_write_var(sup_e1_e2.e2);
    } else {
        let l = dup_a_b.l;
        let m = sup_e1_e2.l;

        let sup_a1_a2_ptr = if dup_a_b.a.tag() == Tag::UnusedVar {
            Tagged::new_unbound_var()
        } else {
            Sup::alloc()
        };
        let sup_b1_b2_ptr = if dup_a_b.b.tag() == Tag::UnusedVar {
            Tagged::new_unbound_var()
        } else {
            Sup::alloc()
        };
        let dup_a1_b1_ptr = Dup::alloc();
        let dup_a2_b2_ptr = Dup::alloc();

        // a <- #m{a1 a2}
        debug_assert_eq!(dup_a_b.a.read_var_use(), dup_a_b_ptr);
        dup_a_b.a.maybe_write_var(sup_a1_a2_ptr);
        sup_a1_a2_ptr.maybe_write_sup(Sup {
            l: m,
            e1: dup_a1_b1_ptr,
            e2: dup_a2_b2_ptr,
        });

        // b <- #m{b1 b2}
        debug_assert_eq!(dup_a_b.a.read_var_use(), dup_a_b_ptr);
        dup_a_b.b.maybe_write_var(sup_b1_b2_ptr);
        sup_b1_b2_ptr.maybe_write_sup(Sup {
            l: m,
            e1: dup_a1_b1_ptr,
            e2: dup_a2_b2_ptr,
        });
        // dup #l{a1 b1} = e1
        dup_a1_b1_ptr.maybe_write_dup(Dup {
            l,
            a: sup_a1_a2_ptr.sup_e1_var_use_ptr(),
            b: sup_b1_b2_ptr.sup_e1_var_use_ptr(),
            e: sup_e1_e2.e1,
        });
        // dup #l{a2 b2} = e2
        dup_a2_b2_ptr.maybe_write_dup(Dup {
            l,
            a: sup_a1_a2_ptr.sup_e2_var_use_ptr(),
            b: sup_b1_b2_ptr.sup_e2_var_use_ptr(),
            e: sup_e1_e2.e2,
        });
    }
}

/// An owned term graph.
pub struct TermGraph(Tagged);

impl Drop for TermGraph {
    fn drop(&mut self) {
        todo!()
    }
}

impl TermGraph {
    pub fn naive_random_order_reduce(&mut self) {
        unsafe {
            naive_random_order_reduce(&mut self.0);
        }
    }
}
