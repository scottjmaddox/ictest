use rand::seq::SliceRandom;
use memoffset::offset_of;
use std::collections::{HashMap, HashSet, VecDeque};
use std::mem::{align_of, size_of};
use std::{fmt, ptr};

use crate::intern::IStr;
use crate::syntax::Term;

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
    unsafe fn lam_x_raw_ptr(self) -> *mut Tagged {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), Tag::LamPtr);
        let lam_raw_ptr = self.ptr() as *mut Lam;
        lam_raw_ptr.wrapping_offset(offset_of!(Lam, x) as isize) as *mut Tagged
    }

    #[inline(always)]
    unsafe fn lam_e_raw_ptr(self) -> *mut Tagged {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), Tag::LamPtr);
        let lam_raw_ptr = self.ptr() as *mut Lam;
        lam_raw_ptr.wrapping_offset(offset_of!(Lam, e) as isize) as *mut Tagged
    }

    #[inline(always)]
    unsafe fn app_e1_raw_ptr(self) -> *mut Tagged {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), Tag::AppPtr);
        let app_raw_ptr = self.ptr() as *mut App;
        app_raw_ptr.wrapping_offset(offset_of!(App, e1) as isize) as *mut Tagged
    }

    #[inline(always)]
    unsafe fn app_e2_raw_ptr(self) -> *mut Tagged {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), Tag::AppPtr);
        let app_raw_ptr = self.ptr() as *mut App;
        app_raw_ptr.wrapping_offset(offset_of!(App, e2) as isize) as *mut Tagged
    }

    #[inline(always)]
    unsafe fn sup_l_raw_ptr(self) -> *mut u64 {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), Tag::SupPtr);
        let sup_raw_ptr = self.ptr() as *mut Sup;
        sup_raw_ptr.wrapping_offset(offset_of!(Sup, l) as isize) as *mut u64
    }

    #[inline(always)]
    unsafe fn sup_e1_raw_ptr(self) -> *mut Tagged {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), Tag::SupPtr);
        let sup_raw_ptr = self.ptr() as *mut Sup;
        sup_raw_ptr.wrapping_offset(offset_of!(Sup, e1) as isize) as *mut Tagged
    }

    #[inline(always)]
    unsafe fn sup_e2_raw_ptr(self) -> *mut Tagged {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), Tag::SupPtr);
        let sup_raw_ptr = self.ptr() as *mut Sup;
        sup_raw_ptr.wrapping_offset(offset_of!(Sup, e2) as isize) as *mut Tagged
    }

    #[inline(always)]
    unsafe fn dup_l_raw_ptr(self) -> *mut u64 {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), Tag::DupPtr);
        let dup_raw_ptr = self.ptr() as *mut Dup;
        dup_raw_ptr.wrapping_offset(offset_of!(Dup, l) as isize) as *mut u64
    }

    #[inline(always)]
    unsafe fn dup_a_raw_ptr(self) -> *mut Tagged {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), Tag::DupPtr);
        let dup_raw_ptr = self.ptr() as *mut Dup;
        dup_raw_ptr.wrapping_offset(offset_of!(Dup, a) as isize) as *mut Tagged
    }

    #[inline(always)]
    unsafe fn dup_b_raw_ptr(self) -> *mut Tagged {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), Tag::DupPtr);
        let dup_raw_ptr = self.ptr() as *mut Dup;
        dup_raw_ptr.wrapping_offset(offset_of!(Dup, b) as isize) as *mut Tagged
    }

    #[inline(always)]
    unsafe fn dup_e_raw_ptr(self) -> *mut Tagged {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), Tag::DupPtr);
        let dup_raw_ptr = self.ptr() as *mut Dup;
        dup_raw_ptr.wrapping_offset(offset_of!(Dup, e) as isize) as *mut Tagged
    }

    #[inline(always)]
    unsafe fn lam_e_var_use_ptr(self) -> Tagged {
        if self.tag() == Tag::UnboundVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
            Tagged::new_unused_var()
        } else {
            Tagged::new(self.lam_e_raw_ptr() as *mut (), Tag::VarUsePtr)
        }
    }

    #[inline(always)]
    unsafe fn app_e1_var_use_ptr(self) -> Tagged {
        if self.tag() == Tag::UnboundVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
            Tagged::new_unused_var()
        } else {
            Tagged::new(self.app_e1_raw_ptr() as *mut (), Tag::VarUsePtr)
        }
    }

    #[inline(always)]
    unsafe fn app_e2_var_use_ptr(self) -> Tagged {
        if self.tag() == Tag::UnboundVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
            Tagged::new_unused_var()
        } else {
            Tagged::new(self.app_e2_raw_ptr() as *mut (), Tag::VarUsePtr)
        }
    }

    #[inline(always)]
    unsafe fn sup_e1_var_use_ptr(self) -> Tagged {
        if self.tag() == Tag::UnboundVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
            Tagged::new_unused_var()
        } else {
            Tagged::new(self.sup_e1_raw_ptr() as *mut (), Tag::VarUsePtr)
        }
    }

    #[inline(always)]
    unsafe fn sup_e2_var_use_ptr(self) -> Tagged {
        if self.tag() == Tag::UnboundVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
            Tagged::new_unused_var()
        } else {
            Tagged::new(self.sup_e2_raw_ptr() as *mut (), Tag::VarUsePtr)
        }
    }

    #[inline(always)]
    unsafe fn dup_e_var_use_ptr(self) -> Tagged {
        if self.tag() == Tag::UnboundVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
            Tagged::new_unused_var()
        } else {
            Tagged::new(self.dup_e_raw_ptr() as *mut (), Tag::VarUsePtr)
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

    #[inline(always)]
    unsafe fn dealloc_any(self) {
        match self.tag() {
            Tag::LamPtr => self.dealloc_lam(),
            Tag::AppPtr => self.dealloc_app(),
            Tag::SupPtr => self.dealloc_sup(),
            Tag::DupPtr => self.dealloc_dup(),
            _ => panic!(),
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
        reduce_redex(redex);
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
        let ptr = ptr_ptr.read();
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
    let ptr = ptr_ptr.read();
    match ptr.tag() {
        Tag::AppPtr => {
            let app_ptr = ptr;
            let app_e1 = app_ptr.app_e1_raw_ptr().read();
            match app_e1.tag() {
                Tag::LamPtr => app_lam_rule(ptr_ptr, app_ptr, app_e1),
                Tag::SupPtr => app_sup_rule(ptr_ptr, app_ptr, app_e1),
                _ => unreachable!(),
            }
        }
        Tag::DupPtr => {
            let dup_ptr = ptr;
            let dup_e = dup_ptr.dup_e_raw_ptr().read();
            match dup_e.tag() {
                Tag::LamPtr => dup_lam_rule(dup_ptr, dup_e),
                Tag::SupPtr => dup_sup_rule(dup_ptr, dup_e),
                _ => unreachable!(),
            }
        }
        _ => unreachable!(),
    }
}

unsafe fn app_lam_rule(ptr_ptr: *mut Tagged, app_ptr: Tagged, lam_ptr: Tagged) {
    // (λx e) e2
    // ---------- AppLam
    // x <- e2
    // e

    let lam_x = lam_ptr.lam_x_raw_ptr().read();

    // x <- e2
    debug_assert_eq!(lam_x.read_var_use(), lam_ptr);
    lam_x.maybe_write_var(app_ptr.app_e2_raw_ptr().read());
    // e
    ptr_ptr.write(lam_ptr.lam_e_raw_ptr().read());

    // deallocate unreachable nodes
    app_ptr.dealloc_app();
    lam_ptr.dealloc_lam();
}

unsafe fn app_sup_rule(ptr_ptr: *mut Tagged, app_ptr: Tagged, sup_ptr: Tagged) {
    // #l{e1 e2} e3
    // ----------------- AppSup
    // dup #l{a b} = e3
    // #l{(e1 a) (e2 b)}

    let app_sup_e3_ptr = app_ptr;
    let sup_e1_e2_ptr = sup_ptr;

    let l = sup_e1_e2_ptr.sup_l_raw_ptr().read();

    let dup_a_b_ptr = Dup::alloc();
    let app_e1_a_ptr = App::alloc();
    let app_e2_b_ptr = App::alloc();
    let sup_app_app_ptr = Sup::alloc();

    // dup #l{a b} = e3
    dup_a_b_ptr.maybe_write_dup(Dup {
        l,
        a: app_e1_a_ptr.app_e2_var_use_ptr(),
        b: app_e2_b_ptr.app_e2_var_use_ptr(),
        e: app_sup_e3_ptr.app_e2_raw_ptr().read(),
    });

    // #l{(e1 a) (e2 b)}
    app_e1_a_ptr.maybe_write_app(App {
        e1: sup_e1_e2_ptr.sup_e1_raw_ptr().read(),
        e2: dup_a_b_ptr,
    });
    app_e2_b_ptr.maybe_write_app(App {
        e1: sup_e1_e2_ptr.sup_e2_raw_ptr().read(),
        e2: dup_a_b_ptr,
    });
    sup_app_app_ptr.maybe_write_sup(Sup {
        l,
        e1: app_e1_a_ptr,
        e2: app_e2_b_ptr,
    });
    ptr_ptr.write(sup_app_app_ptr);

    // deallocate unreachable nodes
    app_sup_e3_ptr.dealloc_app();
    sup_e1_e2_ptr.dealloc_sup();
}

unsafe fn dup_lam_rule(dup_ptr: Tagged, lam_ptr: Tagged) {
    // dup #l{a b} = (λx e)
    // ------------------ DupLam
    // a <- (λx1 c)
    // b <- (λx2 d)
    // x <- #l{x1,x2}
    // dup #l{c d} = e

    let dup_a_b_ptr = dup_ptr;
    let lam_x_e_ptr = lam_ptr;

    let l = dup_a_b_ptr.dup_l_raw_ptr().read();
    let dup_a_b_a = dup_a_b_ptr.dup_a_raw_ptr().read();
    let dup_a_b_b = dup_a_b_ptr.dup_b_raw_ptr().read();
    let lam_x_e_x = lam_x_e_ptr.lam_x_raw_ptr().read();

    let lam_x1_c_ptr = if dup_a_b_a.tag() == Tag::UnusedVar {
        Tagged::new_unbound_var()
    } else {
        Lam::alloc()
    };
    let lam_x2_d_ptr = if dup_a_b_b.tag() == Tag::UnusedVar {
        Tagged::new_unbound_var()
    } else {
        Lam::alloc()
    };
    let sup_x1_x2_ptr = if lam_x_e_x.tag() == Tag::UnusedVar {
        Tagged::new_unbound_var()
    } else {
        Sup::alloc()
    };
    let dup_c_d_ptr = Dup::alloc();

    // a <- (λx1 c)
    debug_assert_eq!(dup_a_b_a.read_var_use(), dup_a_b_ptr);
    dup_a_b_a.maybe_write_var(lam_x1_c_ptr);
    lam_x1_c_ptr.maybe_write_lam(Lam {
        x: sup_x1_x2_ptr.sup_e1_var_use_ptr(),
        e: dup_c_d_ptr,
    });

    // b <- (λx2 d)
    debug_assert_eq!(dup_a_b_b.read_var_use(), dup_a_b_ptr);
    dup_a_b_b.maybe_write_var(lam_x2_d_ptr);
    lam_x2_d_ptr.maybe_write_lam(Lam {
        x: sup_x1_x2_ptr.sup_e2_var_use_ptr(),
        e: dup_c_d_ptr,
    });

    // x <- #l{x1,x2}
    debug_assert_eq!(lam_x_e_x.read_var_use(), dup_a_b_ptr.dup_e_raw_ptr().read());
    lam_x_e_x.maybe_write_var(sup_x1_x2_ptr);
    sup_x1_x2_ptr.maybe_write_sup(Sup {
        l,
        e1: lam_x1_c_ptr,
        e2: lam_x2_d_ptr,
    });

    // dup #l{c d} = e
    dup_c_d_ptr.maybe_write_dup(Dup {
        l,
        a: lam_x1_c_ptr.lam_e_var_use_ptr(),
        b: lam_x2_d_ptr.lam_e_var_use_ptr(),
        e: lam_x_e_ptr.lam_e_raw_ptr().read(),
    });

    // deallocate unreachable nodes
    dup_a_b_ptr.dealloc_dup();
    lam_x_e_ptr.dealloc_lam();
}

unsafe fn dup_sup_rule(dup_ptr: Tagged, sup_ptr: Tagged) {
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
    let sup_e1_e2_ptr = sup_ptr;

    let l = dup_a_b_ptr.dup_l_raw_ptr().read();
    let m = sup_e1_e2_ptr.sup_l_raw_ptr().read();
    let dup_a_b_a = dup_a_b_ptr.dup_a_raw_ptr().read();
    let dup_a_b_b = dup_a_b_ptr.dup_b_raw_ptr().read();

    // let sup_e1_e2 = sup_e1_e2_ptr.read_sup();

    if l == m {
        // a <- e1
        debug_assert_eq!(dup_a_b_a.read_var_use(), dup_a_b_ptr);
        dup_a_b_a.maybe_write_var(sup_e1_e2_ptr.sup_e1_raw_ptr().read());
        // b <- e2
        debug_assert_eq!(dup_a_b_b.read_var_use(), dup_a_b_ptr);
        dup_a_b_b.maybe_write_var(sup_e1_e2_ptr.sup_e2_raw_ptr().read());
    } else {
        let sup_a1_a2_ptr = if dup_a_b_a.tag() == Tag::UnusedVar {
            Tagged::new_unbound_var()
        } else {
            Sup::alloc()
        };
        let sup_b1_b2_ptr = if dup_a_b_b.tag() == Tag::UnusedVar {
            Tagged::new_unbound_var()
        } else {
            Sup::alloc()
        };
        let dup_a1_b1_ptr = Dup::alloc();
        let dup_a2_b2_ptr = Dup::alloc();

        // a <- #m{a1 a2}
        debug_assert_eq!(dup_a_b_a.read_var_use(), dup_a_b_ptr);
        dup_a_b_a.maybe_write_var(sup_a1_a2_ptr);
        sup_a1_a2_ptr.maybe_write_sup(Sup {
            l: m,
            e1: dup_a1_b1_ptr,
            e2: dup_a2_b2_ptr,
        });

        // b <- #m{b1 b2}
        debug_assert_eq!(dup_a_b_b.read_var_use(), dup_a_b_ptr);
        dup_a_b_b.maybe_write_var(sup_b1_b2_ptr);
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
            e: sup_e1_e2_ptr.sup_e1_raw_ptr().read(),
        });
        // dup #l{a2 b2} = e2
        dup_a2_b2_ptr.maybe_write_dup(Dup {
            l,
            a: sup_a1_a2_ptr.sup_e2_var_use_ptr(),
            b: sup_b1_b2_ptr.sup_e2_var_use_ptr(),
            e: sup_e1_e2_ptr.sup_e2_raw_ptr().read(),
        });
    }

    // deallocate unreachable nodes
    dup_a_b_ptr.dealloc_dup();
    sup_e1_e2_ptr.dealloc_sup();
}

unsafe fn visit_nodes<F: FnMut(Tagged)>(ptr: Tagged, mut f: F) {
    let mut visited = HashSet::new();
    let mut queue = VecDeque::new();
    queue.push_back(ptr);
    while let Some(ptr) = queue.pop_front() {
        if visited.contains(&ptr) {
            continue;
        }
        visited.insert(ptr);
        match ptr.tag() {
            Tag::UnusedVar => {}
            Tag::VarUsePtr => unreachable!(),
            Tag::UnboundVar => {}
            Tag::LamPtr => {
                let lam = ptr.read_lam();
                if lam.x.tag() == Tag::VarUsePtr {
                    queue.push_back(lam.x.read_var_use());
                }
                queue.push_back(lam.e);
                f(ptr);
            }
            Tag::AppPtr => {
                let app = ptr.read_app();
                queue.push_back(app.e1);
                queue.push_back(app.e2);
                f(ptr);
            }
            Tag::SupPtr => {
                let sup = ptr.read_sup();
                queue.push_back(sup.e1);
                queue.push_back(sup.e2);
                f(ptr);
            }
            Tag::DupPtr => {
                let dup = ptr.read_dup();
                if dup.a.tag() == Tag::VarUsePtr {
                    queue.push_back(dup.a.read_var_use());
                }
                if dup.b.tag() == Tag::VarUsePtr {
                    queue.push_back(dup.b.read_var_use());
                }
                queue.push_back(dup.e);
                f(ptr);
            }
        }
    }
}

/// An owned term graph.
pub struct TermGraph(Tagged);

impl Drop for TermGraph {
    fn drop(&mut self) {
        let mut nodes = Vec::new();
        unsafe {
            visit_nodes(self.0, |ptr| nodes.push(ptr));
            for node in nodes {
                node.dealloc_any();
            }
        }
    }
}

impl fmt::Debug for TermGraph {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut nodes = Vec::new();
        unsafe {
            visit_nodes(self.0, |ptr| nodes.push(ptr));
            for ptr in nodes {
                write!(f, "{:?} {:?} ", ptr.ptr(), ptr.tag())?;
                match ptr.tag() {
                    Tag::UnusedVar => {}
                    Tag::VarUsePtr => {}
                    Tag::UnboundVar => {}
                    Tag::LamPtr => {
                        let lam = ptr.read_lam();
                        write!(f, "({:?} {:?}) ", lam.x.ptr(), lam.x.tag())?;
                        write!(f, "({:?} {:?}) ", lam.e.ptr(), lam.e.tag())?;
                    }
                    Tag::AppPtr => {
                        let app = ptr.read_app();
                        write!(f, "({:?} {:?}) ", app.e1.ptr(), app.e1.tag())?;
                        write!(f, "({:?} {:?}) ", app.e2.ptr(), app.e2.tag())?;
                    }
                    Tag::SupPtr => {
                        let sup = ptr.read_sup();
                        write!(f, "{:?} ", sup.l)?;
                        write!(f, "({:?} {:?}) ", sup.e1.ptr(), sup.e1.tag())?;
                        write!(f, "({:?} {:?}) ", sup.e2.ptr(), sup.e2.tag())?;
                    }
                    Tag::DupPtr => {
                        let dup = ptr.read_dup();
                        write!(f, "{:?} ", dup.l)?;
                        write!(f, "({:?} {:?}) ", dup.a.ptr(), dup.a.tag())?;
                        write!(f, "({:?} {:?}) ", dup.b.ptr(), dup.b.tag())?;
                        write!(f, "({:?} {:?}) ", dup.e.ptr(), dup.e.tag())?;
                    }
                }
                write!(f, "\n")?;
            }
        }
        Ok(())
    }
}

impl From<&Term> for TermGraph {
    fn from(term: &Term) -> Self {
        unsafe fn recurse(
            var_binders: &mut HashMap<IStr, Vec<Tagged>>,
            var_uses: &mut HashMap<(IStr, usize), Tagged>,
            term: &Term,
        ) -> Tagged {
            // TODO: count uses, and fail if not affine
            match term {
                Term::Var(name) => {
                    if let Some(binders) = var_binders.get_mut(name) {
                        let binder = binders.last().copied().unwrap();
                        binder
                    } else {
                        Tagged::new_unbound_var()
                    }
                }
                Term::Lam(x_str, e_term) => do_lam(var_binders, var_uses, *x_str, e_term),
                Term::App(e1_term, e2_term) => {
                    let app_ptr = App::alloc();
                    let e1 = recurse(var_binders, var_uses, e1_term);
                    register_var_use(
                        var_binders,
                        var_uses,
                        e1_term,
                        e1,
                        app_ptr.app_e1_var_use_ptr(),
                    );
                    let e2 = recurse(var_binders, var_uses, e2_term);
                    register_var_use(
                        var_binders,
                        var_uses,
                        e2_term,
                        e2,
                        app_ptr.app_e2_var_use_ptr(),
                    );
                    app_ptr.maybe_write_app(App { e1, e2 });
                    app_ptr
                }
                Term::Sup(l, e1_term, e2_term) => {
                    let sup_ptr = Sup::alloc();
                    let e1 = recurse(var_binders, var_uses, e1_term);
                    register_var_use(
                        var_binders,
                        var_uses,
                        e1_term,
                        e1,
                        sup_ptr.sup_e1_var_use_ptr(),
                    );
                    let e2 = recurse(var_binders, var_uses, e2_term);
                    register_var_use(
                        var_binders,
                        var_uses,
                        e2_term,
                        e2,
                        sup_ptr.sup_e2_var_use_ptr(),
                    );
                    sup_ptr.maybe_write_sup(Sup { l: *l, e1, e2 });
                    sup_ptr
                }
                Term::Dup(l, a_str, b_str, e_term, cont_term) => {
                    let dup_ptr = Dup::alloc();
                    let a_scopes = var_binders.entry(*a_str).or_default();
                    a_scopes.push(dup_ptr);
                    let a_scope = a_scopes.len();
                    let b_scopes = var_binders.entry(*b_str).or_default();
                    b_scopes.push(dup_ptr);
                    let b_scope = b_scopes.len();
                    let e = recurse(var_binders, var_uses, e_term);
                    register_var_use(
                        var_binders,
                        var_uses,
                        e_term,
                        e,
                        dup_ptr.dup_e_var_use_ptr(),
                    );
                    let cont = recurse(var_binders, var_uses, cont_term);
                    register_var_use(
                        var_binders,
                        var_uses,
                        cont_term,
                        cont,
                        dup_ptr.dup_e_var_use_ptr(),
                    );
                    let a = var_uses
                        .get(&(*a_str, a_scope))
                        .copied()
                        .unwrap_or(Tagged::new_unused_var());
                    let b = var_uses
                        .get(&(*b_str, b_scope))
                        .copied()
                        .unwrap_or(Tagged::new_unused_var());
                    assert!(a.tag() != Tag::UnusedVar || b.tag() != Tag::UnusedVar);
                    dup_ptr.maybe_write_dup(Dup { l: *l, a, b, e });
                    cont
                }
                Term::Let(x, e1_term, e2_term) => {
                    // let x = e1 in e2 => (λx e2) e1
                    let app_ptr = App::alloc();
                    let e1 = recurse(var_binders, var_uses, e1_term);
                    register_var_use(
                        var_binders,
                        var_uses,
                        e1_term,
                        e1,
                        app_ptr.app_e2_var_use_ptr(),
                    );
                    let lam_ptr = do_lam(var_binders, var_uses, *x, e2_term);
                    app_ptr.maybe_write_app(App {
                        e1: lam_ptr,
                        e2: e1,
                    });
                    app_ptr
                }
            }
        }
        fn register_var_use(
            var_binders: &mut HashMap<IStr, Vec<Tagged>>,
            var_uses: &mut HashMap<(IStr, usize), Tagged>,
            e_term: &Term,
            e: Tagged,
            var_use_ptr: Tagged,
        ) {
            if let Term::Var(v_str) = e_term {
                if e.tag() != Tag::UnboundVar {
                    let v_scope = var_binders.entry(*v_str).or_default().len();
                    assert!(
                        !var_uses.contains_key(&(*v_str, v_scope)),
                        "non-affine usage"
                    );
                    var_uses.insert((*v_str, v_scope), var_use_ptr);
                }
            }
        }
        unsafe fn do_lam(
            var_binders: &mut HashMap<IStr, Vec<Tagged>>,
            var_uses: &mut HashMap<(IStr, usize), Tagged>,
            x_str: IStr,
            e_term: &Term,
        ) -> Tagged {
            let lam_ptr = Lam::alloc();
            let x_scopes = var_binders.entry(x_str).or_default();
            x_scopes.push(lam_ptr);
            let x_scope = x_scopes.len();
            let e = recurse(var_binders, var_uses, e_term);
            register_var_use(
                var_binders,
                var_uses,
                e_term,
                e,
                lam_ptr.lam_e_var_use_ptr(),
            );
            let x = var_uses
                .get(&(x_str, x_scope))
                .copied()
                .unwrap_or(Tagged::new_unused_var());
            lam_ptr.maybe_write_lam(Lam { x, e });
            lam_ptr
        }
        let var_binders = &mut HashMap::new();
        let var_uses = &mut HashMap::new();
        unsafe { TermGraph(recurse(var_binders, var_uses, term)) }
    }
}

impl TermGraph {
    pub fn naive_random_order_reduce(&mut self) {
        unsafe {
            naive_random_order_reduce(&mut self.0);
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_app_lam_from_term() {
        // term = ((λx. x) y)
        let term = Term::App(
            Box::new(Term::Lam("x".into(), Box::new(Term::Var("x".into())))),
            Box::new(Term::Var("y".into())),
        );
        let term_graph = TermGraph::from(&term);
        assert_eq!(term_graph.0.tag(), Tag::AppPtr);
        unsafe {
            let mut nodes = Vec::new();
            visit_nodes(term_graph.0, |ptr| nodes.push(ptr));
            assert_eq!(nodes.len(), 2);
            assert_eq!(nodes[0].tag(), Tag::AppPtr);
            assert_eq!(nodes[1].tag(), Tag::LamPtr);
            let app_ptr = nodes[0];
            let lam_ptr = nodes[1];
            let app = app_ptr.read_app();
            let lam = lam_ptr.read_lam();
            assert_eq!(app.e1, lam_ptr);
            assert_eq!(app.e2.tag(), Tag::UnboundVar);
            assert_eq!(lam.x, lam_ptr.lam_e_var_use_ptr());
            assert_eq!(lam.e, lam_ptr);
        }
    }

    #[test]
    fn test_app_sup_from_term() {
        // term = (#0{x0 x1} y)
        let term = Term::App(
            Box::new(Term::Sup(
                0,
                Box::new(Term::Var("x0".into())),
                Box::new(Term::Var("x1".into())),
            )),
            Box::new(Term::Var("y".into())),
        );
        let term_graph = TermGraph::from(&term);
        assert_eq!(term_graph.0.tag(), Tag::AppPtr);
        unsafe {
            let mut nodes = Vec::new();
            visit_nodes(term_graph.0, |ptr| nodes.push(ptr));
            assert_eq!(nodes.len(), 2);
            assert_eq!(nodes[0].tag(), Tag::AppPtr);
            assert_eq!(nodes[1].tag(), Tag::SupPtr);
            let app_ptr = nodes[0];
            let sup_ptr = nodes[1];
            let app = app_ptr.read_app();
            let sup = sup_ptr.read_sup();
            assert_eq!(app.e1, sup_ptr);
            assert_eq!(app.e2.tag(), Tag::UnboundVar);
            assert_eq!(sup.l, 0);
            assert_eq!(sup.e1.tag(), Tag::UnboundVar);
            assert_eq!(sup.e2.tag(), Tag::UnboundVar);
        }
    }

    #[test]
    fn test_app_dup_app_sup_from_term() {
        // term = ((let #0{v1 v2} = v0; #0{v1 v2}) v3)
        let term = Term::App(
            Box::new(Term::Dup(
                0,
                "v1".into(),
                "v2".into(),
                Box::new(Term::Var("v0".into())),
                Box::new(Term::Sup(
                    0,
                    Box::new(Term::Var("v1".into())),
                    Box::new(Term::Var("v2".into())),
                )),
            )),
            Box::new(Term::Var("v3".into())),
        );
        let term_graph = TermGraph::from(&term);
        assert_eq!(term_graph.0.tag(), Tag::AppPtr);
        unsafe {
            let mut nodes = Vec::new();
            visit_nodes(term_graph.0, |ptr| nodes.push(ptr));
            assert_eq!(nodes.len(), 3);
            assert_eq!(nodes[0].tag(), Tag::AppPtr);
            assert_eq!(nodes[1].tag(), Tag::SupPtr);
            assert_eq!(nodes[2].tag(), Tag::DupPtr);
            let app_ptr = nodes[0];
            let sup_ptr = nodes[1];
            let dup_ptr = nodes[2];
            let app = app_ptr.read_app();
            let sup = sup_ptr.read_sup();
            let dup = dup_ptr.read_dup();
            assert_eq!(app.e1, sup_ptr);
            assert_eq!(app.e2.tag(), Tag::UnboundVar);
            assert_eq!(sup.l, 0);
            assert_eq!(sup.e1, dup_ptr);
            assert_eq!(sup.e2, dup_ptr);
            assert_eq!(dup.l, 0);
            assert_eq!(dup.a, sup_ptr.sup_e1_var_use_ptr());
            assert_eq!(dup.b, sup_ptr.sup_e2_var_use_ptr());
            assert_eq!(dup.e, Tagged::new_unbound_var());
        }
    }

    #[test]
    fn test_dup_lam_dup_sup_from_term() {
        // term = (let #0{v1 v2} = (λv0 v0); #0{v1 v2})
        let term = Term::Dup(
            0,
            "v1".into(),
            "v2".into(),
            Box::new(Term::Lam(
                "v0".into(),
                Box::new(Term::Var("v0".into())),
            )),
            Box::new(Term::Sup(
                0,
                Box::new(Term::Var("v1".into())),
                Box::new(Term::Var("v2".into())),
            )),
        );
        let term_graph = TermGraph::from(&term);
        assert_eq!(term_graph.0.tag(), Tag::SupPtr);
        unsafe {
            let mut nodes = Vec::new();
            visit_nodes(term_graph.0, |ptr| nodes.push(ptr));
            assert_eq!(nodes.len(), 3);
            assert_eq!(nodes[0].tag(), Tag::SupPtr);
            assert_eq!(nodes[1].tag(), Tag::DupPtr);
            assert_eq!(nodes[2].tag(), Tag::LamPtr);
            let sup_ptr = nodes[0];
            let dup_ptr = nodes[1];
            let lam_ptr = nodes[2];
            let sup = sup_ptr.read_sup();
            let dup = dup_ptr.read_dup();
            let lam = lam_ptr.read_lam();
            assert_eq!(sup.l, 0);
            assert_eq!(sup.e1, dup_ptr);
            assert_eq!(sup.e2, dup_ptr);
            assert_eq!(dup.l, 0);
            assert_eq!(dup.a, sup_ptr.sup_e1_var_use_ptr());
            assert_eq!(dup.b, sup_ptr.sup_e2_var_use_ptr());
            assert_eq!(dup.e, lam_ptr);
            assert_eq!(lam.x, lam_ptr.lam_e_var_use_ptr());
            assert_eq!(lam.e, lam_ptr);
        }
    }

    #[test]
    fn test_dup_dup_dup_sup_from_term() {
        // term = (let #0{v1 v2} = (let #1{v3 v4} = v0; #1{v3 v4}); #0{v1 v2})
        let term = Term::Dup(
            0,
            "v1".into(),
            "v2".into(),
            Box::new(Term::Dup(
                1,
                "v3".into(),
                "v4".into(),
                Box::new(Term::Var("v0".into())),
                Box::new(Term::Sup(
                    1,
                    Box::new(Term::Var("v3".into())),
                    Box::new(Term::Var("v4".into())),
                )),
            )),
            Box::new(Term::Sup(
                0,
                Box::new(Term::Var("v1".into())),
                Box::new(Term::Var("v2".into())),
            )),
        );
        let term_graph = TermGraph::from(&term);
        assert_eq!(term_graph.0.tag(), Tag::SupPtr);
        unsafe {
            let mut nodes = Vec::new();
            visit_nodes(term_graph.0, |ptr| nodes.push(ptr));
            assert_eq!(nodes.len(), 4);
            assert_eq!(nodes[0].tag(), Tag::SupPtr);
            assert_eq!(nodes[1].tag(), Tag::DupPtr);
            assert_eq!(nodes[2].tag(), Tag::SupPtr);
            assert_eq!(nodes[3].tag(), Tag::DupPtr);
            let sup_v1_v2_ptr = nodes[0];
            let dup_v1_v2_ptr = nodes[1];
            let sup_v3_v4_ptr = nodes[2];
            let dup_v3_v4_ptr2 = nodes[3];
            let sup_v1_v2 = sup_v1_v2_ptr.read_sup();
            let dup_v1_v2 = dup_v1_v2_ptr.read_dup();
            let sup_v3_v4 = sup_v3_v4_ptr.read_sup();
            let dup_v3_v4 = dup_v3_v4_ptr2.read_dup();
            assert_eq!(sup_v1_v2.l, 0);
            assert_eq!(sup_v1_v2.e1, dup_v1_v2_ptr);
            assert_eq!(sup_v1_v2.e2, dup_v1_v2_ptr);
            assert_eq!(dup_v1_v2.l, 0);
            assert_eq!(dup_v1_v2.a, sup_v1_v2_ptr.sup_e1_var_use_ptr());
            assert_eq!(dup_v1_v2.b, sup_v1_v2_ptr.sup_e2_var_use_ptr());
            assert_eq!(dup_v1_v2.e, sup_v3_v4_ptr);
            assert_eq!(sup_v3_v4.l, 1);
            assert_eq!(sup_v3_v4.e1, dup_v3_v4_ptr2);
            assert_eq!(sup_v3_v4.e2, dup_v3_v4_ptr2);
            assert_eq!(dup_v3_v4.l, 1);
            assert_eq!(dup_v3_v4.a, sup_v3_v4_ptr.sup_e1_var_use_ptr());
            assert_eq!(dup_v3_v4.b, sup_v3_v4_ptr.sup_e2_var_use_ptr());
            assert_eq!(dup_v3_v4.e, Tagged::new_unbound_var());
        }
    }

    #[test]
    fn test_app_lam_dup_sup_lam() {
        // term = ((λx let #0{x0 x1} = x; #0{x0 x1}) (λy. y))
        let term = Term::App(
            Box::new(Term::Lam(
                "x".into(),
                Box::new(Term::Dup(
                    0,
                    "x0".into(),
                    "x1".into(),
                    Box::new(Term::Var("x".into())),
                    Box::new(Term::Sup(
                        0,
                        Box::new(Term::Var("x0".into())),
                        Box::new(Term::Var("x1".into())),
                    )),
                )),
            )),
            Box::new(Term::Lam("y".into(), Box::new(Term::Var("y".into())))),
        );
        let term_graph = TermGraph::from(&term);
        assert_eq!(term_graph.0.tag(), Tag::AppPtr);
        unsafe {
            let mut nodes = Vec::new();
            visit_nodes(term_graph.0, |ptr| nodes.push(ptr));
            assert_eq!(nodes.len(), 5);
            assert_eq!(nodes[0].tag(), Tag::AppPtr);
            assert_eq!(nodes[1].tag(), Tag::LamPtr);
            assert_eq!(nodes[2].tag(), Tag::LamPtr);
            assert_eq!(nodes[3].tag(), Tag::SupPtr);
            assert_eq!(nodes[4].tag(), Tag::DupPtr);
            let app_ptr = nodes[0];
            let lam_x_ptr = nodes[1];
            let lam_y_ptr = nodes[2];
            let sup_ptr = nodes[3];
            let dup_ptr = nodes[4];
            let app = app_ptr.read_app();
            let lam_x = lam_x_ptr.read_lam();
            let lam_y = lam_y_ptr.read_lam();
            let sup = sup_ptr.read_sup();
            let dup = dup_ptr.read_dup();
            assert_eq!(app.e1, lam_x_ptr);
            assert_eq!(app.e2, lam_y_ptr);
            assert_eq!(lam_x.x, dup_ptr.dup_e_var_use_ptr());
            assert_eq!(lam_x.e, sup_ptr);
            assert_eq!(lam_y.x, lam_y_ptr.lam_e_var_use_ptr());
            assert_eq!(lam_y.e, lam_y_ptr);
            assert_eq!(sup.l, 0);
            assert_eq!(sup.e1, dup_ptr);
            assert_eq!(sup.e2, dup_ptr);
            assert_eq!(dup.l, 0);
            assert_eq!(dup.a, sup_ptr.sup_e1_var_use_ptr());
            assert_eq!(dup.b, sup_ptr.sup_e2_var_use_ptr());
            assert_eq!(dup.e, lam_x_ptr);
        }
    }

    #[test]
    fn test_app_lam_var_reduce() {
        // ((λx. x) y)
        // ----------- AppLam
        // y
        let term = Term::App(
            Box::new(Term::Lam("x".into(), Box::new(Term::Var("x".into())))),
            Box::new(Term::Var("y".into())),
        );
        let mut term_graph = TermGraph::from(&term);

        term_graph.naive_random_order_reduce();

        assert_eq!(term_graph.0.tag(), Tag::UnboundVar);
        unsafe {
            let mut nodes = Vec::new();
            visit_nodes(term_graph.0, |ptr| nodes.push(ptr));
            assert_eq!(nodes.len(), 0);
        }
    }

    #[test]
    fn test_app_sup_reduce() {
        // #0{x0 x1} y
        // ------------------- AppSup
        // dup #0{y0 y1} = y
        // #0{(x0 y0) (x1 y1)}
        let term = Term::App(
            Box::new(Term::Sup(
                0,
                Box::new(Term::Var("x0".into())),
                Box::new(Term::Var("x1".into())),
            )),
            Box::new(Term::Var("y".into())),
        );
        let mut term_graph = TermGraph::from(&term);

        term_graph.naive_random_order_reduce();

        assert_eq!(term_graph.0.tag(), Tag::SupPtr);
        unsafe {
            let mut nodes = Vec::new();
            visit_nodes(term_graph.0, |ptr| nodes.push(ptr));
            assert_eq!(nodes.len(), 4);
            assert_eq!(nodes[0].tag(), Tag::SupPtr);
            assert_eq!(nodes[1].tag(), Tag::AppPtr);
            assert_eq!(nodes[2].tag(), Tag::AppPtr);
            assert_eq!(nodes[3].tag(), Tag::DupPtr);
            let sup_ptr = nodes[0];
            let app_x0_y0_ptr = nodes[1];
            let app_x1_y1_ptr = nodes[2];
            let dup_ptr = nodes[3];
            let sup = sup_ptr.read_sup();
            let app_x0_y0 = app_x0_y0_ptr.read_app();
            let app_x1_y1 = app_x1_y1_ptr.read_app();
            let dup = dup_ptr.read_dup();
            assert_eq!(sup.l, 0);
            assert_eq!(sup.e1, app_x0_y0_ptr);
            assert_eq!(sup.e2, app_x1_y1_ptr);
            assert_eq!(app_x0_y0.e1, Tagged::new_unbound_var());
            assert_eq!(app_x0_y0.e2, dup_ptr);
            assert_eq!(app_x1_y1.e1, Tagged::new_unbound_var());
            assert_eq!(app_x1_y1.e2, dup_ptr);
            assert_eq!(dup.l, 0);
            assert_eq!(dup.a, app_x0_y0_ptr.app_e2_var_use_ptr());
            assert_eq!(dup.b, app_x1_y1_ptr.app_e2_var_use_ptr());
            assert_eq!(dup.e, Tagged::new_unbound_var());
        }
    }
}
