use rand::seq::SliceRandom;
use std::collections::{HashMap, HashSet, VecDeque};
use std::mem::{align_of, size_of};
use std::ptr::addr_of_mut;
use std::{fmt, ptr};

use crate::intern::IStr;
use crate::syntax::Term;

/// A lambda node, e.g. `(λx e)`.
#[derive(Debug, Clone, Copy)]
#[repr(C, align(8))]
struct Lam {
    x: Tagged,
    e: Tagged,
}

/// An application node, e.g. `(e1 e2)`.
#[derive(Debug, Clone, Copy)]
#[repr(C, align(8))]
struct App {
    e1: Tagged,
    e2: Tagged,
}

/// A superposition node, e.g. `#l{e1 e2}`.
#[derive(Debug, Clone, Copy)]
#[repr(C, align(8))]
struct Sup {
    l: u64,
    e1: Tagged,
    e2: Tagged,
}

/// A duplication node, e.g. `dup #l{a b} = e;`
#[derive(Debug, Clone, Copy)]
#[repr(C, align(8))]
struct Dup {
    l: u64,
    a: Tagged,
    b: Tagged,
    e: Tagged,
}

#[derive(Debug, Clone, Copy)]
enum NodeType {
    Lam,
    App,
    Sup,
    Dup,
}

impl Lam {
    #[inline(always)]
    unsafe fn alloc() -> Tagged {
        let ptr = std::alloc::alloc(std::alloc::Layout::new::<Self>()) as *mut ();
        Tagged::new(ptr, Tag::LamPtr)
    }
}

impl App {
    #[inline(always)]
    unsafe fn alloc() -> Tagged {
        let ptr = std::alloc::alloc(std::alloc::Layout::new::<Self>()) as *mut ();
        Tagged::new(ptr, Tag::AppPtr)
    }
}

impl Sup {
    #[inline(always)]
    unsafe fn alloc() -> Tagged {
        let ptr = std::alloc::alloc(std::alloc::Layout::new::<Self>()) as *mut ();
        Tagged::new(ptr, Tag::SupPtr)
    }
}

impl Dup {
    #[inline(always)]
    unsafe fn alloc() -> Tagged {
        let ptr = std::alloc::alloc(std::alloc::Layout::new::<Self>()) as *mut ();
        Tagged::new(ptr, Tag::DupPtr)
    }
}

trait LamPtrExt {
    unsafe fn x(self) -> *mut Tagged;
    unsafe fn e(self) -> *mut Tagged;
}

impl LamPtrExt for *mut Lam {
    #[inline(always)]
    unsafe fn x(self) -> *mut Tagged {
        addr_of_mut!((*self).x)
    }

    #[inline(always)]
    unsafe fn e(self) -> *mut Tagged {
        addr_of_mut!((*self).e)
    }
}

trait AppPtrExt {
    unsafe fn e1(self) -> *mut Tagged;
    unsafe fn e2(self) -> *mut Tagged;
}

impl AppPtrExt for *mut App {
    #[inline(always)]
    unsafe fn e1(self) -> *mut Tagged {
        addr_of_mut!((*self).e1)
    }

    #[inline(always)]
    unsafe fn e2(self) -> *mut Tagged {
        addr_of_mut!((*self).e2)
    }
}

trait SupPtrExt {
    unsafe fn l(self) -> *mut u64;
    unsafe fn e1(self) -> *mut Tagged;
    unsafe fn e2(self) -> *mut Tagged;
}

impl SupPtrExt for *mut Sup {
    #[inline(always)]
    unsafe fn l(self) -> *mut u64 {
        addr_of_mut!((*self).l)
    }

    #[inline(always)]
    unsafe fn e1(self) -> *mut Tagged {
        addr_of_mut!((*self).e1)
    }

    #[inline(always)]
    unsafe fn e2(self) -> *mut Tagged {
        addr_of_mut!((*self).e2)
    }
}

trait DupPtrExt {
    unsafe fn l(self) -> *mut u64;
    unsafe fn a(self) -> *mut Tagged;
    unsafe fn b(self) -> *mut Tagged;
    unsafe fn e(self) -> *mut Tagged;
}

impl DupPtrExt for *mut Dup {
    #[inline(always)]
    unsafe fn l(self) -> *mut u64 {
        addr_of_mut!((*self).l)
    }

    #[inline(always)]
    unsafe fn a(self) -> *mut Tagged {
        addr_of_mut!((*self).a)
    }

    #[inline(always)]
    unsafe fn b(self) -> *mut Tagged {
        addr_of_mut!((*self).b)
    }

    #[inline(always)]
    unsafe fn e(self) -> *mut Tagged {
        addr_of_mut!((*self).e)
    }
}

/// A tagged value or pointer.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
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
    /// A variable bound by a `Lam::x`. Points to the binding `Lam` node.
    LamBoundVar = 4,
    /// A variable bound by a `Dup::a`. Points to the binding `Dup` node.
    DupABoundVar = 5,
    /// A variable bound by a `Dup::b`. Points to the binding `Dup` node.
    DupBBoundVar = 6,
    /// A pointer to a `Lam` node.
    LamPtr = 7,
    /// A pointer to an `App` node.
    AppPtr = 8,
    /// A pointer to a `Sup` node.
    SupPtr = 9,
    /// A pointer to a `Dup` node.
    DupPtr = 10,
}

impl Tag {
    // NOTE: We're storing the tag in the top 4 bits of the pointer.
    const BIT_OFFSET: u64 = 60;
    const MASK: u64 = 0xF000000000000000;
}

impl Tagged {
    #[inline(always)]
    unsafe fn new(ptr: *mut (), tag: Tag) -> Self {
        const _: () = assert!(size_of::<*mut ()>() == size_of::<u64>());
        let value = ((tag as u64) << Tag::BIT_OFFSET) | (ptr as u64);
        let tagged = Tagged(value as *mut ());
        debug_assert_eq!(tagged.ptr(), ptr);
        debug_assert_eq!(tagged.tag(), tag);
        tagged
    }

    #[inline(always)]
    fn ptr(self) -> *mut () {
        // NOTE: We're assuming the top 4 pointer bits are always 0.
        (self.0 as u64 & !Tag::MASK) as *mut ()
    }

    #[inline(always)]
    unsafe fn tag(self) -> Tag {
        let value = (self.0 as u64 >> Tag::BIT_OFFSET) as u8;
        debug_assert!(value >= Tag::UnusedVar as u8);
        debug_assert!(value <= Tag::DupPtr as u8);
        std::mem::transmute(value)
    }

    unsafe fn node_type(self) -> NodeType {
        match self.tag() {
            Tag::LamPtr => NodeType::Lam,
            Tag::AppPtr => NodeType::App,
            Tag::SupPtr => NodeType::Sup,
            Tag::DupPtr => NodeType::Dup,
            _ => panic!(),
        }
    }

    #[inline(always)]
    unsafe fn new_unused_var() -> Self {
        Tagged::new(ptr::null_mut(), Tag::UnusedVar)
    }

    #[inline(always)]
    unsafe fn new_unbound_var() -> Self {
        Tagged::new(ptr::null_mut(), Tag::UnboundVar)
    }

    #[inline(always)]
    unsafe fn var_use(self) -> *mut Tagged {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), Tag::VarUsePtr);
        self.ptr() as *mut Tagged
    }

    #[inline(always)]
    unsafe fn lam(self) -> *mut Lam {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert!(self.tag() == Tag::LamPtr || self.tag() == Tag::LamBoundVar);
        self.ptr() as *mut Lam
    }

    #[inline(always)]
    unsafe fn app(self) -> *mut App {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), Tag::AppPtr);
        self.ptr() as *mut App
    }

    #[inline(always)]
    unsafe fn sup(self) -> *mut Sup {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), Tag::SupPtr);
        self.ptr() as *mut Sup
    }

    #[inline(always)]
    unsafe fn dup(self) -> *mut Dup {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert!(
            self.tag() == Tag::DupPtr
                || self.tag() == Tag::DupABoundVar
                || self.tag() == Tag::DupBBoundVar
        );
        self.ptr() as *mut Dup
    }

    #[inline(always)]
    unsafe fn var_use_read(self) -> Tagged {
        if self.tag() == Tag::UnusedVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
            Tagged::new_unbound_var()
        } else {
            self.var_use().read()
        }
    }

    #[inline(always)]
    unsafe fn lam_read(self) -> Lam {
        self.lam().read()
    }

    #[inline(always)]
    unsafe fn app_read(self) -> App {
        self.app().read()
    }

    #[inline(always)]
    unsafe fn sup_read(self) -> Sup {
        self.sup().read()
    }

    #[inline(always)]
    unsafe fn dup_read(self) -> Dup {
        self.dup().read()
    }

    #[inline(always)]
    unsafe fn var_use_write_if_used(self, val: Tagged) {
        if self.tag() == Tag::UnusedVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
        } else {
            self.var_use().write(val)
        }
    }

    #[inline(always)]
    unsafe fn lam_write_if_bound(self, lam: Lam) {
        if self.tag() == Tag::UnboundVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
        } else {
            self.lam().write(lam)
        }
    }

    #[allow(dead_code)]
    #[inline(always)]
    unsafe fn app_write_if_bound(self, app: App) {
        if self.tag() == Tag::UnboundVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
        } else {
            self.app().write(app)
        }
    }

    #[inline(always)]
    unsafe fn sup_write_if_bound(self, sup: Sup) {
        if self.tag() == Tag::UnboundVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
        } else {
            self.sup().write(sup)
        }
    }

    #[allow(dead_code)]
    #[inline(always)]
    unsafe fn dup_write_if_bound(self, dup: Dup) {
        if self.tag() == Tag::UnboundVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
        } else {
            self.dup().write(dup)
        }
    }

    #[inline(always)]
    unsafe fn lam_e_var_use_ptr(self) -> Tagged {
        if self.tag() == Tag::UnboundVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
            Tagged::new_unused_var()
        } else {
            Tagged::new(self.lam().e() as *mut (), Tag::VarUsePtr)
        }
    }

    #[inline(always)]
    unsafe fn app_e1_var_use_ptr(self) -> Tagged {
        if self.tag() == Tag::UnboundVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
            Tagged::new_unused_var()
        } else {
            Tagged::new(self.app().e1() as *mut (), Tag::VarUsePtr)
        }
    }

    #[inline(always)]
    unsafe fn app_e2_var_use_ptr(self) -> Tagged {
        if self.tag() == Tag::UnboundVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
            Tagged::new_unused_var()
        } else {
            Tagged::new(self.app().e2() as *mut (), Tag::VarUsePtr)
        }
    }

    #[inline(always)]
    unsafe fn sup_e1_var_use_ptr(self) -> Tagged {
        if self.tag() == Tag::UnboundVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
            Tagged::new_unused_var()
        } else {
            Tagged::new(self.sup().e1() as *mut (), Tag::VarUsePtr)
        }
    }

    #[inline(always)]
    unsafe fn sup_e2_var_use_ptr(self) -> Tagged {
        if self.tag() == Tag::UnboundVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
            Tagged::new_unused_var()
        } else {
            Tagged::new(self.sup().e2() as *mut (), Tag::VarUsePtr)
        }
    }

    #[inline(always)]
    unsafe fn dup_e_var_use_ptr(self) -> Tagged {
        if self.tag() == Tag::UnboundVar {
            debug_assert_eq!(self.ptr(), ptr::null_mut());
            Tagged::new_unused_var()
        } else {
            Tagged::new(self.dup().e() as *mut (), Tag::VarUsePtr)
        }
    }

    #[inline(always)]
    unsafe fn if_bound_var_move_to(self, var_use_ptr: Tagged) {
        match self.tag() {
            Tag::LamBoundVar => self.lam().x().write(var_use_ptr),
            Tag::DupABoundVar => self.dup().a().write(var_use_ptr),
            Tag::DupBBoundVar => self.dup().b().write(var_use_ptr),
            _ => {}
        }
    }

    #[inline(always)]
    unsafe fn lam_bound_var(self) -> Tagged {
        debug_assert_eq!(self.tag(), Tag::LamPtr);
        Tagged::new(self.ptr(), Tag::LamBoundVar)
    }

    #[inline(always)]
    unsafe fn dup_a_bound_var(self) -> Tagged {
        debug_assert_eq!(self.tag(), Tag::DupPtr);
        Tagged::new(self.ptr(), Tag::DupABoundVar)
    }

    #[inline(always)]
    unsafe fn dup_b_bound_var(self) -> Tagged {
        debug_assert_eq!(self.tag(), Tag::DupPtr);
        Tagged::new(self.ptr(), Tag::DupBBoundVar)
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
            _ => panic!("dealloc_any called on non-node pointer"),
        }
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

        // println!("After reduce_redex:");
        // print_graph(root_ptr_ptr.read());
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
            Tag::UnusedVar | Tag::VarUsePtr | Tag::UnboundVar | Tag::LamBoundVar => {}
            Tag::LamPtr => {
                stack.push(ptr.lam().e());
            }
            Tag::AppPtr => {
                match ptr.app().e1().read().tag() {
                    Tag::LamPtr => redexes.push(ptr_ptr),
                    Tag::SupPtr => redexes.push(ptr_ptr),
                    _ => {}
                }
                stack.push(ptr.app().e1());
                stack.push(ptr.app().e2());
            }
            Tag::SupPtr => {
                stack.push(ptr.sup().e1());
                stack.push(ptr.sup().e2());
            }
            Tag::DupABoundVar | Tag::DupBBoundVar | Tag::DupPtr => {
                match ptr.dup().e().read().tag() {
                    Tag::LamPtr => redexes.push(ptr_ptr),
                    Tag::SupPtr => redexes.push(ptr_ptr),
                    _ => {}
                }
                stack.push(ptr.dup().e());
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
            let app_e1 = app_ptr.app().e1().read();
            match app_e1.tag() {
                Tag::LamPtr => app_lam_rule(ptr_ptr, app_ptr, app_e1),
                Tag::SupPtr => app_sup_rule(ptr_ptr, app_ptr, app_e1),
                _ => unreachable!(),
            }
        }
        Tag::DupPtr => {
            let dup_ptr = ptr;
            let dup_e = dup_ptr.dup().e().read();
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

    // x <- e2
    let x_use_ptr = lam_ptr.lam().x().read();
    let e2_ptr = app_ptr.app().e2().read();
    debug_assert_eq!(x_use_ptr.var_use_read(), lam_ptr.lam_bound_var());
    x_use_ptr.var_use_write_if_used(e2_ptr);
    e2_ptr.if_bound_var_move_to(x_use_ptr);

    // e
    let e_ptr = lam_ptr.lam().e().read();
    ptr_ptr.write(e_ptr);
    e_ptr.if_bound_var_move_to(Tagged::new(ptr_ptr as *mut _, Tag::VarUsePtr));

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

    let l = sup_e1_e2_ptr.sup().l().read();

    let dup_a_b_ptr = Dup::alloc();
    let app_e1_a_ptr = App::alloc();
    let app_e2_b_ptr = App::alloc();
    let sup_app_app_ptr = Sup::alloc();

    // dup #l{a b} = e3
    let a = app_e1_a_ptr.app_e2_var_use_ptr();
    let b = app_e2_b_ptr.app_e2_var_use_ptr();
    let e3 = app_sup_e3_ptr.app().e2().read();
    dup_a_b_ptr.dup().write(Dup { l, a, b, e: e3 });
    e3.if_bound_var_move_to(dup_a_b_ptr.dup_e_var_use_ptr());

    // (e1 a)
    let e1 = sup_e1_e2_ptr.sup().e1().read();
    let a = dup_a_b_ptr.dup_a_bound_var();
    app_e1_a_ptr.app().write(App { e1, e2: a });
    e1.if_bound_var_move_to(app_e1_a_ptr.app_e1_var_use_ptr());

    // (e2 b)
    let e2 = sup_e1_e2_ptr.sup().e2().read();
    let b = dup_a_b_ptr.dup_b_bound_var();
    app_e2_b_ptr.app().write(App { e1: e2, e2: b });
    e2.if_bound_var_move_to(app_e2_b_ptr.app_e1_var_use_ptr());

    // #l{(e1 a) (e2 b)}
    sup_app_app_ptr.sup().write(Sup {
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
    // -------------------- DupLam
    // a <- (λx1 c)
    // b <- (λx2 d)
    // x <- #l{x1 x2}
    // dup #l{c d} = e

    let dup_a_b_ptr = dup_ptr;
    let lam_x_e_ptr = lam_ptr;

    let l = dup_a_b_ptr.dup().l().read();
    let dup_a_b_a = dup_a_b_ptr.dup().a().read();
    let dup_a_b_b = dup_a_b_ptr.dup().b().read();
    let lam_x_e_x = lam_x_e_ptr.lam().x().read();

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
    debug_assert_eq!(dup_a_b_a.var_use_read(), dup_a_b_ptr);
    dup_a_b_a.var_use_write_if_used(lam_x1_c_ptr);
    lam_x1_c_ptr.lam_write_if_bound(Lam {
        x: sup_x1_x2_ptr.sup_e1_var_use_ptr(),
        e: dup_c_d_ptr,
    });

    // b <- (λx2 d)
    debug_assert_eq!(dup_a_b_b.var_use_read(), dup_a_b_ptr);
    dup_a_b_b.var_use_write_if_used(lam_x2_d_ptr);
    lam_x2_d_ptr.lam_write_if_bound(Lam {
        x: sup_x1_x2_ptr.sup_e2_var_use_ptr(),
        e: dup_c_d_ptr,
    });

    // x <- #l{x1,x2}
    debug_assert_eq!(lam_x_e_x.var_use_read(), dup_a_b_ptr.dup().e().read());
    lam_x_e_x.var_use_write_if_used(sup_x1_x2_ptr);
    sup_x1_x2_ptr.sup_write_if_bound(Sup {
        l,
        e1: lam_x1_c_ptr,
        e2: lam_x2_d_ptr,
    });

    // dup #l{c d} = e
    let e = lam_x_e_ptr.lam().e().read();
    dup_c_d_ptr.dup().write(Dup {
        l,
        a: lam_x1_c_ptr.lam_e_var_use_ptr(),
        b: lam_x2_d_ptr.lam_e_var_use_ptr(),
        e,
    });
    e.if_bound_var_move_to(dup_c_d_ptr.dup_e_var_use_ptr());

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

    let l = dup_a_b_ptr.dup().l().read();
    let m = sup_e1_e2_ptr.sup().l().read();
    let dup_a_b_a = dup_a_b_ptr.dup().a().read();
    let dup_a_b_b = dup_a_b_ptr.dup().b().read();

    // let sup_e1_e2 = sup_e1_e2_ptr.read_sup();

    if l == m {
        // a <- e1
        debug_assert_eq!(dup_a_b_a.var_use_read(), dup_a_b_ptr);
        let e1 = sup_e1_e2_ptr.sup().e1().read();
        dup_a_b_a.var_use_write_if_used(e1);
        e1.if_bound_var_move_to(dup_a_b_a);
        // b <- e2
        debug_assert_eq!(dup_a_b_b.var_use_read(), dup_a_b_ptr);
        let e2 = sup_e1_e2_ptr.sup().e2().read();
        dup_a_b_b.var_use_write_if_used(e2);
        e2.if_bound_var_move_to(dup_a_b_b);
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
        debug_assert_eq!(dup_a_b_a.var_use_read(), dup_a_b_ptr);
        dup_a_b_a.var_use_write_if_used(sup_a1_a2_ptr);
        sup_a1_a2_ptr.sup_write_if_bound(Sup {
            l: m,
            e1: dup_a1_b1_ptr,
            e2: dup_a2_b2_ptr,
        });

        // b <- #m{b1 b2}
        debug_assert_eq!(dup_a_b_b.var_use_read(), dup_a_b_ptr);
        dup_a_b_b.var_use_write_if_used(sup_b1_b2_ptr);
        sup_b1_b2_ptr.sup_write_if_bound(Sup {
            l: m,
            e1: dup_a1_b1_ptr,
            e2: dup_a2_b2_ptr,
        });
        // dup #l{a1 b1} = e1
        let e1 = sup_e1_e2_ptr.sup().e1().read();
        dup_a1_b1_ptr.dup().write(Dup {
            l,
            a: sup_a1_a2_ptr.sup_e1_var_use_ptr(),
            b: sup_b1_b2_ptr.sup_e1_var_use_ptr(),
            e: e1,
        });
        e1.if_bound_var_move_to(dup_a1_b1_ptr.dup_e_var_use_ptr());
        // dup #l{a2 b2} = e2
        let e2 = sup_e1_e2_ptr.sup().e2().read();
        dup_a2_b2_ptr.dup().write(Dup {
            l,
            a: sup_a1_a2_ptr.sup_e2_var_use_ptr(),
            b: sup_b1_b2_ptr.sup_e2_var_use_ptr(),
            e: e2,
        });
        e2.if_bound_var_move_to(dup_a2_b2_ptr.dup_e_var_use_ptr());
    }

    // deallocate unreachable nodes
    dup_a_b_ptr.dealloc_dup();
    sup_e1_e2_ptr.dealloc_sup();
}

struct NodeIter {
    visited: HashSet<Tagged>,
    queue: VecDeque<Tagged>,
}

impl NodeIter {
    fn new(ptr: Tagged) -> Self {
        let visited = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(ptr);
        Self { visited, queue }
    }
}

impl Iterator for NodeIter {
    type Item = Tagged;
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            while let Some(ptr) = self.queue.pop_front() {
                if self.visited.contains(&ptr) {
                    continue;
                }
                self.visited.insert(ptr);
                match ptr.tag() {
                    Tag::UnusedVar => {}
                    Tag::VarUsePtr => unreachable!(),
                    Tag::UnboundVar => {}
                    Tag::LamBoundVar => {}
                    Tag::DupABoundVar | Tag::DupBBoundVar => {
                        self.queue.push_back(Tagged::new(ptr.ptr(), Tag::DupPtr));
                    }
                    Tag::LamPtr => {
                        let lam = ptr.lam_read();
                        if lam.x.tag() == Tag::VarUsePtr {
                            self.queue.push_back(lam.x.var_use_read());
                        }
                        self.queue.push_back(lam.e);
                        return Some(ptr);
                    }
                    Tag::AppPtr => {
                        let app = ptr.app_read();
                        self.queue.push_back(app.e1);
                        self.queue.push_back(app.e2);
                        return Some(ptr);
                    }
                    Tag::SupPtr => {
                        let sup = ptr.sup_read();
                        self.queue.push_back(sup.e1);
                        self.queue.push_back(sup.e2);
                        return Some(ptr);
                    }
                    Tag::DupPtr => {
                        let dup = ptr.dup_read();
                        if dup.a.tag() == Tag::VarUsePtr {
                            self.queue.push_back(dup.a.var_use_read());
                        }
                        if dup.b.tag() == Tag::VarUsePtr {
                            self.queue.push_back(dup.b.var_use_read());
                        }
                        self.queue.push_back(dup.e);
                        return Some(ptr);
                    }
                }
            }
        }
        None
    }
}

/// An owned term graph.
pub struct TermGraph(Tagged);

impl TermGraph {
    fn node_iter(&self) -> NodeIter {
        NodeIter::new(self.0)
    }
}

impl Drop for TermGraph {
    fn drop(&mut self) {
        let nodes = self.node_iter().collect::<Vec<_>>();
        for node in nodes {
            unsafe { node.dealloc_any() };
        }
    }
}

impl fmt::Debug for Tagged {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?} {:?}", unsafe { self.tag() }, self.ptr())
    }
}

#[allow(dead_code)]
fn print_graph(ptr: Tagged) {
    for ptr in NodeIter::new(ptr) {
        print!("{:?}", ptr.ptr());
        unsafe {
            match ptr.node_type() {
                NodeType::Lam => println!(" {:?}", ptr.lam_read()),
                NodeType::App => println!(" {:?}", ptr.app_read()),
                NodeType::Sup => println!(" {:?}", ptr.sup_read()),
                NodeType::Dup => println!(" {:?}", ptr.dup_read()),
            }
        }
    }
}

impl fmt::Debug for TermGraph {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for ptr in self.node_iter() {
            write!(f, "{:?}", ptr.ptr())?;
            unsafe {
                match ptr.node_type() {
                    NodeType::Lam => write!(f, " {:?}\n", ptr.lam_read())?,
                    NodeType::App => write!(f, " {:?}\n", ptr.app_read())?,
                    NodeType::Sup => write!(f, " {:?}\n", ptr.sup_read())?,
                    NodeType::Dup => write!(f, " {:?}\n", ptr.dup_read())?,
                }
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
                    app_ptr.app().write(App { e1, e2 });
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
                    sup_ptr.sup().write(Sup { l: *l, e1, e2 });
                    sup_ptr
                }
                Term::Dup(l, a_str, b_str, e_term, cont_term) => {
                    let dup_ptr = Dup::alloc();
                    let a_scopes = var_binders.entry(*a_str).or_default();
                    a_scopes.push(dup_ptr.dup_a_bound_var());
                    let a_scope = a_scopes.len();
                    let b_scopes = var_binders.entry(*b_str).or_default();
                    b_scopes.push(dup_ptr.dup_b_bound_var());
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
                    dup_ptr.dup().write(Dup { l: *l, a, b, e });
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
                    app_ptr.app().write(App {
                        e1: lam_ptr,
                        e2: e1,
                    });
                    app_ptr
                }
            }
        }
        unsafe fn register_var_use(
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
            x_scopes.push(lam_ptr.lam_bound_var());
            let x_scope = x_scopes.len();
            let e = recurse(var_binders, var_uses, e_term);
            let lam_e_var_use_ptr = lam_ptr.lam_e_var_use_ptr();
            register_var_use(var_binders, var_uses, e_term, e, lam_e_var_use_ptr);
            let x = var_uses
                .get(&(x_str, x_scope))
                .copied()
                .unwrap_or(Tagged::new_unused_var());
            lam_ptr.lam().write(Lam { x, e });
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
            naive_random_order_reduce(addr_of_mut!(self.0));
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
        unsafe {
            assert_eq!(term_graph.0.tag(), Tag::AppPtr);
            let nodes = term_graph.node_iter().collect::<Vec<_>>();
            assert_eq!(nodes.len(), 2);
            assert_eq!(nodes[0].tag(), Tag::AppPtr);
            assert_eq!(nodes[1].tag(), Tag::LamPtr);
            let app_ptr = nodes[0];
            let lam_ptr = nodes[1];
            let app = app_ptr.app_read();
            let lam = lam_ptr.lam_read();
            assert_eq!(app.e1, lam_ptr);
            assert_eq!(app.e2.tag(), Tag::UnboundVar);
            assert_eq!(lam.x, lam_ptr.lam_e_var_use_ptr());
            assert_eq!(lam.e, lam_ptr.lam_bound_var());
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
        unsafe {
            assert_eq!(term_graph.0.tag(), Tag::AppPtr);
            let nodes = term_graph.node_iter().collect::<Vec<_>>();
            assert_eq!(nodes.len(), 2);
            assert_eq!(nodes[0].tag(), Tag::AppPtr);
            assert_eq!(nodes[1].tag(), Tag::SupPtr);
            let app_ptr = nodes[0];
            let sup_ptr = nodes[1];
            let app = app_ptr.app_read();
            let sup = sup_ptr.sup_read();
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
        unsafe {
            assert_eq!(term_graph.0.tag(), Tag::AppPtr);
            let nodes = term_graph.node_iter().collect::<Vec<_>>();
            assert_eq!(nodes.len(), 3);
            assert_eq!(nodes[0].tag(), Tag::AppPtr);
            assert_eq!(nodes[1].tag(), Tag::SupPtr);
            assert_eq!(nodes[2].tag(), Tag::DupPtr);
            let app_ptr = nodes[0];
            let sup_ptr = nodes[1];
            let dup_ptr = nodes[2];
            let app = app_ptr.app_read();
            let sup = sup_ptr.sup_read();
            let dup = dup_ptr.dup_read();
            assert_eq!(app.e1, sup_ptr);
            assert_eq!(app.e2.tag(), Tag::UnboundVar);
            assert_eq!(sup.l, 0);
            assert_eq!(sup.e1, dup_ptr.dup_a_bound_var());
            assert_eq!(sup.e2, dup_ptr.dup_b_bound_var());
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
            Box::new(Term::Lam("v0".into(), Box::new(Term::Var("v0".into())))),
            Box::new(Term::Sup(
                0,
                Box::new(Term::Var("v1".into())),
                Box::new(Term::Var("v2".into())),
            )),
        );
        let term_graph = TermGraph::from(&term);
        unsafe {
            assert_eq!(term_graph.0.tag(), Tag::SupPtr);
            let nodes = term_graph.node_iter().collect::<Vec<_>>();
            assert_eq!(nodes.len(), 3);
            assert_eq!(nodes[0].tag(), Tag::SupPtr);
            assert_eq!(nodes[1].tag(), Tag::DupPtr);
            assert_eq!(nodes[2].tag(), Tag::LamPtr);
            let sup_ptr = nodes[0];
            let dup_ptr = nodes[1];
            let lam_ptr = nodes[2];
            let sup = sup_ptr.sup_read();
            let dup = dup_ptr.dup_read();
            let lam = lam_ptr.lam_read();
            assert_eq!(sup.l, 0);
            assert_eq!(sup.e1, dup_ptr.dup_a_bound_var());
            assert_eq!(sup.e2, dup_ptr.dup_b_bound_var());
            assert_eq!(dup.l, 0);
            assert_eq!(dup.a, sup_ptr.sup_e1_var_use_ptr());
            assert_eq!(dup.b, sup_ptr.sup_e2_var_use_ptr());
            assert_eq!(dup.e, lam_ptr);
            assert_eq!(lam.x, lam_ptr.lam_e_var_use_ptr());
            assert_eq!(lam.e, lam_ptr.lam_bound_var());
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
        unsafe {
            assert_eq!(term_graph.0.tag(), Tag::SupPtr);
            let nodes = term_graph.node_iter().collect::<Vec<_>>();
            assert_eq!(nodes.len(), 4);
            assert_eq!(nodes[0].tag(), Tag::SupPtr);
            assert_eq!(nodes[1].tag(), Tag::DupPtr);
            assert_eq!(nodes[2].tag(), Tag::SupPtr);
            assert_eq!(nodes[3].tag(), Tag::DupPtr);
            let sup_v1_v2_ptr = nodes[0];
            let dup_v1_v2_ptr = nodes[1];
            let sup_v3_v4_ptr = nodes[2];
            let dup_v3_v4_ptr2 = nodes[3];
            let sup_v1_v2 = sup_v1_v2_ptr.sup_read();
            let dup_v1_v2 = dup_v1_v2_ptr.dup_read();
            let sup_v3_v4 = sup_v3_v4_ptr.sup_read();
            let dup_v3_v4 = dup_v3_v4_ptr2.dup_read();
            assert_eq!(sup_v1_v2.l, 0);
            assert_eq!(sup_v1_v2.e1, dup_v1_v2_ptr.dup_a_bound_var());
            assert_eq!(sup_v1_v2.e2, dup_v1_v2_ptr.dup_b_bound_var());
            assert_eq!(dup_v1_v2.l, 0);
            assert_eq!(dup_v1_v2.a, sup_v1_v2_ptr.sup_e1_var_use_ptr());
            assert_eq!(dup_v1_v2.b, sup_v1_v2_ptr.sup_e2_var_use_ptr());
            assert_eq!(dup_v1_v2.e, sup_v3_v4_ptr);
            assert_eq!(sup_v3_v4.l, 1);
            assert_eq!(sup_v3_v4.e1, dup_v3_v4_ptr2.dup_a_bound_var());
            assert_eq!(sup_v3_v4.e2, dup_v3_v4_ptr2.dup_b_bound_var());
            assert_eq!(dup_v3_v4.l, 1);
            assert_eq!(dup_v3_v4.a, sup_v3_v4_ptr.sup_e1_var_use_ptr());
            assert_eq!(dup_v3_v4.b, sup_v3_v4_ptr.sup_e2_var_use_ptr());
            assert_eq!(dup_v3_v4.e, Tagged::new_unbound_var());
        }
    }

    #[test]
    fn test_app_lam_dup_sup_lam_from_term() {
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
        unsafe {
            assert_eq!(term_graph.0.tag(), Tag::AppPtr);
            let nodes = term_graph.node_iter().collect::<Vec<_>>();
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
            let app = app_ptr.app_read();
            let lam_x = lam_x_ptr.lam_read();
            let lam_y = lam_y_ptr.lam_read();
            let sup = sup_ptr.sup_read();
            let dup = dup_ptr.dup_read();
            assert_eq!(app.e1, lam_x_ptr);
            assert_eq!(app.e2, lam_y_ptr);
            assert_eq!(lam_x.x, dup_ptr.dup_e_var_use_ptr());
            assert_eq!(lam_x.e, sup_ptr);
            assert_eq!(lam_y.x, lam_y_ptr.lam_e_var_use_ptr());
            assert_eq!(lam_y.e, lam_y_ptr.lam_bound_var());
            assert_eq!(sup.l, 0);
            assert_eq!(sup.e1, dup_ptr.dup_a_bound_var());
            assert_eq!(sup.e2, dup_ptr.dup_b_bound_var());
            assert_eq!(dup.l, 0);
            assert_eq!(dup.a, sup_ptr.sup_e1_var_use_ptr());
            assert_eq!(dup.b, sup_ptr.sup_e2_var_use_ptr());
            assert_eq!(dup.e, lam_x_ptr.lam_bound_var());
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

        println!("Before:\n{:?}", term_graph);
        term_graph.naive_random_order_reduce();
        println!("After:\n{:?}", term_graph);

        unsafe {
            assert_eq!(term_graph.0.tag(), Tag::UnboundVar);
            let nodes = term_graph.node_iter().collect::<Vec<_>>();
            assert_eq!(nodes.len(), 0);
        }
    }

    #[test]
    fn test_lam_app_lam_reduce() {
        // λy ((λx x) y)
        // ------------- AppLam
        // λy y
        let term = Term::Lam(
            "y".into(),
            Box::new(Term::App(
                Box::new(Term::Lam("x".into(), Box::new(Term::Var("x".into())))),
                Box::new(Term::Var("y".into())),
            )),
        );
        let mut term_graph = TermGraph::from(&term);

        println!("Before:\n{:?}", term_graph);
        term_graph.naive_random_order_reduce();
        println!("After:\n{:?}", term_graph);

        unsafe {
            assert_eq!(term_graph.0.tag(), Tag::LamPtr);
            let nodes = term_graph.node_iter().collect::<Vec<_>>();
            assert_eq!(nodes.len(), 1);
            assert_eq!(nodes[0].tag(), Tag::LamPtr);
            let lam_ptr = nodes[0];
            let lam = lam_ptr.lam_read();
            assert_eq!(lam.x, lam_ptr.lam_e_var_use_ptr());
            assert_eq!(lam.e, lam_ptr.lam_bound_var());
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

        println!("Before:\n{:?}", term_graph);
        term_graph.naive_random_order_reduce();
        println!("After:\n{:?}", term_graph);

        unsafe {
            assert_eq!(term_graph.0.tag(), Tag::SupPtr);
            let nodes = term_graph.node_iter().collect::<Vec<_>>();
            assert_eq!(nodes.len(), 4);
            assert_eq!(nodes[0].tag(), Tag::SupPtr);
            assert_eq!(nodes[1].tag(), Tag::AppPtr);
            assert_eq!(nodes[2].tag(), Tag::AppPtr);
            assert_eq!(nodes[3].tag(), Tag::DupPtr);
            let sup_ptr = nodes[0];
            let app_x0_y0_ptr = nodes[1];
            let app_x1_y1_ptr = nodes[2];
            let dup_ptr = nodes[3];
            let sup = sup_ptr.sup_read();
            let app_x0_y0 = app_x0_y0_ptr.app_read();
            let app_x1_y1 = app_x1_y1_ptr.app_read();
            let dup = dup_ptr.dup_read();
            assert_eq!(sup.l, 0);
            assert_eq!(sup.e1, app_x0_y0_ptr);
            assert_eq!(sup.e2, app_x1_y1_ptr);
            assert_eq!(app_x0_y0.e1, Tagged::new_unbound_var());
            assert_eq!(app_x0_y0.e2, dup_ptr.dup_a_bound_var());
            assert_eq!(app_x1_y1.e1, Tagged::new_unbound_var());
            assert_eq!(app_x1_y1.e2, dup_ptr.dup_b_bound_var());
            assert_eq!(dup.l, 0);
            assert_eq!(dup.a, app_x0_y0_ptr.app_e2_var_use_ptr());
            assert_eq!(dup.b, app_x1_y1_ptr.app_e2_var_use_ptr());
            assert_eq!(dup.e, Tagged::new_unbound_var());
        }
    }

    #[test]
    fn test_lam_lam_lam_app_sup_reduce() {
        // λx λy λz #0{x y} z
        // ------------------- AppSup
        // dup #0{z0 z1} = z
        // λx λy λz #0{(x z0) (y z1)}
        let term = Term::Lam(
            "x".into(),
            Box::new(Term::Lam(
                "y".into(),
                Box::new(Term::Lam(
                    "z".into(),
                    Box::new(Term::App(
                        Box::new(Term::Sup(
                            0,
                            Box::new(Term::Var("x".into())),
                            Box::new(Term::Var("y".into())),
                        )),
                        Box::new(Term::Var("z".into())),
                    )),
                )),
            )),
        );
        let mut term_graph = TermGraph::from(&term);

        println!("Before:\n{:?}", term_graph);
        term_graph.naive_random_order_reduce();
        println!("After:\n{:?}", term_graph);

        unsafe {
            assert_eq!(term_graph.0.tag(), Tag::LamPtr);
            let nodes = term_graph.node_iter().collect::<Vec<_>>();
            assert_eq!(nodes.len(), 7);
            assert_eq!(nodes[0].tag(), Tag::LamPtr);
            assert_eq!(nodes[1].tag(), Tag::LamPtr);
            assert_eq!(nodes[2].tag(), Tag::LamPtr);
            assert_eq!(nodes[3].tag(), Tag::SupPtr);
            assert_eq!(nodes[4].tag(), Tag::AppPtr);
            assert_eq!(nodes[5].tag(), Tag::AppPtr);
            assert_eq!(nodes[6].tag(), Tag::DupPtr);
            let lam_x_ptr = nodes[0];
            let lam_y_ptr = nodes[1];
            let lam_z_ptr = nodes[2];
            let sup_ptr = nodes[3];
            let app_x_z0_ptr = nodes[4];
            let app_y_z1_ptr = nodes[5];
            let dup_ptr = nodes[6];
            let lam_x = lam_x_ptr.lam_read();
            let lam_y = lam_y_ptr.lam_read();
            let lam_z = lam_z_ptr.lam_read();
            let sup = sup_ptr.sup_read();
            let app_x_z0 = app_x_z0_ptr.app_read();
            let app_y_z1 = app_y_z1_ptr.app_read();
            let dup = dup_ptr.dup_read();
            assert_eq!(lam_x.x, app_x_z0_ptr.app_e1_var_use_ptr());
            assert_eq!(lam_x.e, lam_y_ptr);
            assert_eq!(lam_y.x, app_y_z1_ptr.app_e1_var_use_ptr());
            assert_eq!(lam_y.e, lam_z_ptr);
            assert_eq!(lam_z.e, sup_ptr);
            assert_eq!(sup.l, 0);
            assert_eq!(sup.e1, app_x_z0_ptr);
            assert_eq!(sup.e2, app_y_z1_ptr);
            assert_eq!(app_x_z0.e1, lam_x_ptr.lam_bound_var());
            assert_eq!(app_x_z0.e2, dup_ptr.dup_a_bound_var());
            assert_eq!(app_y_z1.e1, lam_y_ptr.lam_bound_var());
            assert_eq!(app_y_z1.e2, dup_ptr.dup_b_bound_var());
            assert_eq!(dup.l, 0);
            assert_eq!(dup.a, app_x_z0_ptr.app_e2_var_use_ptr());
            assert_eq!(dup.b, app_y_z1_ptr.app_e2_var_use_ptr());
            assert_eq!(dup.e, lam_z_ptr.lam_bound_var());
        }
    }

    #[test]
    fn test_app_dup_app_sup_reduce() {
        // dup #0{v1 v2} = v0
        // #0{v1 v2} v3
        // ------------------- AppSup
        // dup #0{v1 v2} = v0
        // dup #0{v4 v5} = v3
        // #0{(v1 v4) (v2 v5)}
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
        let mut term_graph = TermGraph::from(&term);

        println!("Before:\n{:?}", term_graph);
        term_graph.naive_random_order_reduce();
        println!("After:\n{:?}", term_graph);

        unsafe {
            assert_eq!(term_graph.0.tag(), Tag::SupPtr);
            let nodes = term_graph.node_iter().collect::<Vec<_>>();
            assert_eq!(nodes.len(), 5);
            assert_eq!(nodes[0].tag(), Tag::SupPtr);
            assert_eq!(nodes[1].tag(), Tag::AppPtr);
            assert_eq!(nodes[2].tag(), Tag::AppPtr);
            assert_eq!(nodes[3].tag(), Tag::DupPtr);
            assert_eq!(nodes[4].tag(), Tag::DupPtr);
            let sup_ptr = nodes[0];
            let app_v1_v4_ptr = nodes[1];
            let app_v2_v5_ptr = nodes[2];
            let dup_v1_v2_ptr = nodes[3];
            let dup_v4_v5_ptr = nodes[4];
            let sup = sup_ptr.sup_read();
            let app_v1_v4 = app_v1_v4_ptr.app_read();
            let app_v2_v5 = app_v2_v5_ptr.app_read();
            let dup_v1_v2 = dup_v1_v2_ptr.dup_read();
            let dup_v4_v5 = dup_v4_v5_ptr.dup_read();
            assert_eq!(sup.l, 0);
            assert_eq!(sup.e1, app_v1_v4_ptr);
            assert_eq!(sup.e2, app_v2_v5_ptr);
            assert_eq!(app_v1_v4.e1, dup_v1_v2_ptr.dup_a_bound_var());
            assert_eq!(app_v1_v4.e2, dup_v4_v5_ptr.dup_a_bound_var());
            assert_eq!(app_v2_v5.e1, dup_v1_v2_ptr.dup_b_bound_var());
            assert_eq!(app_v2_v5.e2, dup_v4_v5_ptr.dup_b_bound_var());
            assert_eq!(dup_v1_v2.l, 0);
            assert_eq!(dup_v1_v2.a, app_v1_v4_ptr.app_e1_var_use_ptr());
            assert_eq!(dup_v1_v2.b, app_v2_v5_ptr.app_e1_var_use_ptr());
            assert_eq!(dup_v1_v2.e, Tagged::new_unbound_var());
            assert_eq!(dup_v4_v5.l, 0);
            assert_eq!(dup_v4_v5.a, app_v1_v4_ptr.app_e2_var_use_ptr());
            assert_eq!(dup_v4_v5.b, app_v2_v5_ptr.app_e2_var_use_ptr());
            assert_eq!(dup_v4_v5.e, Tagged::new_unbound_var());
        }
    }
}
