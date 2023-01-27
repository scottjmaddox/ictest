use std::mem::{align_of, size_of};
use std::ptr;

/// A pointer to a field inside of a `Lam`, `App`, `Sup`, or `Dup` node
/// representing a bound variable. Null represents an unused variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C, align(8))]
struct FieldPtr(*mut NodePtr);
const _: () = assert!(size_of::<FieldPtr>() == 8);
const _: () = assert!(align_of::<FieldPtr>() == 8);

impl FieldPtr {
    fn new_unused_var() -> Self {
        FieldPtr(ptr::null_mut())
    }

    fn is_unbound_var(self) -> bool {
        self.0.is_null()
    }

    #[inline(always)]
    unsafe fn read(self) -> NodePtr {
        if self.0.is_null() {
            NodePtr::new_unbound_var()
        } else {
            self.0.read()
        }
    }

    #[inline(always)]
    unsafe fn write(self, value: NodePtr) {
        if self.0.is_null() {
            return;
        } else {
            self.0.write(value)
        }
    }
}

/// A tagged pointer to a `Lam`, `App`, `Sup`, or `Dup` node.
/// Null represents an unbound variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C, align(8))]
struct NodePtr(*mut ());
const _: () = assert!(size_of::<NodePtr>() == 8);
const _: () = assert!(align_of::<NodePtr>() == 8);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum NodePtrTag {
    UnusedVar = 0,
    LamPtr = 1,
    AppPtr = 2,
    SupPtr = 3,
    DupPtr = 4,
}
impl NodePtrTag {
    const MASK: u64 = 0b111;
}

impl NodePtr {
    #[inline(always)]
    fn new(ptr: *mut (), tag: NodePtrTag) -> Self {
        const _: () = assert!(size_of::<*mut ()>() == size_of::<u64>());
        let value = ptr as u64 | tag as u64;
        let field = NodePtr(value as *mut ());
        debug_assert_eq!(field.tag(), tag);
        debug_assert_eq!(field.ptr(), ptr);
        field
    }

    #[inline(always)]
    fn new_unbound_var() -> Self {
        NodePtr::new(ptr::null_mut(), NodePtrTag::UnusedVar)
    }

    #[inline(always)]
    fn tag(self) -> NodePtrTag {
        let value = (self.0 as u64 & NodePtrTag::MASK) as u8;
        unsafe { std::mem::transmute(value) }
    }

    #[inline(always)]
    fn ptr(self) -> *mut () {
        (self.0 as u64 & !NodePtrTag::MASK) as *mut ()
    }

    #[inline(always)]
    unsafe fn read_lam(self) -> Lam {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), NodePtrTag::LamPtr);
        let ptr = self.ptr() as *const Lam;
        unsafe { ptr.read() }
    }

    #[inline(always)]
    unsafe fn read_app(self) -> App {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), NodePtrTag::AppPtr);
        let ptr = self.ptr() as *const App;
        unsafe { ptr.read() }
    }

    #[inline(always)]
    unsafe fn read_sup(self) -> Sup {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), NodePtrTag::SupPtr);
        let ptr = self.ptr() as *const Sup;
        unsafe { ptr.read() }
    }

    #[inline(always)]
    unsafe fn read_dup(self) -> Dup {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), NodePtrTag::DupPtr);
        let ptr = self.ptr() as *const Dup;
        unsafe { ptr.read() }
    }

    #[inline(always)]
    unsafe fn write_lam(self, lam: Lam) {
        if self.ptr().is_null() {
            return;
        } else {
            debug_assert_eq!(self.tag(), NodePtrTag::LamPtr);
            let ptr = self.ptr() as *mut Lam;
            unsafe { ptr.write(lam) }
        }
    }

    #[inline(always)]
    unsafe fn write_app(self, app: App) {
        if self.ptr().is_null() {
            return;
        } else {
            debug_assert_eq!(self.tag(), NodePtrTag::AppPtr);
            let ptr = self.ptr() as *mut App;
            unsafe { ptr.write(app) }
        }
    }

    #[inline(always)]
    unsafe fn write_sup(self, sup: Sup) {
        if self.ptr().is_null() {
            return;
        } else {
            debug_assert_eq!(self.tag(), NodePtrTag::SupPtr);
            let ptr = self.ptr() as *mut Sup;
            unsafe { ptr.write(sup) }
        }
    }

    #[inline(always)]
    unsafe fn write_dup(self, dup: Dup) {
        if self.ptr().is_null() {
            return;
        } else {
            debug_assert_eq!(self.tag(), NodePtrTag::DupPtr);
            let ptr = self.ptr() as *mut Dup;
            unsafe { ptr.write(dup) }
        }
    }

    #[inline(always)]
    fn lam_e_field_ptr(self) -> FieldPtr {
        if self.ptr().is_null() {
            FieldPtr::new_unused_var()
        } else {
            debug_assert_ne!(self.ptr(), ptr::null_mut());
            debug_assert_eq!(self.tag(), NodePtrTag::LamPtr);
            let ptr = self.ptr() as *mut Lam;
            unsafe { FieldPtr(&mut (*ptr).e) }
        }
    }

    #[inline(always)]
    fn app_e1_field_ptr(self) -> FieldPtr {
        if self.ptr().is_null() {
            FieldPtr::new_unused_var()
        } else {
            debug_assert_ne!(self.ptr(), ptr::null_mut());
            debug_assert_eq!(self.tag(), NodePtrTag::AppPtr);
            let ptr = self.ptr() as *mut App;
            unsafe { FieldPtr(&mut (*ptr).e1) }
        }
    }

    #[inline(always)]
    fn app_e2_field_ptr(self) -> FieldPtr {
        if self.ptr().is_null() {
            FieldPtr::new_unused_var()
        } else {
            debug_assert_ne!(self.ptr(), ptr::null_mut());
            debug_assert_eq!(self.tag(), NodePtrTag::AppPtr);
            let ptr = self.ptr() as *mut App;
            unsafe { FieldPtr(&mut (*ptr).e2) }
        }
    }

    #[inline(always)]
    fn sup_e1_field_ptr(self) -> FieldPtr {
        if self.ptr().is_null() {
            FieldPtr::new_unused_var()
        } else {
            debug_assert_ne!(self.ptr(), ptr::null_mut());
            debug_assert_eq!(self.tag(), NodePtrTag::SupPtr);
            let ptr = self.ptr() as *mut Sup;
            unsafe { FieldPtr(&mut (*ptr).e1) }
        }
    }

    #[inline(always)]
    fn sup_e2_field_ptr(self) -> FieldPtr {
        if self.ptr().is_null() {
            FieldPtr::new_unused_var()
        } else {
            debug_assert_ne!(self.ptr(), ptr::null_mut());
            debug_assert_eq!(self.tag(), NodePtrTag::SupPtr);
            let ptr = self.ptr() as *mut Sup;
            unsafe { FieldPtr(&mut (*ptr).e2) }
        }
    }

    #[inline(always)]
    fn dup_e_field_ptr(self) -> FieldPtr {
        if self.ptr().is_null() {
            FieldPtr::new_unused_var()
        } else {
            debug_assert_ne!(self.ptr(), ptr::null_mut());
            debug_assert_eq!(self.tag(), NodePtrTag::DupPtr);
            let ptr = self.ptr() as *mut Dup;
            unsafe { FieldPtr(&mut (*ptr).e) }
        }
    }

    #[inline(always)]
    unsafe fn dealloc_lam(self) {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), NodePtrTag::LamPtr);
        let ptr = self.ptr() as *mut u8;
        unsafe {
            std::alloc::dealloc(ptr, std::alloc::Layout::new::<Lam>());
        }
    }

    #[inline(always)]
    unsafe fn dealloc_app(self) {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), NodePtrTag::AppPtr);
        let ptr = self.ptr() as *mut u8;
        unsafe {
            std::alloc::dealloc(ptr, std::alloc::Layout::new::<App>());
        }
    }

    #[inline(always)]
    unsafe fn dealloc_sup(self) {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), NodePtrTag::SupPtr);
        let ptr = self.ptr() as *mut u8;
        unsafe {
            std::alloc::dealloc(ptr, std::alloc::Layout::new::<Sup>());
        }
    }

    #[inline(always)]
    unsafe fn dealloc_dup(self) {
        debug_assert_ne!(self.ptr(), ptr::null_mut());
        debug_assert_eq!(self.tag(), NodePtrTag::DupPtr);
        let ptr = self.ptr() as *mut u8;
        unsafe {
            std::alloc::dealloc(ptr, std::alloc::Layout::new::<Dup>());
        }
    }
}

/// A lambda node, e.g. `(λx e)`.
#[repr(C, align(8))]
struct Lam {
    x: FieldPtr,
    e: NodePtr,
}
const _: () = assert!(size_of::<Lam>() == 8 * 2);
const _: () = assert!(align_of::<Lam>() == 8);

/// An application node, e.g. `(e1 e2)`.
#[repr(C, align(8))]
struct App {
    e1: NodePtr,
    e2: NodePtr,
}
const _: () = assert!(size_of::<App>() == 8 * 2);
const _: () = assert!(align_of::<App>() == 8);

/// A superposition node, e.g. `#l{e1 e2}`.
#[repr(C, align(8))]
struct Sup {
    l: u64,
    e1: NodePtr,
    e2: NodePtr,
}
const _: () = assert!(size_of::<Sup>() == 8 * 3);
const _: () = assert!(align_of::<Sup>() == 8);

/// A duplication node, e.g. `dup #l{a b} = e;`
#[repr(C, align(8))]
struct Dup {
    l: u64,
    a: FieldPtr,
    b: FieldPtr,
    e: NodePtr,
}
const _: () = assert!(size_of::<Dup>() == 8 * 4);
const _: () = assert!(align_of::<Dup>() == 8);

impl Lam {
    unsafe fn alloc() -> NodePtr {
        let ptr = std::alloc::alloc(std::alloc::Layout::new::<Self>()) as *mut ();
        NodePtr::new(ptr, NodePtrTag::LamPtr)
    }
}

impl App {
    unsafe fn alloc() -> NodePtr {
        let ptr = std::alloc::alloc(std::alloc::Layout::new::<Self>()) as *mut ();
        NodePtr::new(ptr, NodePtrTag::AppPtr)
    }
}

impl Sup {
    unsafe fn alloc() -> NodePtr {
        let ptr = std::alloc::alloc(std::alloc::Layout::new::<Self>()) as *mut ();
        NodePtr::new(ptr, NodePtrTag::SupPtr)
    }
}

impl Dup {
    unsafe fn alloc() -> NodePtr {
        let ptr = std::alloc::alloc(std::alloc::Layout::new::<Self>()) as *mut ();
        NodePtr::new(ptr, NodePtrTag::DupPtr)
    }
}

// TODO: reducer that collects tasks and tries reordering them.
// TODO: do we really need the var to Lam/Dup pointers?
impl NodePtr {
    /// Reduce a graph to weak normal form.
    fn reduce(self) -> Self {
        match self.tag() {
            NodePtrTag::UnusedVar => self,
            NodePtrTag::LamPtr => self,
            NodePtrTag::AppPtr => {
                let app_ptr = self;
                let app = unsafe { self.read_app() };
                let app_e1 = app.e1.reduce();
                match app_e1.tag() {
                    NodePtrTag::UnusedVar => self,
                    NodePtrTag::LamPtr => app_lam_rule(app_ptr, app, app_e1),
                    NodePtrTag::AppPtr => self,
                    NodePtrTag::SupPtr => app_sup_rule(app_ptr, app, app_e1),
                    NodePtrTag::DupPtr => self,
                }
            }
            NodePtrTag::SupPtr => self,
            NodePtrTag::DupPtr => {
                let dup_ptr = self;
                let dup = unsafe { self.read_dup() };
                let dup_e = dup.e.reduce();
                match dup_e.tag() {
                    NodePtrTag::UnusedVar => self,
                    NodePtrTag::LamPtr => dup_lam_rule(dup_ptr, dup, dup_e),
                    NodePtrTag::AppPtr => self,
                    NodePtrTag::SupPtr => dup_sup_rule(dup_ptr, dup, dup_e),
                    NodePtrTag::DupPtr => self,
                }
            }
        }
    }

    /// Reduce a graph to strong normal form.
    fn normal(self: NodePtr) -> NodePtr {
        todo!()
    }
}

fn app_lam_rule(app_ptr: NodePtr, app: App, lam_x_e_ptr: NodePtr) -> NodePtr {
    // (λx e) e2
    // ---------- AppLam
    // x <- e2
    // e
    unsafe {
        app_ptr.dealloc_app();
        let lam = lam_x_e_ptr.read_lam();
        lam_x_e_ptr.dealloc_lam();
        // perform the substitution
        debug_assert_eq!(lam_x_e_ptr, lam.x.read());
        lam.x.write(app.e2);
        lam.e.reduce()
    }
}

fn app_sup_rule(app_sup_e3_ptr: NodePtr, app_sup_e3: App, sup_e1_e2_ptr: NodePtr) -> NodePtr {
    // #l{e1 e2} e3
    // ----------------- AppSup
    // dup #l{a b} = e3
    // #l{(e1 a) (e2 b)}
    unsafe {
        // TODO: reuse the app and sup nodes?
        app_sup_e3_ptr.dealloc_app();
        let sup_e1_e2 = sup_e1_e2_ptr.read_sup();
        sup_e1_e2_ptr.dealloc_sup();

        let dup_a_b_ptr = Dup::alloc();
        let sup_app_app_ptr = Sup::alloc();
        let app_e1_a_ptr = App::alloc();
        let app_e2_b_ptr = App::alloc();

        // dup #l{a b} = e3
        dup_a_b_ptr.write_dup(Dup {
            l: sup_e1_e2.l,
            a: app_e1_a_ptr.app_e2_field_ptr(),
            b: app_e2_b_ptr.app_e2_field_ptr(),
            e: app_sup_e3.e2,
        });

        // #l{(e1 a) (e2 b)}
        sup_app_app_ptr.write_sup(Sup {
            l: sup_e1_e2.l,
            e1: app_e1_a_ptr,
            e2: app_e2_b_ptr,
        });
        app_e1_a_ptr.write_app(App {
            e1: sup_e1_e2.e1,
            e2: dup_a_b_ptr,
        });
        app_e2_b_ptr.write_app(App {
            e1: sup_e1_e2.e2,
            e2: dup_a_b_ptr,
        });

        dup_a_b_ptr.reduce();
        sup_app_app_ptr.reduce()
    }
}

fn dup_lam_rule(dup_a_b_ptr: NodePtr, dup_a_b: Dup, lam_x_e_ptr: NodePtr) -> NodePtr {
    // dup #l{a b} = (λx e)
    // ------------------ DupLam
    // a <- (λx1 c)
    // b <- (λx2 d)
    // x <- #l{x1,x2}
    // dup #l{c d} = e
    unsafe {
        // TODO: reuse the dup node?
        dup_a_b_ptr.dealloc_dup();
        let lam_x_e = lam_x_e_ptr.read_lam();
        lam_x_e_ptr.dealloc_lam();

        let lam_x1_c_ptr = if dup_a_b.a.is_unbound_var() {
            NodePtr::new_unbound_var()
        } else {
            Lam::alloc()
        };
        let lam_x2_d_ptr = if dup_a_b.b.is_unbound_var() {
            NodePtr::new_unbound_var()
        } else {
            Lam::alloc()
        };
        let sup_x1_x2_ptr = if lam_x_e.x.is_unbound_var() {
            NodePtr::new_unbound_var()
        } else {
            Sup::alloc()
        };
        let dup_c_d_ptr = Dup::alloc();

        // a <- (λx1 c)
        dup_a_b.a.write(lam_x1_c_ptr);
        lam_x1_c_ptr.write_lam(Lam {
            x: sup_x1_x2_ptr.sup_e1_field_ptr(),
            e: dup_c_d_ptr,
        });

        // b <- (λx2 d)
        dup_a_b.b.write(lam_x2_d_ptr);
        lam_x2_d_ptr.write_lam(Lam {
            x: sup_x1_x2_ptr.sup_e2_field_ptr(),
            e: dup_c_d_ptr,
        });

        // x <- #l{x1,x2}
        lam_x_e.x.write(sup_x1_x2_ptr);
        sup_x1_x2_ptr.write_sup(Sup {
            l: dup_a_b.l,
            e1: lam_x1_c_ptr,
            e2: lam_x2_d_ptr,
        });

        // dup #l{c d} = e
        dup_c_d_ptr.write_dup(Dup {
            l: dup_a_b.l,
            a: lam_x1_c_ptr.lam_e_field_ptr(),
            b: lam_x2_d_ptr.lam_e_field_ptr(),
            e: lam_x_e.e,
        });

        dup_c_d_ptr.reduce()
    }
}

fn dup_sup_rule(dup_a_b_ptr: NodePtr, dup_a_b: Dup, sup_e1_e2_ptr: NodePtr) {
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
    unsafe {
        // TODO: reuse the dup and sup nodes?
        dup_a_b_ptr.dealloc_dup();
        let sup_e1_e2 = sup_e1_e2_ptr.read_sup();
        sup_e1_e2_ptr.dealloc_sup();
        if dup_a_b.l == sup_e1_e2.l {
            // a <- e1
            dup_a_b.a.write(sup_e1_e2.e1);
            // b <- e2
            dup_a_b.b.write(sup_e1_e2.e2);
        } else {
            let l = dup_a_b.l;
            let m = sup_e1_e2.l;
            let sup_a1_a2_ptr = if dup_a_b.a.is_unbound_var() {
                NodePtr::new_unbound_var()
            } else {
                Sup::alloc()
            };
            let sup_b1_b2_ptr = if dup_a_b.b.is_unbound_var() {
                NodePtr::new_unbound_var()
            } else {
                Sup::alloc()
            };
            let dup_a1_b1_ptr = Dup::alloc();
            let dup_a2_b2_ptr = Dup::alloc();
            // a <- #m{a1 a2}
            dup_a_b.a.write(sup_a1_a2_ptr);
            sup_a1_a2_ptr.write_sup(Sup {
                l: m,
                e1: dup_a1_b1_ptr,
                e2: dup_a2_b2_ptr,
            });
            // b <- #m{b1 b2}
            dup_a_b.b.write(sup_b1_b2_ptr);
            sup_b1_b2_ptr.write_sup(Sup {
                l: m,
                e1: dup_a1_b1_ptr,
                e2: dup_a2_b2_ptr,
            });
            // dup #l{a1 b1} = e1
            dup_a1_b1_ptr.write_dup(Dup {
                l,
                a: sup_a1_a2_ptr.sup_e1_field_ptr(),
                b: sup_b1_b2_ptr.sup_e1_field_ptr(),
                e: sup_e1_e2.e1,
            });
            // dup #l{a2 b2} = e2
            dup_a2_b2_ptr.write_dup(Dup {
                l,
                a: sup_a1_a2_ptr.sup_e2_field_ptr(),
                b: sup_b1_b2_ptr.sup_e2_field_ptr(),
                e: sup_e1_e2.e2,
            });

            dup_a1_b1_ptr.reduce();
            dup_a2_b2_ptr.reduce();
        }
    }
}

/// An owned term graph.
pub struct TermGraph(NodePtr);

impl Drop for TermGraph {
    fn drop(&mut self) {
        todo!()
    }
}

impl TermGraph {
    /// Consumes the `TermGraph` and returns the underlying `NodePtr`.
    ///
    /// After calling this function, the caller is responsible for the memory
    /// previously managed by the `TermGraph`.
    fn into_field(self) -> NodePtr {
        let field = self.0;
        std::mem::forget(self);
        field
    }

    /// Reduce a term to weak normal form.
    pub fn reduce(self) -> Self {
        TermGraph(self.into_field().reduce())
    }

    /// Reduce a term to strong normal form.
    pub fn normal(self) -> Self {
        TermGraph(self.into_field().normal())
    }
}
