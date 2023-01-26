use memoffset::offset_of;
use std::mem::{align_of, size_of};
use std::ptr;

/// A pointer to a `Field` inside of a `Lam`, `App`, `Sup`, or `Dup` node
/// representing a bound variable. When wrapped in an `Option`, i.e.
/// `Option<VarPtr>`, `None` represents an unused variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C, align(8))]
struct VarPtr(ptr::NonNull<Field>);
const _: () = assert!(size_of::<VarPtr>() == 8);
const _: () = assert!(align_of::<VarPtr>() == 8);

impl VarPtr {
    #[inline(always)]
    unsafe fn read(self) -> Field {
        self.0.as_ptr().read()
    }

    #[inline(always)]
    unsafe fn write(self, value: Field) {
        self.0.as_ptr().write(value)
    }
}

/// A field inside of a `Lam`, `App`, `Sup`, or `Dup` node representing either
/// an unbound variable or a tagged pointer to another node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C, align(8))]
struct Field(*mut ());
const _: () = assert!(size_of::<Field>() == 8);
const _: () = assert!(align_of::<Field>() == 8);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum FieldTag {
    UnusedVar = 0,
    LamPtr = 1,
    AppPtr = 2,
    SupPtr = 3,
    DupPtr = 4,
}
impl FieldTag {
    const MASK: u64 = 0b111;
}

impl Field {
    #[inline(always)]
    fn new(ptr: *mut (), tag: FieldTag) -> Self {
        const _: () = assert!(size_of::<*mut ()>() == size_of::<u64>());
        let value = ptr as u64 | tag as u64;
        let field = Field(value as *mut ());
        debug_assert_eq!(field.tag(), tag);
        debug_assert_eq!(field.ptr(), ptr);
        field
    }

    #[inline(always)]
    fn new_unused_var() -> Self {
        Self::new(ptr::null_mut(), FieldTag::UnusedVar)
    }

    #[inline(always)]
    fn tag(self) -> FieldTag {
        let value = (self.0 as u64 & FieldTag::MASK) as u8;
        unsafe { std::mem::transmute(value) }
    }

    #[inline(always)]
    fn ptr(self) -> *mut () {
        (self.0 as u64 & !FieldTag::MASK) as *mut ()
    }

    #[inline(always)]
    unsafe fn read_lam(self) -> Lam {
        debug_assert_eq!(self.tag(), FieldTag::LamPtr);
        let ptr = self.ptr() as *const Lam;
        unsafe { ptr.read() }
    }

    #[inline(always)]
    unsafe fn read_app(self) -> App {
        debug_assert_eq!(self.tag(), FieldTag::AppPtr);
        let ptr = self.ptr() as *const App;
        unsafe { ptr.read() }
    }

    #[inline(always)]
    unsafe fn read_sup(self) -> Sup {
        debug_assert_eq!(self.tag(), FieldTag::SupPtr);
        let ptr = self.ptr() as *const Sup;
        unsafe { ptr.read() }
    }

    #[inline(always)]
    unsafe fn read_dup(self) -> Dup {
        debug_assert_eq!(self.tag(), FieldTag::DupPtr);
        let ptr = self.ptr() as *const Dup;
        unsafe { ptr.read() }
    }

    fn dealloc_app(self) {
        todo!()
    }

    fn dealloc_lam(self) {
        todo!()
    }
}

/// A lambda node, e.g. `(λx e)`.
#[repr(C, align(8))]
struct Lam {
    x: Option<VarPtr>,
    e: Field,
}
const _: () = assert!(size_of::<Lam>() == 8 * 2);
const _: () = assert!(align_of::<Lam>() == 8);

/// An application node, e.g. `(e1 e2)`.
#[repr(C, align(8))]
struct App {
    e1: Field,
    e2: Field,
}
const _: () = assert!(size_of::<App>() == 8 * 2);
const _: () = assert!(align_of::<App>() == 8);

/// A superposition node, e.g. `#l{e1 e2}`.
#[repr(C, align(8))]
struct Sup {
    l: u64,
    e1: Field,
    e2: Field,
}
const _: () = assert!(size_of::<Sup>() == 8 * 3);
const _: () = assert!(align_of::<Sup>() == 8);

/// A duplication node, e.g. `dup #l{a b} = e;`
#[repr(C, align(8))]
struct Dup {
    l: u64,
    a: Option<VarPtr>,
    b: Option<VarPtr>,
    e: Field,
}
const _: () = assert!(size_of::<Dup>() == 8 * 4);
const _: () = assert!(align_of::<Dup>() == 8);

impl VarPtr {
    fn reduce(self) -> Self {
        todo!()
    }
}

// TODO: reducer that collects tasks and tries reordering them.
// TODO: do we really need the var to Lam/Dup pointers?
impl Field {
    /// Reduce a graph to weak normal form.
    fn reduce(self) -> Self {
        match self.tag() {
            FieldTag::UnusedVar => self,
            FieldTag::LamPtr => self,
            FieldTag::AppPtr => {
                let app_ptr = self;
                let app = unsafe { self.read_app() };
                let app_e1 = app.e1.reduce();
                match app_e1.tag() {
                    FieldTag::UnusedVar => self,

                    // (λx e) e2
                    // ---------- AppLam
                    // x <- e2
                    // e
                    FieldTag::LamPtr => {
                        let lam_ptr = app_e1;
                        app_ptr.dealloc_app();
                        let lam = unsafe { lam_ptr.read_lam() };
                        lam_ptr.dealloc_lam();
                        if let Some(x) = lam.x {
                            debug_assert_eq!(lam_ptr, unsafe { x.read() });
                            // perform the substitution
                            unsafe { x.write(app.e2) };
                        }
                        lam.e.reduce()
                    }

                    FieldTag::AppPtr => self,

                    // #l{e1 e2} e3
                    // ----------------- AppSup
                    // dup #l{a b} = e3
                    // #l{(e1 a) (e2 b)}
                    FieldTag::SupPtr => {
                        let sup_ptr = app_e1;
                        let sup = unsafe { sup_ptr.read_sup() };
                        let l = sup.l;
                        let e1 = sup.e1;
                        let e2 = sup.e2;
                        let e3 = app.e2;
                        let mut dup_box = Box::new(Dup {
                            l,
                            a: None,
                            b: None,
                            e: e3,
                        });
                        let dup_raw_ptr = &*dup_box as *const _ as *mut ();
                        let dup_ptr = Field::new(dup_raw_ptr, FieldTag::DupPtr);
                        let e1_a_app_box = Box::new(App {
                            e1: e1,
                            e2: dup_ptr,
                        });
                        let e2_b_app_box = Box::new(App {
                            e1: e2,
                            e2: dup_ptr,
                        });
                        let a_var_raw_ptr = &e1_a_app_box.e2 as *const _ as *mut _;
                        let b_var_raw_ptr = &e2_b_app_box.e2 as *const _ as *mut _;
                        dup_box.a = Some(VarPtr(ptr::NonNull::new(a_var_raw_ptr).unwrap()));
                        dup_box.b = Some(VarPtr(ptr::NonNull::new(b_var_raw_ptr).unwrap()));
                        Box::leak(dup_box);
                        let e1_a_app_raw_ptr = Box::into_raw(e1_a_app_box);
                        let e2_b_app_raw_ptr = Box::into_raw(e2_b_app_box);
                        let e1_a_app_ptr =
                            Field::new(e1_a_app_raw_ptr as *mut (), FieldTag::AppPtr);
                        let e2_b_app_ptr =
                            Field::new(e2_b_app_raw_ptr as *mut (), FieldTag::AppPtr);
                        dup_ptr.reduce();
                        e1_a_app_ptr.reduce();
                        e2_b_app_ptr.reduce();
                        sup_ptr
                    }

                    FieldTag::DupPtr => unreachable!(), // I think?
                }
            }
            FieldTag::SupPtr => todo!(),
            FieldTag::DupPtr => {
                // `self` is a var pointing to the binding Dup node.
                todo!()
            }
        }
    }

    /// Reduce a graph to strong normal form.
    fn normal(self: Field) -> Field {
        todo!()
    }
}

/// An owned term graph.
pub struct TermGraph(Field);

impl Drop for TermGraph {
    fn drop(&mut self) {
        todo!()
    }
}

impl TermGraph {
    /// Consumes the `TermGraph` and returns the underlying `Field`.
    ///
    /// After calling this function, the caller is responsible for the memory
    /// previously managed by the `TermGraph`.
    fn into_field(self) -> Field {
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
