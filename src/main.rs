use std::{
    ops::Deref,
    iter::once,
};

pub type Ident = String;

pub fn gen_ident(n: u64) -> Ident {
    format!("v{}", n)
}

#[derive(PartialEq, Clone, Debug)]
pub enum Kind {
    Star,
    Fun(Box<Kind>, Box<Kind>),
}

#[derive(PartialEq, Clone)]
pub enum Type {
    Var(TyVar),
    Con(TyCon),
    App(Box<Type>, Box<Type>),
    Gen(u64),
}

#[derive(PartialEq, Clone)]
pub struct TyVar {
    ident: Ident,
    kind: Kind,
}

impl TyVar {
    pub fn new<I: Into<Ident>>(ident: I, kind: Kind) -> Self {
        TyVar {
            ident: ident.into(),
            kind,
        }
    }
}

#[derive(PartialEq, Clone)]
pub struct TyCon {
    ident: Ident,
    kind: Kind,
}

pub fn unit() -> Type {
    Type::Con(TyCon {
        ident: "()".into(),
        kind: Kind::Star,
    })
}

pub fn character() -> Type {
    Type::Con(TyCon {
        ident: "Char".into(),
        kind: Kind::Star,
    })
}

pub fn int() -> Type {
    Type::Con(TyCon {
        ident: "Int".into(),
        kind: Kind::Star,
    })
}

pub fn integer() -> Type {
    Type::Con(TyCon {
        ident: "Integer".into(),
        kind: Kind::Star,
    })
}

pub fn float() -> Type {
    Type::Con(TyCon {
        ident: "Float".into(),
        kind: Kind::Star,
    })
}

pub fn double() -> Type {
    Type::Con(TyCon {
        ident: "Double".into(),
        kind: Kind::Star,
    })
}

pub fn list_con() -> Type {
    use self::Kind::*;
    let b = Box::new;
    Type::Con(TyCon {
        ident: "(->)".into(),
        kind: Fun(b(Star), b(Star)),
    })
}

pub fn arrow_con() -> Type {
    use self::Kind::*;
    let b = Box::new;
    Type::Con(TyCon {
        ident: "(->)".into(),
        kind: Fun(b(Star), b(Fun(b(Star), b(Star)))),
    })
}

pub fn pair_con() -> Type {
    use self::Kind::*;
    let b = Box::new;
    Type::Con(TyCon {
        ident: "(,)".into(),
        kind: Fun(b(Star), b(Fun(b(Star), b(Star)))),
    })
}

pub fn list(elem: Type) -> Type {
    use Type::*;
    let b = Box::new;
    App(b(list_con()), b(elem))
}

pub fn arrow(from: Type, to: Type) -> Type {
    use Type::*;
    let b = Box::new;
    App(b(App(b(arrow_con()), b(from))), b(to))
}

pub fn pair(left: Type, right: Type) -> Type {
    use Type::*;
    let b = Box::new;
    App(b(App(b(pair_con()), b(left))), b(right))
}

pub trait HasKind {
    fn kind(&self) -> Kind;
}

impl HasKind for TyVar {
    fn kind(&self) -> Kind {
        self.kind.clone()
    }
}

impl HasKind for TyCon {
    fn kind(&self) -> Kind {
        self.kind.clone()
    }
}

impl HasKind for Type {
    fn kind(&self) -> Kind {
        use self::Type::*;
        match self {
            Var(v) => v.kind(),
            Con(c) => c.kind(),
            App(from, _) => match from.kind() {
                Kind::Fun(_, to) => *to,
                _ => panic!("Applying type to non-function doesn't yield kind."),
            },
            Gen(_) => panic!("Generic types don't have kinds."),
        }
    }
}

pub type Subst = Vec<(TyVar, Type)>;

pub fn null_subst() -> Subst {
    vec![]
}

pub fn single_subst(from: TyVar, to: Type) -> Subst {
    assert_eq!(from.kind(), to.kind());
    vec![(from, to)]
}

pub trait Types {
    fn apply(&self, s: &Subst) -> Self;
    fn ty_var(&self) -> Vec<TyVar>;
}

impl Types for Type {
    fn apply(&self, s: &Subst) -> Self {
        use self::Type::*;
        let b = Box::new;
        match self {
            Var(v) => s.iter()
                .find(|(k, _)| k == v)
                .map(|(_, v)| v.clone())
                .unwrap_or(Var(v.clone())),
            App(from, to) => App(b(from.apply(s)), b(to.apply(s))),
            _ => self.clone(),
        }
    }

    fn ty_var(&self) -> Vec<TyVar> {
        use self::Type::*;
        match self {
            Var(v) => vec![v.clone()],
            App(from, to) => {
                let mut vars = from.ty_var();
                for v in to.ty_var() {
                    if !vars.contains(&v) {
                        vars.push(v);
                    }
                }
                vars
            },
            _ => vec![],
        }
    }
}

impl<T: Types> Types for Vec<T> {
    fn apply(&self, s: &Subst) -> Self {
        self.iter().map(|t| t.apply(s)).collect()
    }

    fn ty_var(&self) -> Vec<TyVar> {
        let cs: Vec<_> = self.iter().flat_map(|t| t.ty_var()).collect();
        let mut result = vec![];
        for c in cs {
            if !result.contains(&c) {
                result.push(c);
            }
        }
        return result;
    }
}

pub fn compose_subst(s1: &Subst, s2: &Subst) -> Subst {
    s2.iter()
        .map(|(u, t)| (u.clone(), t.apply(s1)))
        .chain(s1.clone())
        .collect()
}

pub fn merge_subst(s1: &Subst, s2: &Subst) -> Result<Subst, String> {
    let s22: Vec<_> = s2.iter().map(|s| &s.0).collect();
    let mut res = vec![];
    for s in s1.iter().map(|s| s.0.clone()) {
        if s22.contains(&&s) {
            res.push(s);
        }
    }
    let agree = res
        .iter()
        .all(|v| Type::Var(v.clone()).apply(&s1) == Type::Var(v.clone()).apply(&s2));
    if agree {
        Ok(s1.iter().chain(s2.iter()).cloned().collect())
    } else {
        Err("Merge fails".into())
    }
}

pub fn most_general_unifier(a: &Type, b: &Type) -> Result<Subst, String> {
    use Type::*;
    match (a, b) {
        (App(f1, p1), App(f2, p2)) => {
            let s1 = most_general_unifier(f1, f2)?;
            let s2 = most_general_unifier(&p1.apply(&s1), &p2.apply(&s1))?;
            Ok(compose_subst(&s1, &s2))
        },
        (Var(i), t) | (t, Var(i)) => var_bind(i, t),
        (Con(c1), Con(c2)) if c1 == c2 => Ok(null_subst()),
        _ => Err("Types don't unify".into()),
    }
}

pub fn var_bind(var: &TyVar, ty: &Type) -> Result<Subst, String> {
    if ty == &Type::Var(var.clone()) {
        return Ok(null_subst());
    }
    if ty.ty_var().contains(var) {
        return Err("Occurs check fails".into());
    }
    if var.kind() != ty.kind() {
        return Err("Kinds don't match".into());
    }
    Ok(single_subst(var.clone(), ty.clone()))
}

pub fn do_matching(a: &Type, b: &Type) -> Result<Subst, String> {
    use Type::*;
    match (a, b) {
        (App(f1, p1), App(f2, p2)) => {
            let f_subst = do_matching(f1, f2)?;
            let p_subst = do_matching(p1, p2)?;
            merge_subst(&f_subst, &p_subst)
        },
        (Var(i), t) if i.kind() == t.kind() => Ok(single_subst(i.clone(), t.clone())),
        (Con(c1), Con(c2)) if c1 == c2 => Ok(null_subst()),
        _ => Err("Types don't match".into())
    }
}

#[derive(PartialEq, Clone)]
pub struct Qual<T> {
    context: Vec<Pred>,
    head: T,
}

#[derive(PartialEq, Clone)]
pub struct Pred {
    ident: Ident,
    ty: Type,
}

impl Pred {
    fn new<I: Into<Ident>>(ident: I, ty: Type) -> Self {
        Pred {
            ident: ident.into(),
            ty,
        }
    }
}

impl<T: Types> Types for Qual<T> {
    fn apply(&self, s: &Subst) -> Self {
        Qual {
            context: self.context.apply(s),
            head: self.head.apply(s),
        }
    }

    fn ty_var(&self) -> Vec<TyVar> {
        let mut res = self.context.ty_var();
        for t in self.head.ty_var() {
            if !res.contains(&t) {
                res.push(t);
            }
        }
        res
    }
}

impl Types for Pred {
    fn apply(&self, s: &Subst) -> Self {
        Pred {
            ident: self.ident.clone(),
            ty: self.ty.apply(s)
        }
    }

    fn ty_var(&self) -> Vec<TyVar> {
        self.ty.ty_var()
    }
}

pub fn most_general_unifier_pred(p1: &Pred, p2: &Pred) -> Result<Subst, String> {
    lift(most_general_unifier)(p1, p2)
}

pub fn do_matching_pred(p1: &Pred, p2: &Pred) -> Result<Subst, String> {
    lift(do_matching)(p1, p2)
}

pub fn lift<F>(f: F) -> impl Fn(&Pred, &Pred) -> Result<Subst, String>
    where F: Fn(&Type, &Type) -> Result<Subst, String>
{
    move |p1, p2| {
        if p1.ident == p2.ident {
            f(&p1.ty, &p2.ty)
        } else {
            Err("Classes differ".into())
        }
    }
}

pub type Class = (Vec<Ident>, Vec<Inst>);
pub type Inst = Qual<Pred>;

pub struct ClassEnv {
    classes: Box<Fn(&str) -> Option<Class>>,
    defaults: Vec<Type>,
}

impl ClassEnv {
    pub fn initial() -> Self {
        ClassEnv {
            classes: Box::new(|_| None),
            defaults: vec![integer(), double()],
        }
    }

    pub fn supers(&self, i: &Ident) -> Vec<Ident> {
        (self.classes)(i).unwrap().0
    }

    pub fn insts(&self, i: &Ident) -> Vec<Inst> {
        (self.classes)(i).unwrap().1
    }

    pub fn modify(self, ident: Ident, class: Class) -> Self {
        let classes = self.classes;
        ClassEnv {
            classes: Box::new(move |i| if i == &ident {
                Some(class.clone())
            } else {
                (classes)(i)
            }),
            defaults: self.defaults,
        }
    }
}

pub struct EnvTransformer(Box<Fn(ClassEnv) -> Option<ClassEnv>>);

impl Deref for EnvTransformer {
    type Target = Box<Fn(ClassEnv) -> Option<ClassEnv>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl EnvTransformer {
    fn seq(self, rhs: Self) -> Self {
        EnvTransformer(Box::new(move |env| rhs(self(env)?)))
    }
}

pub fn add_class<I>(i: I, is: Vec<Ident>) -> EnvTransformer
    where I: Into<Ident>,
{
    let i = i.into();
    EnvTransformer(Box::new(move |env| {
        if (env.classes)(&i).is_some() {
            return None;
        }
        if is.iter().any(|i| (env.classes)(i).is_none()) {
            return None;
        }
        Some(env.modify(i.clone(), (is.clone(), vec![])))
    }))
}

pub fn add_prelude_classes() -> EnvTransformer {
    add_core_classes().seq(add_num_classes())
}

pub fn add_core_classes() -> EnvTransformer {
    add_class("Eq", vec![])
        .seq(add_class("Ord", vec!["Eq".into()]))
        .seq(add_class("Show", vec![]))
        .seq(add_class("Read", vec![]))
        .seq(add_class("Bounded", vec![]))
        .seq(add_class("Enum", vec![]))
        .seq(add_class("Functor", vec![]))
        .seq(add_class("Monad", vec![]))
}

pub fn add_num_classes() -> EnvTransformer {
    add_class("Num", vec!["Eq".into(), "Show".into()])
        .seq(add_class("Real", vec!["Num".into(), "Ord".into()]))
        .seq(add_class("Fractional", vec!["Num".into()]))
        .seq(add_class("Integral", vec!["Real".into(), "Enum".into()]))
        .seq(add_class("RealFrac", vec!["Real".into(), "Fractional".into()]))
        .seq(add_class("Floating", vec!["Fractional".into()]))
        .seq(add_class("RealFloat", vec!["RealFrac".into(), "Floating".into()]))
}

pub fn add_inst(preds: Vec<Pred>, pred: Pred) -> EnvTransformer {
    EnvTransformer(Box::new(move |env| {
        if (env.classes)(&pred.ident).is_none() {
            return None;
        }
        let mut its = env.insts(&pred.ident);
        {
            let mut qs = its.iter().map(|i| &i.head);
            if qs.any(|p| overlap(&pred, &p)) {
                return None;
            }
        }
        its.insert(0, Inst {
            context: preds.clone(),
            head: pred.clone(),
        });
        let c = (env.supers(&pred.ident), its);
        Some(env.modify(pred.ident.clone(), c))
    }))
}

pub fn overlap(p1: &Pred, p2: &Pred) -> bool {
    most_general_unifier_pred(p1, p2).is_ok()
}

pub fn example_inst() -> EnvTransformer {
    use self::Type::*;
    use self::Kind::*;
    add_prelude_classes()
        .seq(add_inst(vec![], Pred::new("Ord", unit())))
        .seq(add_inst(vec![], Pred::new("Ord", character())))
        .seq(add_inst(vec![], Pred::new("Ord", integer())))
        .seq(add_inst(vec![
            Pred::new("Ord", Var(TyVar::new("a", Star))),
            Pred::new("Ord", Var(TyVar::new("b", Star))),
        ], Pred::new("Ord", pair(
            Var(TyVar::new("a", Star)),
            Var(TyVar::new("b", Star)),
        ))))
}

impl ClassEnv {
    pub fn by_super(&self, pred: &Pred) -> Vec<Pred> {
        once(pred.clone()).chain(
            self.supers(&pred.ident)
                .iter()
                .flat_map(|ident| self.by_super(&Pred {
                    ident: ident.clone(),
                    ty: pred.ty.clone(),
                }))
        ).collect()
    }

    pub fn by_inst(&self, pred: &Pred) -> Option<Vec<Pred>> {
        self.insts(&pred.ident)
            .iter()
            .flat_map(|p| {
                let u = do_matching_pred(&p.head, pred).ok()?;
                Some(
                    p.context.iter()
                        .map(|c| c.apply(&u))
                        .collect()
                )
            })
            .next()
    }

    pub fn entail(&self, ps: &[Pred], p: &Pred) -> bool {
        ps.iter()
            .map(|p| self.by_super(p))
            .any(|s| s.contains(p)) ||
        self.by_inst(p)
            .map(|qs|
                qs.iter()
                    .all(|p| self.entail(ps, p))
            )
            .unwrap_or(false)
    }
}

fn main() {}