type Ident = String;

fn gen_ident(n: u64) -> Ident {
    format!("v{}", n)
}

#[derive(PartialEq, Clone, Debug)]
enum Kind {
    Star,
    Fun(Box<Kind>, Box<Kind>),
}

#[derive(PartialEq, Clone)]
enum Type {
    Var(TyVar),
    Con(TyCon),
    App(Box<Type>, Box<Type>),
    Gen(u64),
}

#[derive(PartialEq, Clone)]
struct TyVar {
    ident: Ident,
    kind: Kind,
}

#[derive(PartialEq, Clone)]
struct TyCon {
    ident: Ident,
    kind: Kind,
}

fn unit() -> Type {
    Type::Con(TyCon {
        ident: "()".into(),
        kind: Kind::Star,
    })
}

fn char() -> Type {
    Type::Con(TyCon {
        ident: "Char".into(),
        kind: Kind::Star,
    })
}

fn int() -> Type {
    Type::Con(TyCon {
        ident: "Int".into(),
        kind: Kind::Star,
    })
}

fn integer() -> Type {
    Type::Con(TyCon {
        ident: "Integer".into(),
        kind: Kind::Star,
    })
}

fn float() -> Type {
    Type::Con(TyCon {
        ident: "Float".into(),
        kind: Kind::Star,
    })
}

fn double() -> Type {
    Type::Con(TyCon {
        ident: "Double".into(),
        kind: Kind::Star,
    })
}

fn list_con() -> Type {
    use self::Kind::*;
    let b = Box::new;
    Type::Con(TyCon {
        ident: "(->)".into(),
        kind: Fun(b(Star), b(Star)),
    })
}

fn arrow_con() -> Type {
    use self::Kind::*;
    let b = Box::new;
    Type::Con(TyCon {
        ident: "(->)".into(),
        kind: Fun(b(Star), b(Fun(b(Star), b(Star)))),
    })
}

fn pair_con() -> Type {
    use self::Kind::*;
    let b = Box::new;
    Type::Con(TyCon {
        ident: "(,)".into(),
        kind: Fun(b(Star), b(Fun(b(Star), b(Star)))),
    })
}

fn list(elem: Type) -> Type {
    use Type::*;
    let b = Box::new;
    App(b(list_con()), b(elem))
}

fn arrow(from: Type, to: Type) -> Type {
    use Type::*;
    let b = Box::new;
    App(b(App(b(arrow_con()), b(from))), b(to))
}

fn pair(left: Type, right: Type) -> Type {
    use Type::*;
    let b = Box::new;
    App(b(App(b(pair_con()), b(left))), b(right))
}

trait HasKind {
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

type Subst = Vec<(TyVar, Type)>;

fn null_subst() -> Subst {
    vec![]
}

fn single_subst(from: TyVar, to: Type) -> Subst {
    assert_eq!(from.kind(), to.kind());
    vec![(from, to)]
}

trait Types {
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

fn compose_subst(s1: &Subst, s2: &Subst) -> Subst {
    s2.iter()
        .map(|(u, t)| (u.clone(), t.apply(s1)))
        .chain(s1.clone())
        .collect()
}

fn merge_subst(s1: &Subst, s2: &Subst) -> Option<Subst> {
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
        Some(s1.iter().chain(s2.iter()).cloned().collect())
    } else {
        None
    }
}

fn most_general_unifier(a: &Type, b: &Type) -> Option<Subst> {
    match (a, b) {
        (Type::App(f1, p1), Type::App(f2, p2)) => {
            let s1 = most_general_unifier(f1, f2)?;
            let s2 = most_general_unifier(&p1.apply(&s1), &p2.apply(&s1))?;
            Some(compose_subst(&s1, &s2))
        },
        (Type::Var(i), t) | (t, Type::Var(i)) => var_bind(i, t),
        (Type::Con(c1), Type::Con(c2)) if c1 == c2 => Some(null_subst()),
        _ => None,
    }
}

fn var_bind(var: &TyVar, ty: &Type) -> Option<Subst> {
    None
}

fn main() {}