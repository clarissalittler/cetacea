//! The theory: a signature plus the theorems admitted by definitional
//! principles.
//!
//! A theory only grows. Every extension is conservative except user
//! axioms, which are tagged, and datatype packages, which are trusted
//! code and tagged with the datatype's name.

use std::collections::{BTreeMap, BTreeSet};

use crate::error::{bail, Result};
use crate::logic::declare_logic;
use crate::name::Name;
use crate::signature::{base_signature, Signature};
use crate::term::{Term, TermView};
use crate::thm::{Tags, Thm};
use crate::types::Type;

pub const MEM_SET_OF: &str = "mem_setOf";
pub const SET_EXT: &str = "set_ext";

#[derive(Clone, Debug)]
pub struct DatatypeSpec {
    pub name: Name,
    pub params: Vec<Name>,
    pub ctors: Vec<CtorSpec>,
}

#[derive(Clone, Debug)]
pub struct CtorSpec {
    pub name: Name,
    pub args: Vec<Type>,
}

#[derive(Clone, Debug)]
pub struct DatatypeInfo {
    pub name: Name,
    pub params: Vec<Name>,
    pub ctors: Vec<CtorInfo>,
    /// `forall v. (exists args. v = c1 args) \/ ...`
    pub cases: Thm,
    /// `forall P. step_1 -> ... -> step_n -> forall v. P v`
    pub induction: Thm,
    /// One theorem per ordered pair of distinct constructors.
    pub distinct: Vec<Thm>,
}

#[derive(Clone, Debug)]
pub struct CtorInfo {
    pub name: Name,
    pub args: Vec<Type>,
    /// Which arguments are recursive occurrences of the datatype.
    pub recursive: Vec<bool>,
    /// `forall xs ys. c xs = c ys -> x1 = y1 /\ ...`, absent for nullary
    /// constructors.
    pub injective: Option<Thm>,
}

impl DatatypeInfo {
    pub fn ctor(&self, name: &Name) -> Option<&CtorInfo> {
        self.ctors.iter().find(|ctor| &ctor.name == name)
    }

    /// The datatype at its generic parameters.
    pub fn generic_type(&self) -> Type {
        Type::con(
            self.name.clone(),
            self.params.iter().map(|p| Type::var(p.clone())).collect(),
        )
    }
}

/// One function of a recursive definition group.
#[derive(Clone, Debug)]
pub struct RecFunSpec {
    pub name: Name,
    /// Index of the argument the function recurses on.
    pub rec_arg: usize,
    /// Closed equations of the form
    /// `forall vars. f a1 .. (c xs) .. an = rhs`, one per constructor.
    pub equations: Vec<Term>,
}

#[derive(Clone, Debug)]
pub struct Theory {
    sig: Signature,
    theorems: BTreeMap<Name, Thm>,
    definitions: BTreeMap<Name, Thm>,
    datatypes: BTreeMap<Name, DatatypeInfo>,
    ctor_owner: BTreeMap<Name, Name>,
    defined: BTreeSet<Name>,
}

impl Default for Theory {
    fn default() -> Theory {
        Theory::new()
    }
}

impl Theory {
    /// The base theory: `Prop`, functions, the logical constants, and
    /// `Set` with its two principles.
    pub fn new() -> Theory {
        let mut sig = base_signature();
        declare_logic(&mut sig);
        let mut theory = Theory {
            sig,
            theorems: BTreeMap::new(),
            definitions: BTreeMap::new(),
            datatypes: BTreeMap::new(),
            ctor_owner: BTreeMap::new(),
            defined: BTreeSet::new(),
        };
        theory.declare_set_principles();
        theory
    }

    fn declare_set_principles(&mut self) {
        let a = Type::var("A");
        let pred_ty = Type::fun(a.clone(), Type::prop());
        let p = Term::free("P", pred_ty);
        let x = Term::free("x", a.clone());
        let px = Term::app(&p, &x).expect("typed");
        let mem_set_of = Term::eq(
            &Term::mem(&x, &Term::set_of(&p).expect("typed")).expect("typed"),
            &px,
        )
        .expect("typed");
        let mem_set_of = Term::foralls(&[p, x.clone()], &mem_set_of).expect("typed");
        self.theorems.insert(
            Name::new(MEM_SET_OF),
            Thm::new(vec![], mem_set_of, Tags::none()),
        );

        let s = Term::free("S", Type::set(a.clone()));
        let t = Term::free("T", Type::set(a));
        let pointwise = Term::forall(
            &x,
            &Term::eq(
                &Term::mem(&x, &s).expect("typed"),
                &Term::mem(&x, &t).expect("typed"),
            )
            .expect("typed"),
        )
        .expect("typed");
        let ext = Term::imp(&pointwise, &Term::eq(&s, &t).expect("typed")).expect("typed");
        let ext = Term::foralls(&[s, t], &ext).expect("typed");
        self.theorems
            .insert(Name::new(SET_EXT), Thm::new(vec![], ext, Tags::none()));
    }

    pub fn signature(&self) -> &Signature {
        &self.sig
    }

    /// A constant at a type instance.
    pub fn constant(&self, name: impl Into<Name>, ty: Type) -> Result<Term> {
        Term::constant(&self.sig, name, ty)
    }

    /// A constant at its declared generic type.
    pub fn generic_constant(&self, name: impl Into<Name>) -> Result<Term> {
        let name = name.into();
        let Some(ty) = self.sig.const_type(&name) else {
            bail!("constant", "unknown constant `{name}`");
        };
        Term::constant(&self.sig, name, ty.clone())
    }

    /// A named theorem: an axiom, a set principle, a datatype principle,
    /// or a recursive-function equation.
    pub fn theorem(&self, name: &str) -> Option<&Thm> {
        self.theorems.get(&Name::new(name))
    }

    pub fn theorems(&self) -> impl Iterator<Item = (&Name, &Thm)> {
        self.theorems.iter()
    }

    /// The defining equation `|- c = body` of a defined constant.
    pub fn definition(&self, name: &str) -> Option<&Thm> {
        self.definitions.get(&Name::new(name))
    }

    pub fn datatype(&self, name: &str) -> Option<&DatatypeInfo> {
        self.datatypes.get(&Name::new(name))
    }

    /// The datatype a constructor belongs to.
    pub fn ctor_datatype(&self, ctor: &Name) -> Option<&DatatypeInfo> {
        self.ctor_owner
            .get(ctor)
            .and_then(|owner| self.datatypes.get(owner))
    }

    pub fn is_defined(&self, name: &Name) -> bool {
        self.defined.contains(name)
    }

    /// Declares an opaque type constructor.
    pub fn new_type(&mut self, name: impl Into<Name>, arity: usize) -> Result<()> {
        self.sig.add_type(name.into(), arity)
    }

    /// Declares an uninterpreted constant.
    pub fn new_const(&mut self, name: impl Into<Name>, ty: Type) -> Result<()> {
        self.sig.add_const(name.into(), ty)
    }

    /// Defines a new constant `c := body` and returns `|- c = body`.
    ///
    /// The body must be closed, and every type variable in the body
    /// must occur in its type; otherwise the definition would let a
    /// constant of type `Prop` secretly depend on a type, which is
    /// unsound in HOL.
    pub fn new_def(&mut self, name: impl Into<Name>, body: &Term) -> Result<Thm> {
        let name = name.into();
        body.require_closed("new_def")?;
        if self.sig.has_const(&name) {
            bail!("new_def", "constant `{name}` is already declared");
        }
        if let Some((var, _)) = body.free_vars().into_iter().next() {
            bail!(
                "new_def",
                "the body of `{name}` mentions the free variable `{var}`; definitions must be closed"
            );
        }
        self.sig.check_type(body.ty())?;
        let mut body_vars = BTreeSet::new();
        body.type_vars(&mut body_vars);
        let mut type_vars = BTreeSet::new();
        body.ty().type_vars(&mut type_vars);
        if let Some(extra) = body_vars.difference(&type_vars).next() {
            bail!(
                "new_def",
                "the body of `{name}` mentions the type variable `{extra}`, which does not occur in its type `{}`",
                body.ty()
            );
        }
        self.sig.add_const(name.clone(), body.ty().clone())?;
        let c = Term::constant_unchecked(name.clone(), body.ty().clone());
        let thm = Thm::new(vec![], Term::eq(&c, body)?, Tags::none());
        self.definitions.insert(name.clone(), thm.clone());
        self.defined.insert(name);
        Ok(thm)
    }

    /// Admits `prop` as an axiom tagged with `name`.
    pub fn new_axiom(&mut self, name: impl Into<Name>, prop: &Term) -> Result<Thm> {
        let name = name.into();
        prop.require_closed("new_axiom")?;
        if !prop.ty().is_prop() {
            bail!("new_axiom", "`{prop}` is not a proposition");
        }
        if self.theorems.contains_key(&name) {
            bail!("new_axiom", "a theorem named `{name}` already exists");
        }
        let thm = Thm::new(vec![], prop.clone(), Tags::axiom(name.clone()));
        self.theorems.insert(name, thm.clone());
        Ok(thm)
    }

    /// Declares a datatype and admits its principles, tagged with the
    /// datatype's name: constructor injectivity, constructor
    /// distinctness, case analysis, and induction.
    ///
    /// Recursive occurrences of the datatype must be direct constructor
    /// arguments at exactly the declared parameters. At least one
    /// constructor must be non-recursive, so the type is inhabited.
    pub fn new_datatype(&mut self, spec: &DatatypeSpec) -> Result<DatatypeInfo> {
        let name = spec.name.clone();
        if self.sig.has_type(&name) {
            bail!("new_datatype", "type `{name}` is already declared");
        }
        let mut seen_params = BTreeSet::new();
        for param in &spec.params {
            if !seen_params.insert(param.clone()) {
                bail!("new_datatype", "duplicate type parameter `{param}`");
            }
        }
        if spec.ctors.is_empty() {
            bail!("new_datatype", "datatype `{name}` has no constructors");
        }
        let generic = Type::con(
            name.clone(),
            spec.params.iter().map(|p| Type::var(p.clone())).collect(),
        );
        let mut ctor_names = BTreeSet::new();
        let mut ctors = Vec::new();
        let mut has_base = false;
        for ctor in &spec.ctors {
            if !ctor_names.insert(ctor.name.clone()) {
                bail!("new_datatype", "duplicate constructor `{}`", ctor.name);
            }
            if self.sig.has_const(&ctor.name) {
                bail!(
                    "new_datatype",
                    "constructor `{}` clashes with an existing constant",
                    ctor.name
                );
            }
            let mut recursive = Vec::new();
            for arg in &ctor.args {
                let is_rec = arg == &generic;
                if !is_rec {
                    self.check_datatype_arg(&name, &spec.params, arg, &ctor.name)?;
                }
                recursive.push(is_rec);
            }
            if recursive.iter().all(|r| !r) {
                has_base = true;
            }
            ctors.push((ctor.clone(), recursive));
        }
        if !has_base {
            bail!(
                "new_datatype",
                "datatype `{name}` has no non-recursive constructor, so it would be empty"
            );
        }

        self.sig.add_type(name.clone(), spec.params.len())?;
        for (ctor, _) in &ctors {
            self.sig
                .add_const(ctor.name.clone(), Type::funs(&ctor.args, generic.clone()))?;
        }

        let tags = Tags::datatype(name.clone());
        let ctor_term = |ctor: &CtorSpec| {
            Term::constant_unchecked(ctor.name.clone(), Type::funs(&ctor.args, generic.clone()))
        };
        let vars = |ctor: &CtorSpec, prefix: &str| -> Vec<Term> {
            ctor.args
                .iter()
                .enumerate()
                .map(|(i, ty)| Term::free(format!("{prefix}{}", i + 1), ty.clone()))
                .collect()
        };

        let mut infos = Vec::new();
        for (ctor, recursive) in &ctors {
            let xs = vars(ctor, "x");
            let ys = vars(ctor, "y");
            let injective = if ctor.args.is_empty() {
                None
            } else {
                let lhs = Term::apps(&ctor_term(ctor), &xs)?;
                let rhs = Term::apps(&ctor_term(ctor), &ys)?;
                let mut conj: Option<Term> = None;
                for (x, y) in xs.iter().zip(&ys).rev() {
                    let eq = Term::eq(x, y)?;
                    conj = Some(match conj {
                        None => eq,
                        Some(rest) => Term::and(&eq, &rest)?,
                    });
                }
                let body = Term::imp(&Term::eq(&lhs, &rhs)?, &conj.expect("non-empty"))?;
                let all_vars: Vec<Term> = xs.iter().chain(&ys).cloned().collect();
                let thm = Thm::new(vec![], Term::foralls(&all_vars, &body)?, tags.clone());
                self.theorems
                    .insert(Name::new(&format!("{name}.{}.inj", ctor.name)), thm.clone());
                Some(thm)
            };
            infos.push(CtorInfo {
                name: ctor.name.clone(),
                args: ctor.args.clone(),
                recursive: recursive.clone(),
                injective,
            });
        }

        let mut distinct = Vec::new();
        for (i, (ci, _)) in ctors.iter().enumerate() {
            for (cj, _) in ctors.iter().skip(i + 1) {
                let xs = vars(ci, "x");
                let ys = vars(cj, "y");
                let lhs = Term::apps(&ctor_term(ci), &xs)?;
                let rhs = Term::apps(&ctor_term(cj), &ys)?;
                let body = Term::imp(&Term::eq(&lhs, &rhs)?, &Term::false_())?;
                let all_vars: Vec<Term> = xs.iter().chain(&ys).cloned().collect();
                let thm = Thm::new(vec![], Term::foralls(&all_vars, &body)?, tags.clone());
                self.theorems.insert(
                    Name::new(&format!("{name}.{}.{}.distinct", ci.name, cj.name)),
                    thm.clone(),
                );
                distinct.push(thm);
            }
        }

        let v = Term::free("v", generic.clone());
        let mut disjuncts = Vec::new();
        for (ctor, _) in &ctors {
            let xs = vars(ctor, "x");
            let applied = Term::apps(&ctor_term(ctor), &xs)?;
            disjuncts.push(Term::existss(&xs, &Term::eq(&v, &applied)?)?);
        }
        let mut cases_body = disjuncts.pop().expect("non-empty");
        while let Some(disjunct) = disjuncts.pop() {
            cases_body = Term::or(&disjunct, &cases_body)?;
        }
        let cases = Thm::new(vec![], Term::forall(&v, &cases_body)?, tags.clone());
        self.theorems
            .insert(Name::new(&format!("{name}.cases")), cases.clone());

        let p = Term::free("P", Type::fun(generic.clone(), Type::prop()));
        let mut steps = Vec::new();
        for (ctor, recursive) in &ctors {
            let xs = vars(ctor, "x");
            let applied = Term::apps(&ctor_term(ctor), &xs)?;
            let hyps: Vec<Term> = xs
                .iter()
                .zip(recursive)
                .filter(|(_, r)| **r)
                .map(|(x, _)| Term::app(&p, x))
                .collect::<Result<_>>()?;
            let step = Term::imps(&hyps, &Term::app(&p, &applied)?)?;
            steps.push(Term::foralls(&xs, &step)?);
        }
        let conclusion = Term::forall(&v, &Term::app(&p, &v)?)?;
        let induction_body = Term::imps(&steps, &conclusion)?;
        let induction = Thm::new(vec![], Term::forall(&p, &induction_body)?, tags);
        self.theorems
            .insert(Name::new(&format!("{name}.induct")), induction.clone());

        let info = DatatypeInfo {
            name: name.clone(),
            params: spec.params.clone(),
            ctors: infos,
            cases,
            induction,
            distinct,
        };
        for ctor in &spec.ctors {
            self.ctor_owner.insert(ctor.name.clone(), name.clone());
        }
        self.datatypes.insert(name, info.clone());
        Ok(info)
    }

    fn check_datatype_arg(
        &self,
        name: &Name,
        params: &[Name],
        ty: &Type,
        ctor: &Name,
    ) -> Result<()> {
        match ty {
            Type::Var(v) => {
                if !params.contains(v) {
                    bail!(
                        "new_datatype",
                        "constructor `{ctor}` mentions the undeclared type variable `{v}`"
                    );
                }
                Ok(())
            }
            Type::Con(con, args) => {
                if con == name {
                    bail!(
                        "new_datatype",
                        "constructor `{ctor}` uses `{name}` in a nested or negative position `{ty}`; only direct recursive arguments are supported"
                    );
                }
                match self.sig.type_arity(con) {
                    None => bail!(
                        "new_datatype",
                        "constructor `{ctor}` mentions the unknown type `{con}`"
                    ),
                    Some(arity) if arity != args.len() => bail!(
                        "new_datatype",
                        "constructor `{ctor}` applies `{con}` to {} argument(s), but it takes {arity}",
                        args.len()
                    ),
                    Some(_) => {}
                }
                for arg in args {
                    self.check_datatype_arg(name, params, arg, ctor)?;
                }
                Ok(())
            }
        }
    }

    /// Admits the defining equations of a group of structurally
    /// recursive functions whose constants were declared with
    /// [`Theory::new_const`].
    ///
    /// Each function recurses on one argument. Every equation matches one
    /// constructor at that argument, with variables everywhere else, and
    /// every call to a group function in a right-hand side passes a
    /// recursive constructor variable at that function's recursive
    /// argument. Group constants may not occur unapplied.
    pub fn new_recfun(&mut self, group: &[RecFunSpec]) -> Result<Vec<Thm>> {
        let mut group_names: BTreeMap<Name, usize> = BTreeMap::new();
        for spec in group {
            if !self.sig.has_const(&spec.name) {
                bail!("new_recfun", "constant `{}` is not declared", spec.name);
            }
            if self.defined.contains(&spec.name) {
                bail!("new_recfun", "constant `{}` is already defined", spec.name);
            }
            if group_names
                .insert(spec.name.clone(), spec.rec_arg)
                .is_some()
            {
                bail!("new_recfun", "`{}` appears twice in the group", spec.name);
            }
        }
        let mut admitted = Vec::new();
        for spec in group {
            admitted.extend(self.check_recfun(spec, &group_names)?);
        }
        for spec in group {
            self.defined.insert(spec.name.clone());
        }
        for (name, thm) in &admitted {
            self.theorems.insert(name.clone(), thm.clone());
        }
        Ok(admitted.into_iter().map(|(_, thm)| thm).collect())
    }

    fn check_recfun(
        &self,
        spec: &RecFunSpec,
        group: &BTreeMap<Name, usize>,
    ) -> Result<Vec<(Name, Thm)>> {
        let f = &spec.name;
        let f_ty = self.sig.const_type(f).expect("checked").clone();
        let (doms, _) = f_ty.strip_fun();
        if spec.rec_arg >= doms.len() {
            bail!(
                "new_recfun",
                "`{f}` has {} argument(s), so it cannot recurse on argument {}",
                doms.len(),
                spec.rec_arg
            );
        }
        let rec_ty = doms[spec.rec_arg].clone();
        let Type::Con(dt_name, _) = &rec_ty else {
            bail!(
                "new_recfun",
                "`{f}` recurses on an argument of type `{rec_ty}`, which is not a datatype"
            );
        };
        let Some(datatype) = self.datatypes.get(dt_name) else {
            bail!(
                "new_recfun",
                "`{f}` recurses on an argument of type `{rec_ty}`, which is not a datatype"
            );
        };
        if spec.equations.is_empty() {
            bail!("new_recfun", "`{f}` has no defining equations");
        }

        let mut covered: BTreeSet<Name> = BTreeSet::new();
        let mut arity: Option<usize> = None;
        let mut out = Vec::new();
        for equation in &spec.equations {
            equation.require_closed("new_recfun")?;
            if !equation.ty().is_prop() {
                bail!("new_recfun", "`{equation}` is not a proposition");
            }
            if let Some((var, _)) = equation.free_vars().into_iter().next() {
                bail!(
                    "new_recfun",
                    "equation `{equation}` has the free variable `{var}`; quantify it"
                );
            }
            let mut body = equation.clone();
            let mut avoid = BTreeSet::new();
            let mut binders = Vec::new();
            while let Some(pred) = body.dest_forall() {
                let (var, opened) = pred.open_fresh(&avoid).expect("lambda");
                avoid.insert(var.as_free().expect("free").0.clone());
                binders.push(var);
                body = opened;
            }
            let Some((lhs, rhs)) = body.dest_eq() else {
                bail!("new_recfun", "`{equation}` is not an equation");
            };
            let (head, args) = lhs.strip_app();
            match head.as_const() {
                Some((n, ty)) if n == f && ty == &f_ty => {}
                Some((n, _)) if n == f => bail!(
                    "new_recfun",
                    "equation `{equation}` uses `{f}` at a type instance; state equations at the declared type `{f_ty}`"
                ),
                _ => bail!(
                    "new_recfun",
                    "the left side of `{equation}` is not an application of `{f}`"
                ),
            }
            match arity {
                None => arity = Some(args.len()),
                Some(n) if n != args.len() => bail!(
                    "new_recfun",
                    "equations of `{f}` have different numbers of arguments"
                ),
                Some(_) => {}
            }
            if args.len() <= spec.rec_arg {
                bail!(
                    "new_recfun",
                    "equation `{equation}` does not supply argument {} of `{f}`",
                    spec.rec_arg
                );
            }
            let mut pattern_vars: Vec<Term> = Vec::new();
            let mut note_var = |t: &Term| -> Result<()> {
                if t.as_free().is_none() {
                    bail!(
                        "new_recfun",
                        "`{t}` in the left side of `{equation}` is not a variable; only the recursive argument may be a constructor pattern"
                    );
                }
                if pattern_vars.contains(t) {
                    bail!(
                        "new_recfun",
                        "variable `{t}` occurs twice in the left side of `{equation}`"
                    );
                }
                pattern_vars.push(t.clone());
                Ok(())
            };
            let (ctor_head, ctor_args) = args[spec.rec_arg].strip_app();
            let Some((ctor_name, _)) = ctor_head.as_const() else {
                bail!(
                    "new_recfun",
                    "the recursive argument in `{equation}` is not a constructor pattern"
                );
            };
            let Some(ctor) = datatype.ctor(ctor_name) else {
                bail!(
                    "new_recfun",
                    "`{ctor_name}` is not a constructor of `{}`",
                    datatype.name
                );
            };
            if ctor_args.len() != ctor.args.len() {
                bail!(
                    "new_recfun",
                    "constructor `{ctor_name}` takes {} argument(s) in `{equation}`",
                    ctor.args.len()
                );
            }
            for (i, arg) in args.iter().enumerate() {
                if i == spec.rec_arg {
                    for ctor_arg in &ctor_args {
                        note_var(ctor_arg)?;
                    }
                } else {
                    note_var(arg)?;
                }
            }
            if !covered.insert(ctor_name.clone()) {
                bail!(
                    "new_recfun",
                    "`{f}` has two equations for constructor `{ctor_name}`"
                );
            }
            for (var, _) in rhs.free_vars() {
                if !pattern_vars
                    .iter()
                    .any(|p| p.as_free().map(|(n, _)| n) == Some(&var))
                {
                    bail!(
                        "new_recfun",
                        "the right side of `{equation}` mentions `{var}`, which is not bound on the left"
                    );
                }
            }
            let rec_vars: Vec<Term> = ctor_args
                .iter()
                .zip(&ctor.recursive)
                .filter(|(_, r)| **r)
                .map(|(t, _)| (*t).clone())
                .collect();
            check_recursive_calls(rhs, group, &rec_vars, equation)?;
            out.push((
                Name::new(&format!("{f}.eq.{ctor_name}")),
                Thm::new(vec![], equation.clone(), Tags::none()),
            ));
        }
        for ctor in &datatype.ctors {
            if !covered.contains(&ctor.name) {
                bail!(
                    "new_recfun",
                    "`{f}` has no equation for constructor `{}`",
                    ctor.name
                );
            }
        }
        Ok(out)
    }
}

/// Every occurrence of a group constant must head an application with
/// enough arguments and a recursive pattern variable at its recursive
/// argument position. This is structural descent, and it is what makes
/// admitting the equations conservative.
fn check_recursive_calls(
    t: &Term,
    group: &BTreeMap<Name, usize>,
    rec_vars: &[Term],
    equation: &Term,
) -> Result<()> {
    match t.view() {
        TermView::Const(name, _) => {
            if group.contains_key(name) {
                bail!(
                    "new_recfun",
                    "`{name}` occurs unapplied in the right side of `{equation}`; recursive calls must pass a smaller argument"
                );
            }
            Ok(())
        }
        TermView::Free(..) | TermView::Bound(..) => Ok(()),
        TermView::Lam(_, _, body) => check_recursive_calls(body, group, rec_vars, equation),
        TermView::App(..) => {
            let (head, args) = t.strip_app();
            if let Some((name, _)) = head.as_const() {
                if let Some(&rec_arg) = group.get(name) {
                    match args.get(rec_arg) {
                        Some(arg) if rec_vars.contains(arg) => {}
                        _ => bail!(
                            "new_recfun",
                            "the call `{t}` in `{equation}` is not structurally smaller: argument {rec_arg} must be one of the recursive pattern variables"
                        ),
                    }
                }
            } else {
                check_recursive_calls(head, group, rec_vars, equation)?;
            }
            for arg in args {
                check_recursive_calls(arg, group, rec_vars, equation)?;
            }
            Ok(())
        }
    }
}
