//! Proof expressions: hypotheses, theorems, projections, application to
//! terms and proofs, and explicit instantiation.
//!
//! The result of elaboration is a kernel theorem that may still mention
//! metavariables for theorem parameters that were not determined by the
//! arguments. Those are solved later by unifying with the goal (see
//! [`ProofCtx::coerce`]) or reported.

use std::collections::BTreeMap;

use hol_elab::{print_term, Diagnostic, Elab, Env, ParamInfo, Scope, TypePosition};
use hol_kernel::{
    and_left, and_right, assume, eq_mp, forall_elim, iff_left, iff_right, imp_elim, sym, trans,
    Name, Term, TermView, Thm, Type,
};
use hol_syntax::{Expr, Ident, InstArg, Projection, ProofExpr, Span};

use crate::conv::{head_unfold, normalize, rhs, Rules};
use crate::proof::Goal;
use crate::unify::{meta_display_name, schematize, Subst};

pub type Result<T> = std::result::Result<T, Diagnostic>;

pub struct ProofCtx<'a> {
    pub env: &'a Env,
    pub goal: &'a Goal,
    pub scope: Scope,
    pub subst: Subst,
    pub rules: Rules,
    /// Term parameters of the theorem at the head of the current
    /// application, in declaration order, for positional arguments.
    positional: Vec<Term>,
}

enum ArgKind<'e> {
    Term(Expr),
    Proof(&'e ProofExpr),
}

fn kernel(span: Span) -> impl Fn(hol_kernel::KernelError) -> Diagnostic {
    move |e| Diagnostic::new(span, e.message)
}

impl<'a> ProofCtx<'a> {
    pub fn new(env: &'a Env, base_scope: &Scope, goal: &'a Goal, subst: Subst) -> ProofCtx<'a> {
        let mut scope = base_scope.clone();
        for var in &goal.vars {
            scope.push(var.clone());
        }
        let mut subst = subst;
        let rules = Rules::definitional(env, &mut subst);
        ProofCtx {
            env,
            goal,
            scope,
            subst,
            rules,
            positional: Vec::new(),
        }
    }

    /// Prints a term with metavariables shown as `?name`.
    pub fn show(&self, t: &Term) -> String {
        let text = print_term(self.env, &self.subst.apply(t));
        strip_meta_suffixes(&text)
    }

    pub fn elab_term(&mut self, expr: &Expr, expected: Option<&Type>) -> Result<Term> {
        let unifier = std::mem::take(&mut self.subst.types);
        let mut elab = Elab::with_unifier(self.env, unifier);
        let expected = expected.map(|t| elab.unifier.zonk(t));
        let result = elab.expr(&mut self.scope, expr, expected.as_ref());
        let result = result.map(|t| elab.unifier.zonk_term(&t));
        self.subst.types = elab.into_unifier();
        result
    }

    pub fn elab_type(&mut self, ty: &hol_syntax::TypeExpr) -> Result<Type> {
        hol_elab::elab_type(self.env, &self.scope.types, ty, TypePosition::Param)
    }

    /// `|- t = nf(t)`.
    pub fn norm(&self, t: &Term) -> hol_kernel::Result<Thm> {
        normalize(&self.subst, &self.rules, t).map(|(thm, _)| thm)
    }

    pub fn elab_proof(&mut self, expr: &ProofExpr) -> Result<Thm> {
        match expr {
            ProofExpr::Name(ident) => self.name(ident),
            ProofExpr::Term(term) => Err(Diagnostic::new(
                term.span(),
                "expected a proof (a hypothesis or theorem), but this is a term".to_string(),
            )),
            ProofExpr::Proj(inner, projection, span) => {
                let thm = self.elab_proof(inner)?;
                self.project(thm, *projection, *span)
            }
            ProofExpr::App(head, args, span) => {
                let mut thm = self.elab_proof(head)?;
                let positional = std::mem::take(&mut self.positional);
                self.positional = positional;
                for arg in args {
                    thm = self.apply_arg(thm, arg, *span)?;
                }
                self.positional.clear();
                Ok(thm)
            }
            ProofExpr::Inst(head, args, span) => {
                let ProofExpr::Name(ident) = &**head else {
                    return Err(Diagnostic::new(
                        *span,
                        "explicit instantiation `{...}` applies to a theorem name".to_string(),
                    ));
                };
                self.instantiate(ident, args, *span)
            }
        }
    }

    fn name(&mut self, ident: &Ident) -> Result<Thm> {
        let name = ident.name.as_str();
        if let Some(hyp) = self.goal.hyp(name) {
            return assume(hyp).map_err(kernel(ident.span));
        }
        if let Some(info) = self.env.theorem(name) {
            crate::uses::record(&info.name, ident.span, info.is_imported);
            let (thm, _, term_metas) = schematize(
                &mut self.subst,
                &info.thm,
                &info.type_params(),
                &info.term_params(),
            )
            .map_err(kernel(ident.span))?;
            self.positional = info
                .term_params()
                .iter()
                .filter_map(|(n, _)| term_metas.get(n).cloned())
                .collect();
            return Ok(thm);
        }
        if self.scope.lookup(name).is_some() || self.env.constant(name).is_some() {
            return Err(
                Diagnostic::new(ident.span, format!("`{name}` is a term, not a proof")).note(
                    format!("apply a hypothesis or theorem to it instead, as in `h {name}`"),
                ),
            );
        }
        let mut diag = Diagnostic::new(
            ident.span,
            format!("unknown hypothesis or theorem `{name}`"),
        );
        let hyps: Vec<String> = self.goal.hyps.iter().map(|(n, _)| n.to_string()).collect();
        if !hyps.is_empty() {
            diag = diag.note(format!("hypotheses in scope: {}", hyps.join(", ")));
        }
        Err(diag)
    }

    fn project(&mut self, thm: Thm, projection: Projection, span: Span) -> Result<Thm> {
        let concl = self.subst.apply(thm.concl());
        let thm = self.subst.apply_thm(&thm).map_err(kernel(span))?;
        if concl.dest_and().is_some() {
            return match projection {
                Projection::Left => and_left(&thm),
                Projection::Right => and_right(&thm),
            }
            .map_err(kernel(span));
        }
        if concl.dest_iff().is_some() {
            return match projection {
                Projection::Left => iff_left(&thm),
                Projection::Right => iff_right(&thm),
            }
            .map_err(kernel(span));
        }
        let unfolded = head_unfold(&self.subst, &self.rules, &concl).map_err(kernel(span))?;
        let target = rhs(&unfolded);
        if target != concl && (target.dest_and().is_some() || target.dest_iff().is_some()) {
            let converted = eq_mp(&unfolded, &thm).map_err(kernel(span))?;
            return self.project(converted, projection, span);
        }
        let field = match projection {
            Projection::Left => "left",
            Projection::Right => "right",
        };
        Err(Diagnostic::new(
            span,
            format!(
                "`.{field}` needs a conjunction or biconditional, but this proves `{}`",
                self.show(&concl)
            ),
        ))
    }

    fn classify<'e>(&self, arg: &'e ProofExpr) -> Result<ArgKind<'e>> {
        match arg {
            ProofExpr::Name(ident) => {
                let name = ident.name.as_str();
                if self.goal.hyp(name).is_some() {
                    return Ok(ArgKind::Proof(arg));
                }
                if self.scope.lookup(name).is_some() || self.env.constant(name).is_some() {
                    return Ok(ArgKind::Term(Expr::Var(ident.clone())));
                }
                if self.env.theorem(name).is_some() {
                    return Ok(ArgKind::Proof(arg));
                }
                Err(
                    Diagnostic::new(ident.span, format!("unknown name `{name}`"))
                        .note("arguments are hypotheses, theorems, variables, or terms"),
                )
            }
            ProofExpr::Term(expr) => Ok(ArgKind::Term(expr.clone())),
            _ => Ok(ArgKind::Proof(arg)),
        }
    }

    fn apply_arg(&mut self, thm: Thm, arg: &ProofExpr, span: Span) -> Result<Thm> {
        let kind = self.classify(arg)?;
        let mut thm = thm;
        for _ in 0..50 {
            let concl = self.subst.apply(thm.concl());
            // A term given to a theorem whose statement is not universally
            // quantified fills its next unbound parameter.
            if let ArgKind::Term(expr) = &kind {
                if concl.dest_forall().is_none() && !self.positional.is_empty() {
                    let meta = self.positional.remove(0);
                    let expected = self.subst.apply_type(meta.ty());
                    let term = self.elab_term(expr, Some(&expected))?;
                    if !self.subst.unify(&meta, &term) {
                        return Err(Diagnostic::new(
                            expr.span(),
                            format!(
                                "the parameter was already determined as `{}`, which differs from `{}`",
                                self.show(&meta),
                                self.show(&term)
                            ),
                        ));
                    }
                    return self.subst.apply_thm(&thm).map_err(kernel(span));
                }
            }
            if let Some(pred) = concl.dest_forall() {
                let TermView::Lam(binder, ty, _) = pred.view() else {
                    unreachable!();
                };
                return match kind {
                    ArgKind::Term(expr) => {
                        let ty = self.subst.apply_type(ty);
                        let term = self.elab_term(&expr, Some(&ty))?;
                        let thm = self.subst.apply_thm(&thm).map_err(kernel(span))?;
                        forall_elim(&thm, &term).map_err(kernel(span))
                    }
                    ArgKind::Proof(proof) => Err(Diagnostic::new(
                        proof.span(),
                        format!("expected a term for the variable `{binder}`, but found a proof"),
                    )),
                };
            }
            if let Some((premise, _)) = concl.dest_imp() {
                let premise = premise.clone();
                return match kind {
                    ArgKind::Proof(proof) => {
                        let saved = std::mem::take(&mut self.positional);
                        let arg_thm = self.elab_proof(proof);
                        self.positional = saved;
                        let arg_thm = arg_thm?;
                        let arg_thm = self.coerce(arg_thm, &premise, proof.span())?;
                        let thm = self.subst.apply_thm(&thm).map_err(kernel(span))?;
                        imp_elim(&thm, &arg_thm).map_err(kernel(span))
                    }
                    ArgKind::Term(expr) => Err(Diagnostic::new(
                        expr.span(),
                        format!(
                            "expected a proof of `{}`, but found a term",
                            self.show(&premise)
                        ),
                    )),
                };
            }
            let unfolded = head_unfold(&self.subst, &self.rules, &concl).map_err(kernel(span))?;
            if rhs(&unfolded) == concl {
                break;
            }
            let applied = self.subst.apply_thm(&thm).map_err(kernel(span))?;
            thm = eq_mp(&unfolded, &applied).map_err(kernel(span))?;
        }
        Err(Diagnostic::new(
            span,
            format!(
                "`{}` is not an implication or a universal statement, so it cannot be applied to an argument",
                self.show(thm.concl())
            ),
        ))
    }

    fn instantiate(&mut self, ident: &Ident, args: &[InstArg], span: Span) -> Result<Thm> {
        let name = ident.name.as_str();
        if self.goal.hyp(name).is_some() {
            return Err(Diagnostic::new(
                span,
                format!("`{name}` is a hypothesis; only theorems take `{{...}}` arguments"),
            )
            .note(format!("apply it to terms directly, as in `{name} x`")));
        }
        let Some(info) = self.env.theorem(name).cloned() else {
            return Err(Diagnostic::new(
                ident.span,
                format!("unknown theorem `{name}`"),
            ));
        };
        crate::uses::record(&info.name, ident.span, info.is_imported);
        let (thm, type_metas, term_metas) = schematize(
            &mut self.subst,
            &info.thm,
            &info.type_params(),
            &info.term_params(),
        )
        .map_err(kernel(span))?;
        let param_names: Vec<String> = info.params.iter().map(|p| p.name().to_string()).collect();
        let mut seen: BTreeMap<String, ()> = BTreeMap::new();
        for arg in args {
            let param = arg.param.name.as_str();
            if seen.insert(param.to_string(), ()).is_some() {
                return Err(Diagnostic::new(
                    arg.span,
                    format!("`{param}` is given twice"),
                ));
            }
            if let Some(meta) = type_metas.get(&Name::new(param)) {
                let Some(ty_expr) = &arg.ty else {
                    return Err(Diagnostic::new(
                        arg.span,
                        format!("`{param}` is a type parameter of `{name}`; give it a type such as `Person`"),
                    ));
                };
                let ty = self.elab_type(ty_expr)?;
                if self.subst.types.unify(meta, &ty).is_err() {
                    return Err(Diagnostic::new(
                        arg.span,
                        format!(
                            "`{param}` was already determined as `{}`, which is not `{ty}`",
                            self.subst.apply_type(meta)
                        ),
                    ));
                }
                continue;
            }
            if let Some(meta) = term_metas.get(&Name::new(param)) {
                let Some(expr) = &arg.expr else {
                    return Err(Diagnostic::new(
                        arg.span,
                        format!("`{param}` is a term parameter of `{name}`; give it a term"),
                    ));
                };
                let expected = self.subst.apply_type(meta.ty());
                let term = self.elab_term(expr, Some(&expected))?;
                if !self.subst.unify(meta, &term) {
                    return Err(Diagnostic::new(
                        arg.span,
                        format!(
                            "`{param}` was already determined as `{}`, which differs from `{}`",
                            self.show(meta),
                            self.show(&term)
                        ),
                    ));
                }
                continue;
            }
            let is_hyp_param = info
                .params
                .iter()
                .any(|p| matches!(p, ParamInfo::Hyp(n, _) if n.as_str() == param));
            if is_hyp_param {
                return Err(Diagnostic::new(
                    arg.span,
                    format!("`{param}` is a hypothesis parameter of `{name}`; supply its proof positionally, as in `{name} h`"),
                ));
            }
            return Err(Diagnostic::new(
                arg.span,
                format!("`{name}` has no parameter named `{param}`"),
            )
            .note(format!("its parameters are: {}", param_names.join(", "))));
        }
        Ok(thm)
    }

    /// Turns `thm` into a proof of `expected`, solving metavariables by
    /// unification, first syntactically and then up to definitional
    /// unfolding. The result is fully instantiated.
    pub fn coerce(&mut self, thm: Thm, expected: &Term, span: Span) -> Result<Thm> {
        let concl = self.subst.apply(thm.concl());
        let expected = self.subst.apply(expected);
        let mut trial = self.subst.clone();
        if trial.unify(&concl, &expected) {
            self.subst = trial;
            return self.subst.apply_thm(&thm).map_err(kernel(span));
        }
        let nc = self.norm(&concl).map_err(kernel(span))?;
        let ne = self.norm(&expected).map_err(kernel(span))?;
        let mut trial = self.subst.clone();
        if trial.unify(&rhs(&nc), &rhs(&ne)) {
            self.subst = trial;
            let thm = self.subst.apply_thm(&thm).map_err(kernel(span))?;
            let expected = self.subst.apply(&expected);
            let nc = self.norm(thm.concl()).map_err(kernel(span))?;
            let ne = self.norm(&expected).map_err(kernel(span))?;
            if rhs(&nc) == rhs(&ne) {
                let bridge = trans(&nc, &sym(&ne).map_err(kernel(span))?).map_err(kernel(span))?;
                return eq_mp(&bridge, &thm).map_err(kernel(span));
            }
        }
        Err(Diagnostic::new(
            span,
            format!(
                "proof has type `{}`, but expected `{}`",
                self.show(&concl),
                self.show(&expected)
            ),
        ))
    }

    /// Applies the substitution and rejects leftover metavariables.
    pub fn finalize(&self, thm: &Thm, span: Span, what: &str) -> Result<Thm> {
        let thm = self.subst.apply_thm(thm).map_err(kernel(span))?;
        let mut unsolved = self.subst.unsolved_in(thm.concl());
        for hyp in thm.hyps() {
            unsolved.extend(self.subst.unsolved_in(hyp));
        }
        if let Some((name, _)) = unsolved.first() {
            let display = meta_display_name(name);
            return Err(Diagnostic::new(
                span,
                format!("could not determine the parameter `{display}` of {what}"),
            )
            .suggest(format!("{what} {{{display} := ...}}")));
        }
        Ok(thm)
    }
}

/// `?P.12` prints as `?P`.
pub fn strip_meta_suffixes(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let chars: Vec<char> = text.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        if chars[i] == '?' {
            out.push('?');
            i += 1;
            while i < chars.len()
                && (chars[i].is_alphanumeric() || chars[i] == '_' || chars[i] == '\'')
            {
                out.push(chars[i]);
                i += 1;
            }
            if i < chars.len() && chars[i] == '.' {
                i += 1;
                while i < chars.len() && chars[i].is_ascii_digit() {
                    i += 1;
                }
            }
            continue;
        }
        out.push(chars[i]);
        i += 1;
    }
    out
}
