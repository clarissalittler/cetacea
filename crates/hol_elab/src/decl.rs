//! Elaborating declarations: parameters, theorem headers, and every
//! command except theorem proofs (the tactic crate) and imports (the
//! session).

use hol_kernel::{CtorSpec, DatatypeSpec, Name, RecFunSpec, Term, Type};
use hol_syntax::{Annotation, Command, Expr, Ident, Param, Span, Tier};

use crate::diag::{fail, Diagnostic, Result};
use crate::env::{ConstInfo, DefInfo, Env, ParamInfo, Status, SymbolKind, TheoremInfo};
use crate::expr::{Elab, Scope};
use crate::types::{elab_type, TypePosition, TypeScope};

/// A theorem or axiom header after elaboration.
#[derive(Clone, Debug)]
pub struct TheoremHeader {
    pub name: Name,
    pub params: Vec<ParamInfo>,
    pub scope: Scope,
    /// The full statement, with hypothesis parameters as leading
    /// premises.
    pub statement: Term,
    /// The statement as written, without hypothesis premises.
    pub body: Term,
    pub hyps: Vec<(Name, Term)>,
    pub span: Span,
}

fn kernel_err(span: Span, err: hol_kernel::KernelError) -> Diagnostic {
    Diagnostic::new(span, err.message)
}

fn check_fresh_name(env: &Env, ident: &Ident) -> Result<Name> {
    let name = env.qualify(&ident.name);
    if let Some(kind) = env.name_taken(&name) {
        if !(kind == "a theorem" && env.is_shadowable_theorem(&name)) {
            fail!(ident.span, "`{}` is already declared as {kind}", ident.name);
        }
    }
    if ident.name.contains('.') && env.current_namespace().is_some() {
        fail!(
            ident.span,
            "qualified names cannot be declared inside a namespace block"
        );
    }
    Ok(name)
}

/// Elaborates a parameter list into a scope and parameter descriptions.
pub fn elab_params(
    env: &Env,
    params: &[Param],
    allow_hyps: bool,
) -> Result<(Scope, Vec<ParamInfo>)> {
    let mut scope = Scope::new(TypeScope::default());
    let mut infos: Vec<ParamInfo> = Vec::new();
    let mut seen: Vec<String> = Vec::new();
    for param in params {
        for name in &param.names {
            if seen.contains(&name.name) {
                fail!(name.span, "parameter `{}` is declared twice", name.name);
            }
            seen.push(name.name.clone());
        }
        match &param.annotation {
            Annotation::TypeKind(_) => {
                for name in &param.names {
                    if env.sort(&name.name).is_some() {
                        fail!(
                            name.span,
                            "`{}` is already a declared sort; type parameters need fresh names",
                            name.name
                        );
                    }
                    scope.types.vars.insert(Name::new(&name.name));
                    infos.push(ParamInfo::TypeVar(Name::new(&name.name)));
                }
            }
            Annotation::Type(ty, formula) => {
                match elab_type(env, &scope.types, ty, TypePosition::Param) {
                    Ok(kernel_ty) => {
                        for name in &param.names {
                            let var = Term::free(name.name.as_str(), kernel_ty.clone());
                            scope.push(var);
                            infos.push(ParamInfo::Var(Name::new(&name.name), kernel_ty.clone()));
                        }
                    }
                    Err(type_err) => {
                        let Some(formula) = formula else {
                            return Err(type_err);
                        };
                        if !allow_hyps {
                            return Err(type_err);
                        }
                        match elab_hyp_param(env, &mut scope, formula) {
                            Ok(term) => {
                                for name in &param.names {
                                    infos.push(ParamInfo::Hyp(Name::new(&name.name), term.clone()));
                                }
                            }
                            Err(_) => return Err(type_err),
                        }
                    }
                }
            }
            Annotation::Formula(formula) => {
                if !allow_hyps {
                    fail!(
                        formula.span(),
                        "definition parameters need a type, not a formula"
                    );
                }
                let term = elab_hyp_param(env, &mut scope, formula)?;
                for name in &param.names {
                    infos.push(ParamInfo::Hyp(Name::new(&name.name), term.clone()));
                }
            }
        }
    }
    Ok((scope, infos))
}

fn elab_hyp_param(env: &Env, scope: &mut Scope, formula: &Expr) -> Result<Term> {
    let mut elab = Elab::new(env);
    let term = elab.formula(scope, formula)?;
    elab.finish(&term, formula.span())
}

/// Elaborates a theorem or axiom header.
pub fn elab_theorem_header(
    env: &Env,
    name: &Ident,
    params: &[Param],
    statement: &Expr,
    span: Span,
) -> Result<TheoremHeader> {
    let qualified = check_fresh_name(env, name)?;
    let (mut scope, infos) = elab_params(env, params, true)?;
    let mut elab = Elab::new(env);
    let body = elab.formula(&mut scope, statement)?;
    let body = elab.finish(&body, statement.span())?;
    let hyps: Vec<(Name, Term)> = infos
        .iter()
        .filter_map(|p| match p {
            ParamInfo::Hyp(name, term) => Some((name.clone(), term.clone())),
            _ => None,
        })
        .collect();
    let premises: Vec<Term> = hyps.iter().map(|(_, t)| t.clone()).collect();
    let statement = Term::imps(&premises, &body).map_err(|e| kernel_err(span, e))?;
    Ok(TheoremHeader {
        name: qualified,
        params: infos,
        scope,
        statement,
        body,
        hyps,
        span,
    })
}

/// Elaborates a declaration command other than a theorem or an import.
/// Returns the qualified names it declared.
pub fn elab_command(env: &mut Env, command: &Command) -> Result<Vec<Name>> {
    match command {
        Command::Mode(mode, _) => {
            env.mode = *mode;
            Ok(vec![])
        }
        Command::Logic(tier, _) => {
            env.tier = *tier;
            Ok(vec![])
        }
        Command::Namespace(name, _) => {
            env.push_namespace(&name.name);
            Ok(vec![])
        }
        Command::End(name, span) => match env.pop_namespace() {
            Some(open) if open == name.name => Ok(vec![]),
            Some(open) => {
                env.push_namespace(&open);
                fail!(
                    *span,
                    "`end {}` does not match the open `namespace {open}`",
                    name.name
                )
            }
            None => fail!(*span, "`end {}` has no matching `namespace`", name.name),
        },
        Command::Sort(name, span) => {
            let qualified = check_fresh_name(env, name)?;
            env.theory_mut()
                .new_type(qualified.clone(), 0)
                .map_err(|e| kernel_err(*span, e))?;
            env.add_sort(qualified.clone(), 0);
            env.note_declaration(qualified.clone());
            Ok(vec![qualified])
        }
        Command::Const { name, ty, span } => {
            let qualified = check_fresh_name(env, name)?;
            let kernel_ty = elab_type(env, &TypeScope::default(), ty, TypePosition::Declaration)?;
            if kernel_ty.as_fun().is_some() && env.tier < Tier::Hol {
                return Err(Diagnostic::new(
                    ty.span(),
                    "a constant of function type needs `logic hol`".to_string(),
                )
                .suggest(format!("func {} : {}", name.name, kernel_ty)));
            }
            declare_constant(
                env,
                qualified.clone(),
                kernel_ty,
                SymbolKind::Const,
                0,
                *span,
            )?;
            Ok(vec![qualified])
        }
        Command::Func { name, ty, span } => {
            let qualified = check_fresh_name(env, name)?;
            let kernel_ty = elab_type(env, &TypeScope::default(), ty, TypePosition::Declaration)?;
            let (doms, cod) = kernel_ty.strip_fun();
            if doms.is_empty() {
                return Err(Diagnostic::new(
                    ty.span(),
                    "a `func` needs an arrow type such as `Person -> Person`".to_string(),
                )
                .suggest(format!("const {} : {}", name.name, kernel_ty)));
            }
            if cod.is_prop() {
                return Err(Diagnostic::new(
                    ty.span(),
                    "a function returning `Prop` is a predicate".to_string(),
                )
                .suggest(format!(
                    "pred {}({})",
                    name.name,
                    doms.iter()
                        .map(|d| d.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )));
            }
            let arity = doms.len();
            declare_constant(
                env,
                qualified.clone(),
                kernel_ty,
                SymbolKind::Func,
                arity,
                *span,
            )?;
            Ok(vec![qualified])
        }
        Command::Pred { name, args, span } => {
            let qualified = check_fresh_name(env, name)?;
            let mut doms = Vec::new();
            for arg in args {
                doms.push(elab_type(
                    env,
                    &TypeScope::default(),
                    arg,
                    TypePosition::Declaration,
                )?);
            }
            let kernel_ty = Type::funs(&doms, Type::prop());
            declare_constant(
                env,
                qualified.clone(),
                kernel_ty,
                SymbolKind::Pred,
                doms.len(),
                *span,
            )?;
            Ok(vec![qualified])
        }
        Command::Def {
            name,
            params,
            result,
            body,
            span,
        } => {
            let qualified = check_fresh_name(env, name)?;
            let (mut scope, infos) = elab_params(env, params, false)?;
            let result_ty = elab_type(env, &scope.types, result, TypePosition::Declaration)?;
            let mut elab = Elab::new(env);
            let body_term = elab.expr(&mut scope, body, Some(&result_ty))?;
            let body_term = elab.finish(&body_term, body.span())?;
            let term_params: Vec<(Name, Type)> = infos
                .iter()
                .filter_map(|p| match p {
                    ParamInfo::Var(n, t) => Some((n.clone(), t.clone())),
                    _ => None,
                })
                .collect();
            let vars: Vec<Term> = term_params
                .iter()
                .map(|(n, t)| Term::free(n.clone(), t.clone()))
                .collect();
            let lam = Term::lams(&vars, &body_term).map_err(|e| kernel_err(*span, e))?;
            let equation = env
                .theory_mut()
                .new_def(qualified.clone(), &lam)
                .map_err(|e| {
                    let mut diag = kernel_err(*span, e.clone());
                    if e.message.contains("type variable") {
                        diag = diag.note("a type parameter of a definition must appear in the type of one of its parameters or in its result type");
                    }
                    diag
                })?;
            let type_params: Vec<Name> = infos
                .iter()
                .filter_map(|p| match p {
                    ParamInfo::TypeVar(n) => Some(n.clone()),
                    _ => None,
                })
                .collect();
            env.add_constant(ConstInfo {
                name: qualified.clone(),
                ty: lam.ty().clone(),
                kind: SymbolKind::Def,
                arity: term_params.len(),
                span: Some(*span),
                min_tier: Tier::Fol,
            });
            env.add_def(DefInfo {
                name: qualified.clone(),
                type_params,
                params: term_params,
                result: result_ty.clone(),
                equation,
                is_formula: result_ty.is_prop(),
                span: Some(*span),
            });
            env.note_declaration(qualified.clone());
            Ok(vec![qualified])
        }
        Command::Axiom {
            name,
            params,
            statement,
            span,
        } => {
            let header = elab_theorem_header(env, name, params, statement, *span)?;
            let thm = env
                .theory_mut()
                .new_axiom(header.name.clone(), &header.statement)
                .map_err(|e| kernel_err(*span, e))?;
            let is_imported = env.importing;
            env.add_theorem(TheoremInfo {
                name: header.name.clone(),
                params: header.params,
                statement: header.statement,
                thm,
                status: Status::Axiom,
                is_imported,
                span: Some(*span),
            });
            env.note_declaration(header.name.clone());
            Ok(vec![header.name])
        }
        Command::Data {
            name,
            params,
            ctors,
            span,
        } => elab_data(env, name, params, ctors, *span),
        Command::Defrec {
            name,
            params,
            result,
            rec_on,
            arms,
            span,
        } => elab_defrec(env, name, params, result, rec_on.as_ref(), arms, *span),
        Command::Theorem { span, .. } => fail!(*span, "theorems are checked by the tactic engine"),
        Command::Import { span, .. } => fail!(*span, "imports are resolved by the session"),
    }
}

fn declare_constant(
    env: &mut Env,
    name: Name,
    ty: Type,
    kind: SymbolKind,
    arity: usize,
    span: Span,
) -> Result<()> {
    env.theory_mut()
        .new_const(name.clone(), ty.clone())
        .map_err(|e| kernel_err(span, e))?;
    env.add_constant(ConstInfo {
        name: name.clone(),
        ty,
        kind,
        arity,
        span: Some(span),
        min_tier: Tier::Fol,
    });
    env.note_declaration(name);
    Ok(())
}

fn elab_data(
    env: &mut Env,
    name: &Ident,
    params: &[Ident],
    ctors: &[hol_syntax::CtorDecl],
    span: Span,
) -> Result<Vec<Name>> {
    if env.tier < Tier::Hol && !env.importing {
        return Err(
            Diagnostic::new(span, "declaring a data type needs `logic hol`".to_string())
                .note("add `logic hol` at the top of the file"),
        );
    }
    let qualified = check_fresh_name(env, name)?;
    let type_scope = TypeScope::with(params.iter().map(|p| Name::new(&p.name)));
    // The datatype itself must be visible while elaborating constructor
    // argument types, so register it provisionally.
    let mut probe = env.clone();
    probe.add_sort(qualified.clone(), params.len());
    let mut spec_ctors = Vec::new();
    for ctor in ctors {
        let ctor_name = check_fresh_name(env, &ctor.name)?;
        let mut args = Vec::new();
        for arg in &ctor.args {
            args.push(elab_type(
                &probe,
                &type_scope,
                arg,
                TypePosition::Declaration,
            )?);
        }
        spec_ctors.push(CtorSpec {
            name: ctor_name,
            args,
        });
    }
    let spec = DatatypeSpec {
        name: qualified.clone(),
        params: params.iter().map(|p| Name::new(&p.name)).collect(),
        ctors: spec_ctors,
    };
    let info = env
        .theory_mut()
        .new_datatype(&spec)
        .map_err(|e| kernel_err(span, e))?;
    env.add_sort(qualified.clone(), params.len());
    env.note_declaration(qualified.clone());
    let mut declared = vec![qualified.clone()];
    let generic = info.generic_type();
    for ctor in &info.ctors {
        env.add_constant(ConstInfo {
            name: ctor.name.clone(),
            ty: Type::funs(&ctor.args, generic.clone()),
            kind: SymbolKind::Ctor,
            arity: ctor.args.len(),
            span: Some(span),
            min_tier: Tier::Fol,
        });
        declared.push(ctor.name.clone());
    }
    Ok(declared)
}

#[allow(clippy::too_many_arguments)]
fn elab_defrec(
    env: &mut Env,
    name: &Ident,
    params: &[Param],
    result: &hol_syntax::TypeExpr,
    rec_on: Option<&Ident>,
    arms: &[hol_syntax::RecArm],
    span: Span,
) -> Result<Vec<Name>> {
    if env.tier < Tier::FolNat && !env.importing {
        return Err(Diagnostic::new(
            span,
            "recursive definitions need `logic fol_nat` or `logic hol`".to_string(),
        ));
    }
    let qualified = check_fresh_name(env, name)?;
    let (scope, infos) = elab_params(env, params, false)?;
    let result_ty = elab_type(env, &scope.types, result, TypePosition::Declaration)?;
    let term_params: Vec<(Name, Type)> = infos
        .iter()
        .filter_map(|p| match p {
            ParamInfo::Var(n, t) => Some((n.clone(), t.clone())),
            _ => None,
        })
        .collect();
    if term_params.is_empty() {
        fail!(
            span,
            "a `defrec` needs at least one parameter to recurse on"
        );
    }
    // Recurse on the named parameter, or the first one of a data type.
    let mut rec_arg = None;
    if let Some(chosen) = rec_on {
        match term_params
            .iter()
            .position(|(n, _)| n.as_str() == chosen.name)
        {
            Some(index) => rec_arg = Some(index),
            None => fail!(
                chosen.span,
                "`{}` is not a parameter of `{}`",
                chosen.name,
                name.name
            ),
        }
    }
    for (index, (_, ty)) in term_params.iter().enumerate() {
        if rec_arg.is_some() {
            break;
        }
        if let Type::Con(con, _) = ty {
            if env.theory().datatype(con.as_str()).is_some() {
                rec_arg = Some(index);
                break;
            }
        }
    }
    let Some(rec_arg) = rec_arg else {
        fail!(
            span,
            "`{}` has no parameter of a data type to recurse on",
            name.name
        );
    };
    let Type::Con(dt_name, dt_args) = term_params[rec_arg].1.clone() else {
        unreachable!();
    };
    let datatype = env.theory().datatype(dt_name.as_str()).unwrap().clone();
    let param_subst: hol_kernel::TypeSubst = datatype
        .params
        .iter()
        .cloned()
        .zip(dt_args.iter().cloned())
        .collect();

    let fn_ty = Type::funs(
        &term_params
            .iter()
            .map(|(_, t)| t.clone())
            .collect::<Vec<_>>(),
        result_ty.clone(),
    );
    env.theory_mut()
        .new_const(qualified.clone(), fn_ty.clone())
        .map_err(|e| kernel_err(span, e))?;
    env.add_constant(ConstInfo {
        name: qualified.clone(),
        ty: fn_ty.clone(),
        kind: SymbolKind::Def,
        arity: term_params.len(),
        span: Some(span),
        min_tier: Tier::Fol,
    });

    let f = Term::constant(env.theory().signature(), qualified.clone(), fn_ty.clone())
        .map_err(|e| kernel_err(span, e))?;
    let mut equations = Vec::new();
    for arm in arms {
        let ctor_name = env
            .constant(&arm.ctor.name)
            .map(|c| c.name.clone())
            .unwrap_or_else(|| Name::new(&arm.ctor.name));
        let Some(ctor) = datatype.ctor(&ctor_name) else {
            fail!(
                arm.ctor.span,
                "`{}` is not a constructor of `{}`",
                arm.ctor.name,
                dt_name
            );
        };
        let ctor_arg_types: Vec<Type> = ctor.args.iter().map(|t| t.subst(&param_subst)).collect();
        let rec_count = ctor.recursive.iter().filter(|r| **r).count();
        let expected = ctor_arg_types.len();
        if arm.binders.len() != expected && arm.binders.len() != expected + rec_count {
            fail!(
                arm.span,
                "constructor `{}` has {expected} argument{}; bind {expected} name{} (plus {rec_count} for the recursive results, optionally)",
                arm.ctor.name,
                if expected == 1 { "" } else { "s" },
                if expected == 1 { "" } else { "s" }
            );
        }
        let mut arm_scope = scope.clone();
        let mut ctor_vars = Vec::new();
        for (binder, ty) in arm.binders.iter().zip(&ctor_arg_types) {
            let var = Term::free(binder.name.as_str(), ty.clone());
            arm_scope.push(var.clone());
            ctor_vars.push(var);
        }
        // Optional recursive-result names: `rec` stands for `f(.., k, ..)`.
        let mut rec_index = 0;
        for (i, is_rec) in ctor.recursive.iter().enumerate() {
            if !is_rec {
                continue;
            }
            if let Some(binder) = arm.binders.get(expected + rec_index) {
                let mut args: Vec<Term> = term_params
                    .iter()
                    .map(|(n, t)| Term::free(n.clone(), t.clone()))
                    .collect();
                args[rec_arg] = ctor_vars[i].clone();
                let call = Term::apps(&f, &args).map_err(|e| kernel_err(arm.span, e))?;
                arm_scope.push_named(Name::new(&binder.name), call);
            }
            rec_index += 1;
        }
        let mut elab = Elab::new(env);
        let body = elab.expr(&mut arm_scope, &arm.body, Some(&result_ty))?;
        let body = elab.finish(&body, arm.body.span())?;
        let ctor_term = Term::constant(
            env.theory().signature(),
            ctor.name.clone(),
            Type::funs(&ctor_arg_types, term_params[rec_arg].1.clone()),
        )
        .map_err(|e| kernel_err(arm.span, e))?;
        let pattern = Term::apps(&ctor_term, &ctor_vars).map_err(|e| kernel_err(arm.span, e))?;
        let mut args: Vec<Term> = term_params
            .iter()
            .map(|(n, t)| Term::free(n.clone(), t.clone()))
            .collect();
        args[rec_arg] = pattern;
        let lhs = Term::apps(&f, &args).map_err(|e| kernel_err(arm.span, e))?;
        let eq = Term::eq(&lhs, &body).map_err(|e| kernel_err(arm.span, e))?;
        let mut all_vars: Vec<Term> = Vec::new();
        for (i, (n, t)) in term_params.iter().enumerate() {
            if i == rec_arg {
                all_vars.extend(ctor_vars.iter().cloned());
            } else {
                all_vars.push(Term::free(n.clone(), t.clone()));
            }
        }
        equations.push(Term::foralls(&all_vars, &eq).map_err(|e| kernel_err(arm.span, e))?);
    }
    let thms = env
        .theory_mut()
        .new_recfun(&[RecFunSpec {
            name: qualified.clone(),
            rec_arg,
            equations,
        }])
        .map_err(|e| kernel_err(span, e))?;
    env.add_equations(qualified.clone(), thms);
    env.note_declaration(qualified.clone());
    Ok(vec![qualified])
}
