//! Source schemas for the explicit-path package.

/// One schema description shared by alias binding and the source environment.
/// Binding still lowers and checks it against the independently checked kernel law.
pub(crate) fn path_surface_schemas(
    namespace: Option<&str>,
) -> Vec<(&'static str, Vec<crate::Param>, crate::Formula)> {
    use crate::{Formula, Param, ParamKind, Term, Type};
    let qualify =
        |name: &str| namespace.map_or_else(|| name.to_string(), |ns| format!("{ns}.{name}"));
    let element = Type::Named("A".into());
    let list = Type::App(qualify("List"), vec![element.clone()]);
    let var = |name: &str| Term::Var(name.into());
    let path = |xs| Formula::PredApp(qualify("ValidPath"), vec![var("E"), xs, var("a"), var("b")]);
    let nil = Term::Ascribed {
        term: Box::new(var(&qualify("nil"))),
        ty: list.clone(),
    };
    let nil_left = path(nil);
    let nil_right = Formula::eq(var("b"), var("a"));
    let cons_left = path(Term::App(qualify("cons"), vec![var("h"), var("t")]));
    let cons_right = Formula::and(
        Formula::PredApp("E".into(), vec![var("a"), var("h")]),
        Formula::PredApp(
            qualify("ValidPath"),
            vec![var("E"), var("t"), var("h"), var("b")],
        ),
    );
    let base = vec![
        Param {
            name: "A".into(),
            kind: ParamKind::Type,
        },
        Param {
            name: "E".into(),
            kind: ParamKind::Predicate(vec![element.clone(), element.clone()]),
        },
    ];
    let endpoint = |name: &str| Param {
        name: name.into(),
        kind: ParamKind::Term(element.clone()),
    };
    [
        ("path_nil", nil_left, nil_right),
        ("path_cons", cons_left, cons_right),
    ]
    .into_iter()
    .map(|(name, left, right)| {
        let mut params = base.clone();
        if name == "path_cons" {
            params.push(endpoint("h"));
            params.push(Param {
                name: "t".into(),
                kind: ParamKind::Term(list.clone()),
            });
        }
        params.extend([endpoint("a"), endpoint("b")]);
        (
            name,
            params,
            Formula::and(
                Formula::implies(left.clone(), right.clone()),
                Formula::implies(right, left),
            ),
        )
    })
    .collect()
}
