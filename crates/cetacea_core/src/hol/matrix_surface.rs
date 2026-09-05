//! Source schemas checked independently against the kernel computation laws.
use crate::{Formula, Param, ParamKind, Term, Type};

pub(crate) fn matrix_surface_schemas(
    namespace: Option<&str>,
) -> Vec<(&'static str, Vec<Param>, Formula)> {
    let q = |name: &str| namespace.map_or_else(|| name.to_string(), |ns| format!("{ns}.{name}"));
    let a = Type::Named("A".into());
    let b = Type::Named("B".into());
    let la = Type::App(q("List"), vec![a.clone()]);
    let lb = Type::App(q("List"), vec![b.clone()]);
    let v = |name: &str| Term::Var(name.into());
    let nil = |ty| Term::Ascribed {
        term: Box::new(v(&q("nil"))),
        ty,
    };
    let cons = |h: &str, t: &str| Term::App(q("cons"), vec![v(h), v(t)]);
    let call = |name: &str, first, second| Term::App(q(name), vec![v("w"), first, second]);
    let weight = || Term::App("w".into(), vec![v("a"), v("b")]);
    let add = |x, y| Term::Add(Box::new(x), Box::new(y));
    let parameter = |name: &str, ty| Param {
        name: name.into(),
        kind: ParamKind::Term(ty),
    };
    let entries = [
        (
            "row_sum_nil",
            vec![parameter("a", a.clone())],
            call("row_sum", v("a"), nil(lb.clone())),
            Term::Zero,
        ),
        (
            "row_sum_cons",
            vec![
                parameter("a", a.clone()),
                parameter("b", b.clone()),
                parameter("ys", lb.clone()),
            ],
            call("row_sum", v("a"), cons("b", "ys")),
            add(weight(), call("row_sum", v("a"), v("ys"))),
        ),
        (
            "column_sum_nil",
            vec![parameter("b", b.clone())],
            call("column_sum", nil(la.clone()), v("b")),
            Term::Zero,
        ),
        (
            "column_sum_cons",
            vec![
                parameter("a", a.clone()),
                parameter("xs", la.clone()),
                parameter("b", b.clone()),
            ],
            call("column_sum", cons("a", "xs"), v("b")),
            add(weight(), call("column_sum", v("xs"), v("b"))),
        ),
        (
            "rows_total_nil",
            vec![parameter("ys", lb.clone())],
            call("rows_total", nil(la.clone()), v("ys")),
            Term::Zero,
        ),
        (
            "rows_total_cons",
            vec![
                parameter("a", a.clone()),
                parameter("xs", la.clone()),
                parameter("ys", lb.clone()),
            ],
            call("rows_total", cons("a", "xs"), v("ys")),
            add(
                call("row_sum", v("a"), v("ys")),
                call("rows_total", v("xs"), v("ys")),
            ),
        ),
        (
            "columns_total_nil",
            vec![parameter("xs", la.clone())],
            call("columns_total", v("xs"), nil(lb.clone())),
            Term::Zero,
        ),
        (
            "columns_total_cons",
            vec![
                parameter("xs", la),
                parameter("b", b.clone()),
                parameter("ys", lb),
            ],
            call("columns_total", v("xs"), cons("b", "ys")),
            add(
                call("column_sum", v("xs"), v("b")),
                call("columns_total", v("xs"), v("ys")),
            ),
        ),
    ];
    entries
        .into_iter()
        .map(|(name, tail, left, right)| {
            let mut params = vec![
                Param {
                    name: "A".into(),
                    kind: ParamKind::Type,
                },
                Param {
                    name: "B".into(),
                    kind: ParamKind::Type,
                },
                Param {
                    name: "w".into(),
                    kind: ParamKind::Function {
                        arguments: vec![a.clone(), b.clone()],
                        result: Type::Nat,
                    },
                },
            ];
            params.extend(tail);
            (name, params, Formula::eq(left, right))
        })
        .collect()
}
