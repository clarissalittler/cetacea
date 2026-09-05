//! Standard-library sources shipped with the checker.
pub const STANDARD_LIBRARY_SOURCES: &[(&str, &str)] = &[
    (
        "std/hol/probability_counts.ctea",
        include_str!("../../../std/hol/probability_counts.ctea"),
    ),
    (
        "std/hol/recurrences.ctea",
        include_str!("../../../std/hol/recurrences.ctea"),
    ),
    (
        "std/hol/handshake.ctea",
        include_str!("../../../std/hol/handshake.ctea"),
    ),
    (
        "std/hol/double_counting.ctea",
        include_str!("../../../std/hol/double_counting.ctea"),
    ),
    (
        "std/hol/endpoint_sums.ctea",
        include_str!("../../../std/hol/endpoint_sums.ctea"),
    ),
    (
        "std/hol/weighted_enumerations.ctea",
        include_str!("../../../std/hol/weighted_enumerations.ctea"),
    ),
    (
        "std/hol/finite_weighted_sums.ctea",
        include_str!("../../../std/hol/finite_weighted_sums.ctea"),
    ),
    (
        "std/hol/weighted_sums.ctea",
        include_str!("../../../std/hol/weighted_sums.ctea"),
    ),
    (
        "std/hol/paths.ctea",
        include_str!("../../../std/hol/paths.ctea"),
    ),
    (
        "std/hol/nat_decidable.ctea",
        include_str!("../../../std/hol/nat_decidable.ctea"),
    ),
    (
        "std/hol/finite_union.ctea",
        include_str!("../../../std/hol/finite_union.ctea"),
    ),
    (
        "std/hol/reachability.ctea",
        include_str!("../../../std/hol/reachability.ctea"),
    ),
    (
        "std/hol/sums.ctea",
        include_str!("../../../std/hol/sums.ctea"),
    ),
    ("std/eq.ctea", include_str!("../../../std/eq.ctea")),
    ("std/fol.ctea", include_str!("../../../std/fol.ctea")),
    ("std/fun.ctea", include_str!("../../../std/fun.ctea")),
    (
        "std/hol/counting.ctea",
        include_str!("../../../std/hol/counting.ctea"),
    ),
    (
        "std/hol/pigeonhole.ctea",
        include_str!("../../../std/hol/pigeonhole.ctea"),
    ),
    (
        "std/hol/pigeonhole_classical.ctea",
        include_str!("../../../std/hol/pigeonhole_classical.ctea"),
    ),
    ("std/list.ctea", include_str!("../../../std/list.ctea")),
    (
        "std/modular.ctea",
        include_str!("../../../std/modular.ctea"),
    ),
    ("std/nat.ctea", include_str!("../../../std/nat.ctea")),
    (
        "std/prelude.ctea",
        include_str!("../../../std/prelude.ctea"),
    ),
    ("std/prop.ctea", include_str!("../../../std/prop.ctea")),
    (
        "std/qualified_prelude.ctea",
        include_str!("../../../std/qualified_prelude.ctea"),
    ),
    ("std/set.ctea", include_str!("../../../std/set.ctea")),
];

/// Exact, reserved identity for a source bundled with this checker build.
pub fn bundled_source(identity: &str) -> Option<&'static str> {
    let path = identity.strip_prefix("builtin:")?;
    STANDARD_LIBRARY_SOURCES
        .iter()
        .find_map(|(name, source)| (*name == path).then_some(*source))
}
