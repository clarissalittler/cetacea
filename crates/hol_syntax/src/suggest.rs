//! "Did you mean" suggestions for misspelled names.

/// The candidate closest to `name`, when it is close enough to be a
/// plausible typo and not simply a different word. One edit is allowed
/// for short names, two for names of four to seven characters, three
/// beyond that; an exact match is not a suggestion.
pub fn closest<'a>(name: &str, candidates: impl IntoIterator<Item = &'a str>) -> Option<&'a str> {
    let wanted = name.to_ascii_lowercase();
    let limit = match name.chars().count() {
        0..=3 => 1,
        4..=7 => 2,
        _ => 3,
    };
    let mut best: Option<(usize, &'a str)> = None;
    for candidate in candidates {
        if candidate == name {
            return None;
        }
        let distance = edit_distance(&wanted, &candidate.to_ascii_lowercase());
        if distance <= limit && best.is_none_or(|(known, _)| distance < known) {
            best = Some((distance, candidate));
        }
    }
    best.map(|(_, candidate)| candidate)
}

/// Damerau-Levenshtein distance: insertions, deletions, substitutions,
/// and swaps of adjacent characters each cost one, so the two commonest
/// typos (one wrong letter, two letters transposed) are one edit.
pub fn edit_distance(left: &str, right: &str) -> usize {
    let left: Vec<char> = left.chars().collect();
    let right: Vec<char> = right.chars().collect();
    let mut two_back: Vec<usize> = vec![0; right.len() + 1];
    let mut previous: Vec<usize> = (0..=right.len()).collect();
    let mut current: Vec<usize> = vec![0; right.len() + 1];
    for i in 1..=left.len() {
        current[0] = i;
        for j in 1..=right.len() {
            let cost = usize::from(left[i - 1] != right[j - 1]);
            current[j] = (previous[j] + 1)
                .min(current[j - 1] + 1)
                .min(previous[j - 1] + cost);
            if i > 1 && j > 1 && left[i - 1] == right[j - 2] && left[i - 2] == right[j - 1] {
                current[j] = current[j].min(two_back[j - 2] + 1);
            }
        }
        std::mem::swap(&mut two_back, &mut previous);
        std::mem::swap(&mut previous, &mut current);
    }
    previous[right.len()]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn typos_are_one_or_two_edits() {
        assert_eq!(edit_distance("exatc", "exact"), 1);
        assert_eq!(edit_distance("intor", "intro"), 1);
        assert_eq!(edit_distance("add_zero_rigth", "add_zero_right"), 1);
        assert_eq!(edit_distance("split", "left"), 4);
    }

    #[test]
    fn suggestions_need_to_be_close() {
        let tactics = ["intro", "exact", "apply", "split", "left", "right"];
        assert_eq!(closest("exatc", tactics), Some("exact"));
        assert_eq!(closest("splt", tactics), Some("split"));
        assert_eq!(closest("omega", tactics), None);
        assert_eq!(closest("exact", tactics), None);
    }
}
