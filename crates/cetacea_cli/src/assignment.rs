use std::collections::BTreeSet;
use std::fmt;

use cetacea_core::hol::TeachingProfile;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RequiredTheorem {
    pub name: String,
    pub signature: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct AssignmentManifest {
    pub version: u32,
    pub profile: TeachingProfile,
    pub allow_classical: bool,
    pub allow_extensionality: bool,
    pub allow_choice: bool,
    pub allow_new_axioms: bool,
    pub allow_incomplete: bool,
    pub allowed_imports: Vec<String>,
    pub allowed_axioms: Vec<String>,
    pub required_theorems: Vec<RequiredTheorem>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ManifestError {
    line: Option<usize>,
    message: String,
}

impl ManifestError {
    fn at(line: usize, message: impl Into<String>) -> Self {
        Self {
            line: Some(line),
            message: message.into(),
        }
    }

    fn global(message: impl Into<String>) -> Self {
        Self {
            line: None,
            message: message.into(),
        }
    }
}

impl fmt::Display for ManifestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(line) = self.line {
            write!(f, "line {line}: {}", self.message)
        } else {
            f.write_str(&self.message)
        }
    }
}

pub(crate) fn parse_manifest(source: &str) -> Result<AssignmentManifest, ManifestError> {
    let assignments = logical_assignments(source)?;
    let mut seen = BTreeSet::new();
    let mut required_names = BTreeSet::new();
    let mut version = None;
    let mut profile = None;
    let mut allow_classical = false;
    let mut allow_extensionality = false;
    let mut allow_choice = false;
    let mut allow_new_axioms = false;
    let mut allow_incomplete = false;
    let mut allowed_imports = Vec::new();
    let mut allowed_axioms = Vec::new();
    let mut required_theorems = Vec::new();

    for (line, assignment) in assignments {
        let Some((key, value)) = assignment.split_once('=') else {
            return Err(ManifestError::at(line, "expected `key = value`"));
        };
        let key = key.trim();
        let value = value.trim();
        if key.is_empty() {
            return Err(ManifestError::at(line, "manifest key cannot be empty"));
        }

        if let Some(name) = key.strip_prefix("required_theorem.") {
            let name = name.trim();
            if !is_qualified_name(name) {
                return Err(ManifestError::at(
                    line,
                    "required theorem name must be a nonempty qualified name",
                ));
            }
            if !required_names.insert(name.to_string()) {
                return Err(ManifestError::at(
                    line,
                    format!("duplicate required theorem `{name}`"),
                ));
            }
            let signature = parse_string(value)
                .map_err(|message| ManifestError::at(line, format!("{key}: {message}")))?;
            if signature.trim().is_empty() {
                return Err(ManifestError::at(
                    line,
                    format!("required theorem `{name}` has an empty signature"),
                ));
            }
            required_theorems.push(RequiredTheorem {
                name: name.to_string(),
                signature,
            });
            continue;
        }

        if !seen.insert(key.to_string()) {
            return Err(ManifestError::at(line, format!("duplicate key `{key}`")));
        }
        match key {
            "version" => {
                let parsed = value
                    .parse::<u32>()
                    .map_err(|_| ManifestError::at(line, "version must be the integer `1`"))?;
                if parsed != 1 {
                    return Err(ManifestError::at(
                        line,
                        format!("unsupported assignment manifest version `{parsed}`"),
                    ));
                }
                version = Some(parsed);
            }
            "profile" => {
                let value = parse_string(value)
                    .map_err(|message| ManifestError::at(line, format!("profile: {message}")))?;
                profile = Some(parse_profile(&value).ok_or_else(|| {
                    ManifestError::at(
                        line,
                        "profile must be `prop`, `fol`, `fol+induction`, or `hol`",
                    )
                })?);
            }
            "allow_classical" => allow_classical = parse_bool(line, key, value)?,
            "allow_extensionality" => allow_extensionality = parse_bool(line, key, value)?,
            "allow_choice" => allow_choice = parse_bool(line, key, value)?,
            "allow_new_axioms" => allow_new_axioms = parse_bool(line, key, value)?,
            "allow_incomplete" => allow_incomplete = parse_bool(line, key, value)?,
            "allowed_imports" => {
                allowed_imports = parse_string_array(value)
                    .map_err(|message| ManifestError::at(line, format!("{key}: {message}")))?;
                reject_empty_or_duplicate(line, key, &allowed_imports)?;
            }
            "allowed_axioms" => {
                allowed_axioms = parse_string_array(value)
                    .map_err(|message| ManifestError::at(line, format!("{key}: {message}")))?;
                reject_empty_or_duplicate(line, key, &allowed_axioms)?;
                if let Some(name) = allowed_axioms.iter().find(|name| !is_qualified_name(name)) {
                    return Err(ManifestError::at(
                        line,
                        format!("{key} entry '{name}' is not a qualified declaration name"),
                    ));
                }
            }
            _ => return Err(ManifestError::at(line, format!("unknown key `{key}`"))),
        }
    }

    let version = version.ok_or_else(|| ManifestError::global("missing required key `version`"))?;
    let profile = profile.ok_or_else(|| ManifestError::global("missing required key `profile`"))?;
    required_theorems.sort_by(|left, right| left.name.cmp(&right.name));

    Ok(AssignmentManifest {
        version,
        profile,
        allow_classical,
        allow_extensionality,
        allow_choice,
        allow_new_axioms,
        allow_incomplete,
        allowed_imports,
        allowed_axioms,
        required_theorems,
    })
}

fn parse_profile(value: &str) -> Option<TeachingProfile> {
    match value {
        "prop" => Some(TeachingProfile::Prop),
        "fol" => Some(TeachingProfile::FirstOrder),
        "fol+induction" | "fol-induction" => Some(TeachingProfile::FirstOrderInductive),
        "hol" => Some(TeachingProfile::HigherOrder),
        _ => None,
    }
}

fn is_qualified_name(name: &str) -> bool {
    !name.is_empty()
        && name.split('.').all(|part| {
            let mut chars = part.chars();
            chars
                .next()
                .is_some_and(|ch| ch.is_ascii_alphabetic() || ch == '_')
                && chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
        })
}

fn parse_bool(line: usize, key: &str, value: &str) -> Result<bool, ManifestError> {
    match value {
        "true" => Ok(true),
        "false" => Ok(false),
        _ => Err(ManifestError::at(
            line,
            format!("`{key}` must be `true` or `false`"),
        )),
    }
}

fn reject_empty_or_duplicate(
    line: usize,
    key: &str,
    values: &[String],
) -> Result<(), ManifestError> {
    let mut seen = BTreeSet::new();
    for value in values {
        if value.is_empty() {
            return Err(ManifestError::at(
                line,
                format!("`{key}` cannot contain an empty string"),
            ));
        }
        if !seen.insert(value) {
            return Err(ManifestError::at(
                line,
                format!("`{key}` contains duplicate entry `{value}`"),
            ));
        }
    }
    Ok(())
}

fn logical_assignments(source: &str) -> Result<Vec<(usize, String)>, ManifestError> {
    let mut assignments = Vec::new();
    let mut pending = String::new();
    let mut pending_line = 0usize;
    let mut bracket_depth = 0isize;

    for (index, raw_line) in source.lines().enumerate() {
        let line_number = index + 1;
        let line =
            strip_comment(raw_line).map_err(|message| ManifestError::at(line_number, message))?;
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if pending.is_empty() {
            pending_line = line_number;
        } else {
            pending.push('\n');
        }
        pending.push_str(trimmed);
        bracket_depth += bracket_delta(trimmed);
        if bracket_depth < 0 {
            return Err(ManifestError::at(line_number, "unmatched `]`"));
        }
        if bracket_depth == 0 {
            assignments.push((pending_line, std::mem::take(&mut pending)));
        }
    }

    if bracket_depth != 0 {
        return Err(ManifestError::at(
            pending_line,
            "unterminated array; expected `]`",
        ));
    }
    Ok(assignments)
}

fn strip_comment(line: &str) -> Result<String, &'static str> {
    let mut quote = None;
    let mut escaped = false;
    for (index, ch) in line.char_indices() {
        if let Some(delimiter) = quote {
            if delimiter == '"' && escaped {
                escaped = false;
            } else if delimiter == '"' && ch == '\\' {
                escaped = true;
            } else if ch == delimiter {
                quote = None;
            }
        } else {
            match ch {
                '"' | '\'' => quote = Some(ch),
                '#' => return Ok(line[..index].to_string()),
                _ => {}
            }
        }
    }
    if quote.is_some() {
        Err("quoted strings cannot span lines")
    } else {
        Ok(line.to_string())
    }
}

fn bracket_delta(value: &str) -> isize {
    let mut quote = None;
    let mut escaped = false;
    let mut delta = 0isize;
    for ch in value.chars() {
        if let Some(delimiter) = quote {
            if delimiter == '"' && escaped {
                escaped = false;
            } else if delimiter == '"' && ch == '\\' {
                escaped = true;
            } else if ch == delimiter {
                quote = None;
            }
        } else {
            match ch {
                '"' | '\'' => quote = Some(ch),
                '[' => delta += 1,
                ']' => delta -= 1,
                _ => {}
            }
        }
    }
    delta
}

fn parse_string(value: &str) -> Result<String, String> {
    let mut cursor = StringCursor::new(value);
    let parsed = cursor.quoted()?;
    cursor.whitespace();
    if cursor.peek().is_some() {
        Err("unexpected text after string".to_string())
    } else {
        Ok(parsed)
    }
}

fn parse_string_array(value: &str) -> Result<Vec<String>, String> {
    let mut cursor = StringCursor::new(value);
    cursor.whitespace();
    cursor.expect('[', "expected a string array beginning with `[`")?;
    let mut values = Vec::new();
    loop {
        cursor.whitespace();
        if cursor.consume(']') {
            break;
        }
        values.push(cursor.quoted()?);
        cursor.whitespace();
        if cursor.consume(']') {
            break;
        }
        cursor.expect(',', "expected `,` or `]` after array entry")?;
        cursor.whitespace();
        if cursor.consume(']') {
            break;
        }
    }
    cursor.whitespace();
    if cursor.peek().is_some() {
        Err("unexpected text after string array".to_string())
    } else {
        Ok(values)
    }
}

struct StringCursor<'a> {
    source: &'a str,
    index: usize,
}

impl<'a> StringCursor<'a> {
    fn new(source: &'a str) -> Self {
        Self { source, index: 0 }
    }

    fn peek(&self) -> Option<char> {
        self.source[self.index..].chars().next()
    }

    fn next(&mut self) -> Option<char> {
        let ch = self.peek()?;
        self.index += ch.len_utf8();
        Some(ch)
    }

    fn consume(&mut self, expected: char) -> bool {
        if self.peek() == Some(expected) {
            self.next();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, expected: char, message: &str) -> Result<(), String> {
        if self.consume(expected) {
            Ok(())
        } else {
            Err(message.to_string())
        }
    }

    fn whitespace(&mut self) {
        while self.peek().is_some_and(char::is_whitespace) {
            self.next();
        }
    }

    fn quoted(&mut self) -> Result<String, String> {
        self.whitespace();
        let Some(delimiter @ ('"' | '\'')) = self.next() else {
            return Err("expected a single- or double-quoted string".to_string());
        };
        let mut output = String::new();
        loop {
            let Some(ch) = self.next() else {
                return Err("unterminated quoted string".to_string());
            };
            if ch == delimiter {
                return Ok(output);
            }
            if delimiter == '"' && ch == '\\' {
                let Some(escaped) = self.next() else {
                    return Err("unterminated string escape".to_string());
                };
                output.push(match escaped {
                    '"' => '"',
                    '\\' => '\\',
                    'n' => '\n',
                    'r' => '\r',
                    't' => '\t',
                    other => return Err(format!("unsupported string escape `\\{other}`")),
                });
            } else {
                output.push(ch);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_versioned_assignment_manifest() {
        let manifest = parse_manifest(
            r#"
# Assignment policy is fail-closed.
version = 1
profile = "fol+induction"
allow_classical = true
allow_extensionality = false
allow_choice = false
allow_new_axioms = false
allow_incomplete = true
allowed_imports = [
  "std/prop.ctea",
  "std/nat.ctea", # comments are allowed
]
allowed_axioms = ["prop.excluded_middle"]
required_theorem.exercise_3 = 'forall n : Nat, n = n'
required_theorem.named.result = "True"
"#,
        )
        .expect("manifest should parse");

        assert_eq!(manifest.version, 1);
        assert_eq!(manifest.profile, TeachingProfile::FirstOrderInductive);
        assert!(manifest.allow_classical);
        assert!(manifest.allow_incomplete);
        assert_eq!(manifest.allowed_imports, ["std/prop.ctea", "std/nat.ctea"]);
        assert_eq!(manifest.allowed_axioms, ["prop.excluded_middle"]);
        assert_eq!(manifest.required_theorems.len(), 2);
        assert_eq!(manifest.required_theorems[0].name, "exercise_3");
        assert_eq!(manifest.required_theorems[1].name, "named.result");
    }

    #[test]
    fn manifest_rejects_unknown_duplicate_and_malformed_policy() {
        for (source, expected) in [
            ("profile = 'fol'", "missing required key `version`"),
            ("version = 2\nprofile = 'fol'", "unsupported"),
            (
                "version = 1\nprofile = 'fol'\nprofile = 'hol'",
                "duplicate key `profile`",
            ),
            (
                "version = 1\nprofile = 'fol'\nallow_choice = yes",
                "must be `true` or `false`",
            ),
            (
                "version = 1\nprofile = 'fol'\nsurprise = false",
                "unknown key `surprise`",
            ),
            (
                "version = 1\nprofile = 'fol'\nallowed_imports = ['x', 'x']",
                "duplicate entry `x`",
            ),
            (
                "version = 1\nprofile = 'fol'\nrequired_theorem.x = 'True'\nrequired_theorem.x = 'True'",
                "duplicate required theorem `x`",
            ),
            (
                "version = 1\nprofile = 'fol'\nallowed_axioms = ['not-valid']",
                "qualified declaration name",
            ),
        ] {
            let error = parse_manifest(source).expect_err("manifest should fail");
            assert!(error.to_string().contains(expected), "{error}");
        }
    }

    #[test]
    fn literal_strings_preserve_formula_backslashes() {
        let manifest =
            parse_manifest("version = 1\nprofile = 'prop'\nrequired_theorem.em = 'P \\/ not P'")
                .expect("literal statement should parse");
        assert_eq!(manifest.required_theorems[0].signature, "P \\/ not P");

        let escaped = parse_manifest(
            r#"version = 1
profile = "prop"
required_theorem.message = "line one\nline two""#,
        )
        .expect("double-quoted escapes should parse");
        assert_eq!(escaped.required_theorems[0].signature, "line one\nline two");
    }
}
