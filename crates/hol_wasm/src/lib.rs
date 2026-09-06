//! WebAssembly exports for the browser UI.
//!
//! The calling convention is deliberately plain so the site needs no
//! generated glue: the host allocates a UTF-8 buffer with `c2_alloc`,
//! writes the source, calls an export, and reads back a length-prefixed
//! UTF-8 JSON response (four little-endian length bytes, then the bytes),
//! freeing both with `c2_free`. The standard library is embedded, so
//! `import ../std/prelude.ctea` and friends resolve to it.

use hol_session::{analyze, hints, Options, Policy, VirtualFs};
use hol_syntax::Tier;
use serde::Deserialize;

#[derive(Deserialize, Default)]
struct RequestOptions {
    #[serde(default)]
    tier: Option<String>,
    #[serde(default)]
    deny_sorry: bool,
    #[serde(default)]
    deny_axioms: bool,
    #[serde(default)]
    deny_classical: bool,
    /// The path the source is checked as, for relative imports.
    #[serde(default)]
    path: Option<String>,
    /// An assignment manifest to check against.
    #[serde(default)]
    assignment: Option<hol_session::Manifest>,
    #[serde(default)]
    deny_tactics: Vec<String>,
}

impl RequestOptions {
    fn parse(text: &str) -> RequestOptions {
        serde_json::from_str(text).unwrap_or_default()
    }

    fn options(&self) -> Options {
        let mut policy = Policy {
            deny_sorry: self.deny_sorry,
            deny_axioms: self.deny_axioms,
            deny_classical: self.deny_classical,
            deny_tactics: self.deny_tactics.clone(),
        };
        let mut tier = self.tier.as_deref().and_then(Tier::parse);
        if let Some(manifest) = &self.assignment {
            if let Some(t) = manifest.tier.as_deref().and_then(Tier::parse) {
                tier = Some(t);
            }
            policy.deny_sorry |= manifest.policy.deny_sorry;
            policy.deny_axioms |= manifest.policy.deny_axioms;
            policy.deny_classical |= manifest.policy.deny_classical;
            policy
                .deny_tactics
                .extend(manifest.policy.deny_tactics.iter().cloned());
        }
        Options {
            tier,
            policy,
            std_dir: Some("lib".to_string()),
        }
    }

    fn path(&self) -> String {
        self.path.clone().unwrap_or_else(|| "main.ctea".to_string())
    }
}

/// The embedded standard library.
pub fn standard_library() -> VirtualFs {
    let mut fs = VirtualFs::default();
    fs.add(
        "lib/prelude.ctea",
        include_str!("../../../lib/prelude.ctea"),
    );
    fs.add("lib/prop.ctea", include_str!("../../../lib/prop.ctea"));
    fs.add("lib/fol.ctea", include_str!("../../../lib/fol.ctea"));
    fs.add("lib/eq.ctea", include_str!("../../../lib/eq.ctea"));
    fs.add("lib/set.ctea", include_str!("../../../lib/set.ctea"));
    fs.add("lib/nat.ctea", include_str!("../../../lib/nat.ctea"));
    fs.add(
        "lib/modular.ctea",
        include_str!("../../../lib/modular.ctea"),
    );
    fs.add("lib/fun.ctea", include_str!("../../../lib/fun.ctea"));
    fs.add("lib/list.ctea", include_str!("../../../lib/list.ctea"));
    fs.add("lib/finite.ctea", include_str!("../../../lib/finite.ctea"));
    fs.add(
        "lib/qualified_prelude.ctea",
        include_str!("../../../lib/qualified_prelude.ctea"),
    );
    fs
}

/// Runs the analysis on a source with JSON options; returns JSON.
pub fn analyze_json(source: &str, options: &str) -> String {
    let opts = RequestOptions::parse(options);
    let fs = standard_library();
    let analysis = analyze(
        &fs,
        opts.options(),
        Some(&opts.path()),
        source,
        opts.assignment.as_ref(),
    );
    serde_json::to_string(&analysis).unwrap_or_else(|e| format!("{{\"error\":\"{e}\"}}"))
}

/// Tactic hints at a line; returns JSON.
pub fn hints_json(source: &str, options: &str, line: u32) -> String {
    let opts = RequestOptions::parse(options);
    let fs = standard_library();
    let hints = hints(&fs, opts.options(), Some(&opts.path()), source, line);
    serde_json::to_string(&hints).unwrap_or_else(|e| format!("{{\"error\":\"{e}\"}}"))
}

fn response(text: String) -> *mut u8 {
    let bytes = text.into_bytes();
    let len = bytes.len() as u32;
    let mut buffer = Vec::with_capacity(bytes.len() + 4);
    buffer.extend_from_slice(&len.to_le_bytes());
    buffer.extend_from_slice(&bytes);
    let mut boxed = buffer.into_boxed_slice();
    let ptr = boxed.as_mut_ptr();
    std::mem::forget(boxed);
    ptr
}

/// # Safety
/// `ptr` must point to `len` readable bytes allocated by `c2_alloc`.
unsafe fn read(ptr: *const u8, len: usize) -> String {
    if ptr.is_null() {
        return String::new();
    }
    let slice = std::slice::from_raw_parts(ptr, len);
    String::from_utf8_lossy(slice).into_owned()
}

#[no_mangle]
pub extern "C" fn c2_alloc(len: usize) -> *mut u8 {
    let mut buffer = Vec::<u8>::with_capacity(len.max(1));
    let ptr = buffer.as_mut_ptr();
    std::mem::forget(buffer);
    ptr
}

/// # Safety
/// `ptr` must come from `c2_alloc` or a response, with the same `len`
/// (for responses, the payload length plus four).
#[no_mangle]
pub unsafe extern "C" fn c2_free(ptr: *mut u8, len: usize) {
    if !ptr.is_null() {
        drop(Vec::from_raw_parts(ptr, 0, len.max(1)));
    }
}

#[no_mangle]
pub extern "C" fn c2_version() -> *mut u8 {
    response(format!("\"{}\"", env!("CARGO_PKG_VERSION")))
}

/// # Safety
/// Both pointers must be valid for their lengths.
#[no_mangle]
pub unsafe extern "C" fn c2_analyze(
    source_ptr: *const u8,
    source_len: usize,
    options_ptr: *const u8,
    options_len: usize,
) -> *mut u8 {
    let source = read(source_ptr, source_len);
    let options = read(options_ptr, options_len);
    response(analyze_json(&source, &options))
}

/// # Safety
/// Both pointers must be valid for their lengths.
#[no_mangle]
pub unsafe extern "C" fn c2_hints(
    source_ptr: *const u8,
    source_len: usize,
    options_ptr: *const u8,
    options_len: usize,
    line: u32,
) -> *mut u8 {
    let source = read(source_ptr, source_len);
    let options = read(options_ptr, options_len);
    response(hints_json(&source, &options, line))
}
