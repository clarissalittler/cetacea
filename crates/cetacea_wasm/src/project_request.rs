//! Bounded binary transport for a complete, stateless project analysis request.
use super::*;
use cetacea_core::VirtualProject;

const MAX_REQUEST: usize = 9 * 1024 * 1024;
const MAGIC: u32 = 0x31505443; // CTP1 in little-endian byte order.
const ASSIGNMENT_MAGIC: u32 = 0x32505443; // CTP2 adds an instructor context.

struct Reader<'a> {
    rest: &'a [u8],
}
impl<'a> Reader<'a> {
    fn number(&mut self) -> Result<usize, String> {
        let bytes = self.take(4)?;
        Ok(u32::from_le_bytes(bytes.try_into().unwrap()) as usize)
    }
    fn take(&mut self, len: usize) -> Result<&'a [u8], String> {
        if len > self.rest.len() {
            return Err("truncated project request".into());
        }
        let (value, rest) = self.rest.split_at(len);
        self.rest = rest;
        Ok(value)
    }
    fn string(&mut self, limit: usize) -> Result<String, String> {
        let len = self.number()?;
        if len > limit {
            return Err("project request field exceeds its size limit".into());
        }
        std::str::from_utf8(self.take(len)?)
            .map(str::to_owned)
            .map_err(|_| "project request contains invalid UTF-8".into())
    }
}

fn analyze(bytes: &[u8]) -> Result<String, String> {
    if bytes.len() > MAX_REQUEST {
        return Err("project request exceeds 9 MiB".into());
    }
    let mut reader = Reader { rest: bytes };
    let magic = reader.number()?;
    if magic != MAGIC as usize && magic != ASSIGNMENT_MAGIC as usize {
        return Err("unsupported project request version".into());
    }
    let operation = reader.number()?;
    if operation > 4 {
        return Err("unknown project operation".into());
    }
    let first = reader.number()?;
    let second = reader.number()?;
    let root = reader.string(512)?;
    let theorem = reader.string(4096)?;
    let count = reader.number()?;
    if count > 64 {
        return Err("a project may contain at most 64 source files".into());
    }
    let mut files = Vec::with_capacity(count);
    for _ in 0..count {
        files.push(VirtualFile {
            path: reader.string(512)?,
            source: reader.string(1024 * 1024)?,
        });
    }
    let assignment = if magic == ASSIGNMENT_MAGIC as usize {
        let path = reader.string(512)?;
        let source = reader.string(cetacea_core::assignment::MAX_MANIFEST_BYTES)?;
        let trusted_count = reader.number()?;
        if trusted_count > 64 - count {
            return Err(
                "assignment and project may contain at most 64 source files together".into(),
            );
        }
        let mut trusted = Vec::with_capacity(trusted_count);
        for _ in 0..trusted_count {
            trusted.push(VirtualFile {
                path: reader.string(512)?,
                source: reader.string(1024 * 1024)?,
            });
        }
        Some((path, source, trusted))
    } else {
        None
    };
    if !reader.rest.is_empty() {
        return Err("unexpected trailing project request data".into());
    }
    if let Some((path, source, trusted)) = assignment {
        let assignment = cetacea_core::assignment::VirtualAssignment::new(&path, &source, trusted)?;
        return Ok(match operation {
            0 => {
                let result = assignment.check(&root, &files)?;
                let json = hol_shadow_result_json(&result.report);
                let violations = result
                    .violations
                    .iter()
                    .map(|v| {
                        format!(
                            "{{\"declaration\":{},\"kind\":{},\"message\":{}}}",
                            json_string(&v.declaration),
                            json_string(v.kind),
                            json_string(&v.message)
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(",");
                format!(
                    "{},\"assignment\":{{\"path\":{},\"accepted\":{},\"violations\":[{}]}}}}",
                    json.strip_suffix('}').expect("JSON report object"),
                    json_string(&path),
                    result.accepted(),
                    violations
                )
            }
            1 => outline_json(&assignment.outline(&root, &files)?),
            2 => goal_result_json(&assignment.goals_at(
                &root,
                &files,
                Position {
                    line: first,
                    column: second,
                },
            )?),
            3 => goal_result_json(&assignment.run_tactic(&root, &files, &theorem, first)?),
            4 => explanation_result_json(&assignment.explain(&root, &files, &theorem)?),
            _ => unreachable!("validated operation"),
        });
    }
    let project = VirtualProject::new(&root, &files)?;
    Ok(match operation {
        0 => hol_shadow_result_json(&project.check()),
        1 => outline_json(&outline(
            &files.iter().find(|f| f.path == root).unwrap().source,
        )),
        2 => goal_result_json(&project.goals_at(Position {
            line: first,
            column: second,
        })),
        3 => goal_result_json(&project.run_tactic(&theorem, first)),
        4 => explanation_result_json(&project.explain(&theorem)),
        _ => unreachable!("validated operation"),
    })
}

/// Analyze a complete virtual project. Each request owns its file set; no
/// project state survives between calls, cancellations, or worker restarts.
///
/// # Safety
/// `ptr` must identify `len` readable bytes allocated in this Wasm instance.
#[no_mangle]
pub unsafe extern "C" fn cetacea_project(ptr: *const u8, len: usize) -> *mut u8 {
    let result = if len > MAX_REQUEST {
        Err("project request exceeds 9 MiB".into())
    } else if ptr.is_null() {
        Err("project request pointer was null".into())
    } else {
        analyze(std::slice::from_raw_parts(ptr, len))
    };
    response_json(result.unwrap_or_else(|error| error_json(&error)))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn number(bytes: &mut Vec<u8>, value: usize) {
        bytes.extend_from_slice(&(value as u32).to_le_bytes());
    }
    fn string(bytes: &mut Vec<u8>, value: &str) {
        number(bytes, value.len());
        bytes.extend_from_slice(value.as_bytes());
    }
    fn request(operation: usize, helper: &str) -> Vec<u8> {
        let mut bytes = Vec::new();
        for value in [
            MAGIC as usize,
            operation,
            if operation == 2 { 3 } else { 0 },
            1,
        ] {
            number(&mut bytes, value);
        }
        string(&mut bytes, "lesson/main.ctea");
        string(&mut bytes, "answer");
        number(&mut bytes, 2);
        string(&mut bytes, "lesson/main.ctea");
        string(
            &mut bytes,
            "import helper.ctea as H\ntheorem answer : True := by\n  exact H.helper\n",
        );
        string(&mut bytes, "lesson/helper.ctea");
        string(&mut bytes, helper);
        bytes
    }
    const GOOD: &str = "-- Unicode ∀\ntheorem helper : True := by\n  trivial\n";
    fn assignment_request(operation: usize, signature: &str, collision: bool) -> (Vec<u8>, usize) {
        let mut bytes = Vec::new();
        for value in [
            ASSIGNMENT_MAGIC as usize,
            operation,
            if operation == 2 { 3 } else { 0 },
            1,
        ] {
            number(&mut bytes, value);
        }
        string(&mut bytes, "lesson/main.ctea");
        string(&mut bytes, "answer");
        number(&mut bytes, if collision { 2 } else { 1 });
        string(&mut bytes, "lesson/main.ctea");
        string(
            &mut bytes,
            "import helper.ctea as H\ntheorem answer : True := by\n  exact H.helper\n",
        );
        if collision {
            string(&mut bytes, "lesson/helper.ctea");
            string(&mut bytes, GOOD);
        }
        string(&mut bytes, "lesson/task.ctea-assignment");
        string(&mut bytes, &format!("version = 1\nprofile = 'prop'\nrequired_imports = ['helper.ctea']\nallowed_theorems = ['helper.ctea::helper']\nrequired_theorem.answer = '{signature}'\n"));
        let count_offset = bytes.len();
        number(&mut bytes, 1);
        string(&mut bytes, "lesson/helper.ctea");
        string(&mut bytes, GOOD);
        (bytes, count_offset)
    }
    #[test]
    fn assignment_transport_separates_proof_certification_from_assignment_acceptance() {
        let good = analyze(&assignment_request(0, "True", false).0).unwrap();
        assert!(good.contains("\"hol_certified\":true"));
        assert!(good.contains("\"accepted\":true"));
        let wrong = analyze(&assignment_request(0, "False", false).0).unwrap();
        assert!(wrong.contains("\"hol_certified\":true"));
        assert!(wrong.contains("\"accepted\":false"));
        assert!(wrong.contains("theorem_signature"));
        for operation in 0..=4 {
            assert!(analyze(&assignment_request(operation, "True", false).0).is_ok());
            assert!(analyze(&assignment_request(operation, "True", true).0)
                .unwrap_err()
                .contains("collides"));
        }
        for operation in [3, 4] {
            assert!(analyze(&assignment_request(operation, "True", false).0)
                .unwrap()
                .contains("\"completed\":true"));
        }
    }
    #[test]
    fn assignment_packets_reject_truncation_and_unbounded_trusted_file_counts() {
        let (packet, offset) = assignment_request(0, "True", false);
        for cut in 0..packet.len() {
            assert!(analyze(&packet[..cut]).is_err(), "cut {cut}");
        }
        let mut excessive = packet;
        excessive[offset..offset + 4].copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(analyze(&excessive).unwrap_err().contains("64 source files"));
    }

    #[test]
    fn project_requests_cover_every_analysis_operation_without_retaining_files() {
        assert!(analyze(&request(0, GOOD))
            .unwrap()
            .contains("\"hol_certified\":true"));
        assert!(analyze(&request(1, GOOD))
            .unwrap()
            .contains("\"name\":\"answer\""));
        assert!(analyze(&request(2, GOOD))
            .unwrap()
            .contains("\"target\":\"True\""));
        for operation in [3, 4] {
            assert!(analyze(&request(operation, GOOD))
                .unwrap()
                .contains("\"completed\":true"));
        }
        assert!(
            analyze(&request(0, "theorem helper : False := by\n  trivial\n"))
                .unwrap()
                .contains("\"hol_certified\":false")
        );
        assert!(analyze(&request(0, GOOD))
            .unwrap()
            .contains("\"hol_certified\":true"));
    }
    #[test]
    fn malformed_project_packets_are_rejected_without_panicking() {
        let valid = request(0, GOOD);
        for cut in 0..valid.len() {
            assert!(analyze(&valid[..cut]).is_err(), "cut {cut}");
        }
        let mut trailing = valid.clone();
        trailing.push(0);
        assert!(analyze(&trailing).is_err());
        let mut version = valid.clone();
        version[0] = 0;
        assert!(analyze(&version).is_err());
        assert!(analyze(&request(5, GOOD)).is_err());
        let mut invalid_utf8 = valid.clone();
        invalid_utf8[20] = 255;
        assert!(analyze(&invalid_utf8).is_err());
        let mut oversized_field = valid.clone();
        oversized_field[16..20].copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(analyze(&oversized_field).is_err());
    }
}
