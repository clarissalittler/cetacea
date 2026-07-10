#!/usr/bin/env python3
"""Reject accidental UI/driver dependencies in the proof-kernel module."""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
CORE_SRC = ROOT / "crates" / "cetacea_core" / "src"
KERNEL_PATHS = (
    CORE_SRC / "kernel.rs",
    CORE_SRC / "kernel",
    CORE_SRC / "hol" / "types.rs",
    CORE_SRC / "hol" / "terms.rs",
    CORE_SRC / "hol" / "proofs.rs",
    CORE_SRC / "hol" / "inductive.rs",
    CORE_SRC / "hol" / "recursion.rs",
)

# These names belong outside the trusted logical core. Patterns are purposely
# narrow enough that comments explaining the boundary do not trigger them.
FORBIDDEN = {
    "filesystem access": re.compile(r"\bstd::fs\b|\buse\s+std::fs\b"),
    "filesystem paths": re.compile(r"\bstd::path\b|\bPathBuf\b"),
    "surface parser": re.compile(r"\bTokens\b|\bParseError\b|\bparse_[A-Za-z0-9_]*\b"),
    "tactic engine": re.compile(r"\bTactic\b|\bPartialProof\b|\brun_tactic[A-Za-z0-9_]*\b"),
    "diagnostics/UI": re.compile(
        r"\bDiagnostic\b|\bSourceLocation\b|\bGoalSnapshot\b|\bExplanationResult\b"
    ),
    "countermodel engine": re.compile(r"\bCountermodel\b|\bfind_[A-Za-z0-9_]*countermodel\b"),
    "file checker/driver": re.compile(r"\bFileChecker\b|\bcheck_file[A-Za-z0-9_]*\b"),
}


def kernel_files() -> list[Path]:
    files: list[Path] = []
    for path in KERNEL_PATHS:
        if path.is_file():
            files.append(path)
        elif path.is_dir():
            files.extend(sorted(path.rglob("*.rs")))
    return files


def main() -> int:
    files = kernel_files()
    if not files:
        print("error: no kernel module found", file=sys.stderr)
        return 1

    violations: list[str] = []
    for path in files:
        for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            code = line.split("//", 1)[0]
            for label, pattern in FORBIDDEN.items():
                if pattern.search(code):
                    violations.append(
                        f"{path.relative_to(ROOT)}:{line_number}: {label}: {line.strip()}"
                    )

    if violations:
        print("error: kernel boundary violations:", file=sys.stderr)
        for violation in violations:
            print(f"  {violation}", file=sys.stderr)
        return 1

    print(f"verified kernel boundary: {len(files)} Rust module(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
