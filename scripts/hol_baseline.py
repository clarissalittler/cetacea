#!/usr/bin/env python3
"""Capture or verify the pre-HOL Cetacea corpus oracle.

The golden file deliberately records semantic checker output rather than CLI
presentation: root declaration receipts, diagnostic identities, source hashes,
and the rejection of every theorem in an intended-negative fixture.
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_GOLDEN = ROOT / "docs" / "hol" / "fol-baseline.json"
CORPUS_ROOTS = (
    ROOT / "std",
    ROOT / "examples",
    ROOT / "docs" / "cs250" / "code",
    ROOT / "docs" / "book" / "code",
)
# The oracle freezes the pre-HOL teaching corpus. New source libraries layered
# over logical packages live under std/hol and are checked by check_all plus
# native/browser HOL regressions; adding one must not silently widen this
# historical baseline.
CORPUS_EXCLUDED_ROOTS = (ROOT / "std" / "hol",)
NEGATIVE_MARKERS = ("mistakes", "fallacies", "negative")
THEOREM_DECL = re.compile(r"^\s*theorem\s+([A-Za-z_][A-Za-z0-9_.]*)", re.MULTILINE)


class BaselineError(RuntimeError):
    pass


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def corpus_files() -> list[Path]:
    return sorted(
        (
            path
            for root in CORPUS_ROOTS
            for path in root.rglob("*.ctea")
            if not any(
                path.is_relative_to(excluded) for excluded in CORPUS_EXCLUDED_ROOTS
            )
        ),
        key=relative,
    )


def is_negative(path: Path) -> bool:
    return any(marker in path.name for marker in NEGATIVE_MARKERS)


def ensure_checker(checker: Path | None) -> Path:
    if checker is not None:
        resolved = checker if checker.is_absolute() else ROOT / checker
        if not resolved.is_file():
            raise BaselineError(f"checker does not exist: {resolved}")
        return resolved

    build = subprocess.run(
        ["cargo", "build", "-q", "-p", "cetacea_cli"],
        cwd=ROOT,
        check=False,
    )
    if build.returncode != 0:
        raise BaselineError("could not build cetacea_cli")
    return ROOT / "target" / "debug" / "cetacea_cli"


def canonical_declaration(theorem: dict[str, Any]) -> dict[str, Any]:
    return {
        "name": theorem["name"],
        "statement": theorem["statement"],
        "mode": theorem["mode"],
        "status": theorem["status"],
        "is_axiom": theorem["is_axiom"],
        "uses_sorry": theorem["uses_sorry"],
        "axiom_deps": theorem["axiom_deps"],
    }


def canonical_diagnostic(diagnostic: dict[str, Any]) -> dict[str, Any]:
    location = diagnostic.get("location")
    canonical_location = None
    if location is not None:
        canonical_location = {
            "path": location.get("path"),
            "line": location["line"],
        }
    return {
        "severity": diagnostic["severity"],
        "message": diagnostic["message"],
        "location": canonical_location,
        "notes": diagnostic.get("notes", []),
    }


def check_one(checker: Path, path: Path) -> dict[str, Any]:
    source = path.read_bytes()
    negative = is_negative(path)
    expected_exit = 1 if negative else 0
    completed = subprocess.run(
        [str(checker), "--json", relative(path)],
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode != expected_exit:
        raise BaselineError(
            f"{relative(path)} exited {completed.returncode}; expected {expected_exit}\n"
            f"stdout:\n{completed.stdout}\nstderr:\n{completed.stderr}"
        )
    try:
        result = json.loads(completed.stdout)
    except json.JSONDecodeError as error:
        raise BaselineError(f"invalid JSON for {relative(path)}: {error}") from error

    root_declarations = [
        canonical_declaration(theorem)
        for theorem in result["theorems"]
        if not theorem["is_imported"]
    ]
    accepted_names = {declaration["name"] for declaration in root_declarations}
    declared_negative_theorems = THEOREM_DECL.findall(source.decode("utf-8")) if negative else []
    accidentally_accepted = sorted(accepted_names.intersection(declared_negative_theorems))
    if accidentally_accepted:
        raise BaselineError(
            f"negative fixture {relative(path)} accepted theorem(s): "
            + ", ".join(accidentally_accepted)
        )
    if negative and not declared_negative_theorems:
        raise BaselineError(f"negative fixture {relative(path)} declares no theorem")

    return {
        "path": relative(path),
        "source_sha256": hashlib.sha256(source).hexdigest(),
        "expected_exit": expected_exit,
        "expected_ok": not negative,
        "root_declarations": root_declarations,
        "diagnostics": [
            canonical_diagnostic(diagnostic) for diagnostic in result["diagnostics"]
        ],
        "negative_theorems": declared_negative_theorems,
    }


def capture(checker: Path) -> dict[str, Any]:
    files = [check_one(checker, path) for path in corpus_files()]
    declarations = [
        declaration
        for file_receipt in files
        for declaration in file_receipt["root_declarations"]
    ]
    status_counts: dict[str, int] = {}
    for declaration in declarations:
        status = declaration["status"]
        status_counts[status] = status_counts.get(status, 0) + 1
    return {
        "format_version": 1,
        "description": "Pre-HOL semantic oracle for the Cetacea teaching corpus",
        "summary": {
            "files": len(files),
            "positive_files": sum(file["expected_exit"] == 0 for file in files),
            "negative_files": sum(file["expected_exit"] == 1 for file in files),
            "root_declarations": len(declarations),
            "declaration_statuses": dict(sorted(status_counts.items())),
            "negative_theorems": sum(len(file["negative_theorems"]) for file in files),
            "diagnostics": sum(len(file["diagnostics"]) for file in files),
        },
        "files": files,
    }


def rendered(receipt: dict[str, Any]) -> str:
    return json.dumps(receipt, indent=2, ensure_ascii=False, sort_keys=True) + "\n"


def write_golden(path: Path, receipt: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(rendered(receipt), encoding="utf-8")
    print(f"captured HOL baseline: {relative(path)}")


def verify_golden(path: Path, receipt: dict[str, Any]) -> None:
    if not path.is_file():
        raise BaselineError(
            f"baseline does not exist: {relative(path)}; run `scripts/hol_baseline.py capture`"
        )
    expected = path.read_text(encoding="utf-8")
    actual = rendered(receipt)
    if expected != actual:
        diff = "".join(
            difflib.unified_diff(
                expected.splitlines(keepends=True),
                actual.splitlines(keepends=True),
                fromfile=relative(path),
                tofile="current checker output",
            )
        )
        raise BaselineError(
            "HOL baseline drifted; inspect the semantic change and, if intentional, "
            "run `scripts/hol_baseline.py capture`\n" + diff
        )
    summary = receipt["summary"]
    print(
        "verified HOL baseline: "
        f"{summary['files']} files, {summary['root_declarations']} root declarations, "
        f"{summary['negative_theorems']} negative theorems"
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("capture", "check"))
    parser.add_argument(
        "--golden",
        type=Path,
        default=DEFAULT_GOLDEN,
        help="golden receipt path (default: docs/hol/fol-baseline.json)",
    )
    parser.add_argument("--checker", type=Path, help="use an existing cetacea_cli binary")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    golden = args.golden if args.golden.is_absolute() else ROOT / args.golden
    try:
        checker = ensure_checker(args.checker)
        receipt = capture(checker)
        if args.command == "capture":
            write_golden(golden, receipt)
        else:
            verify_golden(golden, receipt)
    except BaselineError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
