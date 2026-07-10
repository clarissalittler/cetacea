#!/usr/bin/env python3
"""Run the legacy/HOL shadow comparison over the exact teaching corpus.

`report` prints the current migration frontier without treating HOL mismatches
as a script failure. `check` is the H4/H5 exit gate: legacy positive/negative
behavior must remain intact, every accepted declaration must replay through HOL
with matching theorem receipts, and every elaborated root theorem statement
(including a proof-level intended rejection) must receive a pre-receipt fragment
classification. Intentionally ill-typed signatures are rejected before this
seam and counted separately.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import Counter
from pathlib import Path
from typing import Any

import hol_baseline


ROOT = hol_baseline.ROOT


class ShadowError(RuntimeError):
    pass


def run_one(checker: Path, path: Path) -> dict[str, Any]:
    completed = subprocess.run(
        [str(checker), "--hol-shadow", "--json", hol_baseline.relative(path)],
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode not in (0, 1):
        raise ShadowError(
            f"{hol_baseline.relative(path)} exited {completed.returncode}\n"
            f"stdout:\n{completed.stdout}\nstderr:\n{completed.stderr}"
        )
    try:
        result = json.loads(completed.stdout)
    except json.JSONDecodeError as error:
        raise ShadowError(
            f"invalid JSON for {hol_baseline.relative(path)}: {error}\n"
            f"stdout:\n{completed.stdout}\nstderr:\n{completed.stderr}"
        ) from error

    negative = hol_baseline.is_negative(path)
    has_legacy_error = any(
        diagnostic["severity"] == "error" for diagnostic in result["diagnostics"]
    )
    if has_legacy_error != negative:
        disposition = "reject" if negative else "accept"
        raise ShadowError(
            f"legacy checker did not {disposition} {hol_baseline.relative(path)} "
            "as required by the frozen corpus partition"
        )

    root_theorems = [
        theorem for theorem in result["theorems"] if not theorem["is_imported"]
    ]
    declared_negative: list[str] = []
    if negative:
        declared_negative = hol_baseline.THEOREM_DECL.findall(
            path.read_text(encoding="utf-8")
        )
        accepted = {theorem["name"] for theorem in root_theorems}
        accidentally_accepted = sorted(accepted.intersection(declared_negative))
        if accidentally_accepted:
            raise ShadowError(
                f"negative fixture {hol_baseline.relative(path)} accepted theorem(s): "
                + ", ".join(accidentally_accepted)
            )

    shadow = result.get("hol_shadow")
    if shadow is None:
        raise ShadowError(f"{hol_baseline.relative(path)} returned no HOL shadow report")
    root_classifications = [
        classification
        for classification in shadow.get("statement_classifications", [])
        if not classification["is_imported"]
    ]
    classifiable_negative = [
        name
        for name in declared_negative
        if any(
            diagnostic["severity"] == "error"
            and diagnostic["message"].startswith(f"theorem `{name}` failed:")
            for diagnostic in result["diagnostics"]
        )
    ]
    expected_classifications = [
        theorem["name"] for theorem in root_theorems if not theorem["is_axiom"]
    ]
    expected_classifications.extend(classifiable_negative)
    classified_names = [
        classification["name"] for classification in root_classifications
    ]
    missing_classifications = sorted(
        (Counter(expected_classifications) - Counter(classified_names)).elements()
    )
    if missing_classifications:
        raise ShadowError(
            f"{hol_baseline.relative(path)} did not classify root theorem statement(s): "
            + ", ".join(missing_classifications)
        )
    return {
        "path": hol_baseline.relative(path),
        "negative": negative,
        "root_theorems": root_theorems,
        "root_classifications": root_classifications,
        "expected_classifications": len(expected_classifications),
        "negative_classifications": sum(
            (Counter(classifiable_negative) & Counter(classified_names)).values()
        ),
        "negative_before_classification": len(declared_negative)
        - len(classifiable_negative),
        "shadow": shadow,
    }


def mismatch_key(mismatch: dict[str, Any]) -> tuple[str, str, str, str]:
    return (
        mismatch.get("source_path") or "<source>",
        mismatch["kind"],
        mismatch["declaration"],
        mismatch["message"],
    )


def capture(checker: Path) -> dict[str, Any]:
    files = [run_one(checker, path) for path in hol_baseline.corpus_files()]
    root_theorems = [
        theorem for file_result in files for theorem in file_result["root_theorems"]
    ]
    root_hol_theorems = [
        theorem
        for file_result in files
        for theorem in file_result["shadow"]["theorems"]
        if not theorem["is_imported"]
    ]
    root_classifications = [
        classification
        for file_result in files
        for classification in file_result["root_classifications"]
    ]
    mismatch_occurrences = [
        mismatch
        for file_result in files
        for mismatch in file_result["shadow"]["mismatches"]
    ]
    unique_mismatches: dict[tuple[str, str, str, str], dict[str, Any]] = {}
    occurrence_counts: Counter[tuple[str, str, str, str]] = Counter()
    for mismatch in mismatch_occurrences:
        key = mismatch_key(mismatch)
        unique_mismatches.setdefault(key, mismatch)
        occurrence_counts[key] += 1

    fragment_counts = Counter(
        theorem["required_fragment"] for theorem in root_hol_theorems
    )
    status_counts = Counter(theorem["hol_status"] for theorem in root_hol_theorems)
    files_matching = sum(file_result["shadow"]["matches"] for file_result in files)
    mismatches = []
    for key, mismatch in sorted(unique_mismatches.items()):
        mismatches.append(
            {
                **mismatch,
                "occurrences": occurrence_counts[key],
            }
        )

    return {
        "summary": {
            "files": len(files),
            "positive_files": sum(not file_result["negative"] for file_result in files),
            "negative_files": sum(file_result["negative"] for file_result in files),
            "files_matching": files_matching,
            "root_legacy_theorems": len(root_theorems),
            "root_hol_theorems": len(root_hol_theorems),
            "root_statement_classifications": len(root_classifications),
            "expected_root_statement_classifications": sum(
                file_result["expected_classifications"] for file_result in files
            ),
            "negative_statement_classifications": sum(
                file_result["negative_classifications"] for file_result in files
            ),
            "negative_statements_before_classification": sum(
                file_result["negative_before_classification"] for file_result in files
            ),
            "attempted_declaration_occurrences": sum(
                file_result["shadow"]["attempted_declarations"]
                for file_result in files
            ),
            "checked_declaration_occurrences": sum(
                file_result["shadow"]["checked_declarations"]
                for file_result in files
            ),
            "mismatch_occurrences": len(mismatch_occurrences),
            "unique_mismatches": len(mismatches),
            "required_fragments": dict(sorted(fragment_counts.items())),
            "statuses": dict(sorted(status_counts.items())),
        },
        "mismatches": mismatches,
        "files": [
            {
                "path": file_result["path"],
                "matches": file_result["shadow"]["matches"],
                "mismatches": len(file_result["shadow"]["mismatches"]),
            }
            for file_result in files
        ],
    }


def print_report(receipt: dict[str, Any]) -> None:
    summary = receipt["summary"]
    print(
        "HOL shadow: "
        f"{summary['files_matching']}/{summary['files']} files match; "
        f"{summary['root_hol_theorems']}/{summary['root_legacy_theorems']} "
        "root theorem receipts; "
        f"{summary['unique_mismatches']} unique mismatches "
        f"({summary['mismatch_occurrences']} occurrences)"
    )
    print(
        "declaration occurrences: "
        f"{summary['checked_declaration_occurrences']}/"
        f"{summary['attempted_declaration_occurrences']} checked"
    )
    print(
        "pre-receipt statement classifications: "
        f"{summary['root_statement_classifications']}/"
        f"{summary['expected_root_statement_classifications']} root theorem statements; "
        f"{summary['negative_statement_classifications']} proof-negative; "
        f"{summary['negative_statements_before_classification']} rejected before classification"
    )
    print(f"required fragments: {summary['required_fragments']}")
    print(f"statuses: {summary['statuses']}")
    for mismatch in receipt["mismatches"]:
        source = mismatch.get("source_path") or "<source>"
        print(
            f"- {source}:{mismatch['line']}: {mismatch['kind']} "
            f"{mismatch['declaration']} ({mismatch['occurrences']} occurrence(s)): "
            f"{mismatch['message']}"
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("report", "check"))
    parser.add_argument("--checker", type=Path, help="use an existing cetacea_cli binary")
    parser.add_argument("--json", action="store_true", help="print the aggregate as JSON")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        checker = hol_baseline.ensure_checker(args.checker)
        receipt = capture(checker)
    except (hol_baseline.BaselineError, ShadowError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1

    if args.json:
        print(json.dumps(receipt, indent=2, ensure_ascii=False, sort_keys=True))
    else:
        print_report(receipt)
    if args.command == "check" and receipt["summary"]["unique_mismatches"]:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
