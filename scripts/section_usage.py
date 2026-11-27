#!/usr/bin/env python3
"""Report which tactics and library theorems a set of files uses.

Instructors use this to calibrate a course section: run it over the
solutions for a unit, and the output is exactly what an `allow_tactics`
and `allow_theorems` list for that unit must contain.

    python3 scripts/section_usage.py docs/book/code/ch02-solutions.ctea
    python3 scripts/section_usage.py --json docs/book/code/ch0[1-3]-*.ctea
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CHECKER = ROOT / "target" / "debug" / "cetacea2"

HOL = re.compile(r"^data |\bList\b|\bTree\b|\bfunext\b", re.M)
NAT = re.compile(r"\bNat\b|\bsucc\(|\badd\(|\bmul\(|\ble\(|\bsub\(|^defrec |[0-9]", re.M)


def tier_for(source: str) -> str | None:
    """The tier `scripts/check_hol.sh` would choose for a file with no
    `logic` line."""
    if HOL.search(source):
        return "hol"
    if NAT.search(source):
        return "fol_nat"
    return None


def usage(path: Path) -> dict:
    source = path.read_text(encoding="utf-8")
    command = [str(CHECKER), "--json"]
    tier = tier_for(source)
    if tier and not source.lstrip().startswith("logic "):
        command += ["--tier", tier]
    command.append(str(path))
    done = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, check=False)
    report = json.loads(done.stdout)
    tactics: set[str] = set()
    theorems: set[str] = set()
    for decl in report["declarations"]:
        if not decl["is_imported"]:
            tactics.update(decl["tactics"])
            theorems.update(decl.get("theorems", []))
    return {
        "file": str(path),
        "tier": tier or "fol",
        "ok": report["ok"],
        "tactics": sorted(tactics),
        "theorems": sorted(theorems),
    }


def main(argv: list[str]) -> int:
    as_json = "--json" in argv
    paths = [Path(a) for a in argv if not a.startswith("--")]
    if not paths:
        print(__doc__, file=sys.stderr)
        return 2
    if not CHECKER.exists():
        subprocess.run(["cargo", "build", "-q", "-p", "hol_cli"], cwd=ROOT, check=True)
    results = [usage(path) for path in paths]
    if as_json:
        print(json.dumps(results, indent=2))
        return 0
    for result in results:
        print(f"{result['file']} [{result['tier']}]{'' if result['ok'] else ' (does not check)'}")
        print(f"  tactics:  {' '.join(result['tactics']) or '(none)'}")
        print(f"  theorems: {' '.join(result['theorems']) or '(none)'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
