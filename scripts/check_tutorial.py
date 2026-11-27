#!/usr/bin/env python3
"""Hold the tutorial page to the checker.

`web2/tutorial.html` shows complete proofs and quotes what the checker
says about them. This runs every sample through `cetacea2` and fails
if one no longer gets the verdict the page claims, or if a quoted
message is no longer something the checker prints for that sample.

    python3 scripts/check_tutorial.py

In the page, a sample is `<pre data-name="NAME" data-expect="accepted|
failed|incomplete">`, with `data-section="chNN"` when it is checked
under a course section. Any element with `data-from="NAME"` quotes the
checker's output for that sample, and `data-of="NAME" data-line="N"`
says the error is reported on line N.
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
from html.parser import HTMLParser
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAGE = ROOT / "web2" / "tutorial.html"
CHECKER = ROOT / "target" / "debug" / "cetacea2"
COURSE = ROOT / "courses" / "proofs-checked.json"

VOID = {"meta", "link", "br", "hr", "img", "input"}


class Page(HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.stack: list[dict] = []
        self.samples: dict[str, dict] = {}
        self.quotes: list[tuple[str, str]] = []
        self.lines: list[tuple[str, int]] = []

    def handle_starttag(self, tag, attrs):
        if tag in VOID:
            return
        attrs = dict(attrs)
        if "data-of" in attrs and "data-line" in attrs:
            self.lines.append((attrs["data-of"], int(attrs["data-line"])))
        self.stack.append({"tag": tag, "attrs": attrs, "text": []})

    def handle_data(self, data):
        for frame in self.stack:
            frame["text"].append(data)

    def handle_endtag(self, tag):
        if tag in VOID or not self.stack:
            return
        frame = self.stack.pop()
        attrs, text = frame["attrs"], "".join(frame["text"])
        if "data-name" in attrs:
            self.samples[attrs["data-name"]] = {
                "source": text,
                "expect": attrs.get("data-expect", "accepted"),
                "section": attrs.get("data-section"),
            }
        if "data-from" in attrs:
            self.quotes.append((attrs["data-from"], " ".join(text.split())))


def verdict(code: int, output: str) -> str:
    if code != 0 or "failed theorem" in output:
        return "failed"
    if "incomplete theorem" in output:
        return "incomplete"
    return "accepted"


def main() -> int:
    if subprocess.run(["cargo", "build", "-q", "-p", "hol_cli"], cwd=ROOT).returncode != 0:
        return 1
    page = Page()
    page.feed(PAGE.read_text(encoding="utf-8"))
    status = 0
    outputs: dict[str, str] = {}
    with tempfile.TemporaryDirectory() as tmp:
        for name, sample in page.samples.items():
            path = Path(tmp) / f"{name}.ctea"
            path.write_text(sample["source"], encoding="utf-8")
            command = [str(CHECKER), "--std", str(ROOT / "lib")]
            if sample["section"]:
                command += ["--course", str(COURSE), "--section", sample["section"]]
            run = subprocess.run(command + [str(path)], capture_output=True, text=True)
            outputs[name] = run.stdout + run.stderr
            got = verdict(run.returncode, outputs[name])
            if got != sample["expect"]:
                print(
                    f"error: tutorial sample `{name}` is {got}, but the page says {sample['expect']}",
                    file=sys.stderr,
                )
                print(outputs[name], file=sys.stderr)
                status = 1
    for name, text in page.quotes:
        if name not in outputs:
            print(f"error: the tutorial quotes a sample `{name}` that is not on the page", file=sys.stderr)
            status = 1
        elif text not in " ".join(outputs[name].split()):
            print(f"error: the tutorial quotes output the checker no longer prints for `{name}`: {text}", file=sys.stderr)
            status = 1
    for name, line in page.lines:
        if f".ctea:{line}: " not in outputs.get(name, ""):
            print(f"error: the tutorial says `{name}` fails on line {line}, but the checker does not", file=sys.stderr)
            status = 1
    print(f"checked {len(page.samples)} tutorial samples and {len(page.quotes)} quoted messages")
    return status


if __name__ == "__main__":
    raise SystemExit(main())
