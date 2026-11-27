#!/usr/bin/env bash
# Checks that the sample course matches the book: every chapter's worked
# examples and solutions must pass under that chapter's section rules.
# A failure means a section's allow lists drifted from the material it
# is meant to cover (or the material started using something new).
set -u

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root" || exit 1

if ! cargo build -q -p hol_cli; then
  exit 1
fi
checker="$root/target/debug/cetacea2"
course="courses/proofs-checked.json"

if ! "$checker" --course "$course" --list-sections >/dev/null; then
  echo "error: $course does not load" >&2
  exit 1
fi

status=0
checked=0
for chapter in 01 02 03 04 05 06 07 08 09 10 11 12; do
  for kind in examples solutions; do
    file="docs/book/code/ch${chapter}-${kind}.ctea"
    [ -f "$file" ] || continue
    if ! output="$("$checker" --course "$course" --section "ch${chapter}" "$file" 2>&1)"; then
      echo "error: $file does not pass under section ch${chapter}" >&2
      printf '%s\n' "$output" | grep -E '^(error|  note)' | head -8 >&2
      status=1
    fi
    checked=$((checked + 1))
  done
done

if [ "$status" -eq 0 ]; then
  echo "checked $checked chapter files against $course"
fi
exit "$status"
