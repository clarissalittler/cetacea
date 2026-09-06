#!/usr/bin/env bash
# Corpus check for the Cetacea 2 checker (cetacea2). Mirrors check_all.sh:
# positive files must check cleanly, negative files must reject every
# theorem. Files that need natural numbers or data types are skipped until
# the milestone that adds them.
set -u

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root" || exit 1

if ! cargo build -q -p hol_cli; then
  exit 1
fi
checker="$root/target/debug/cetacea2"

is_negative_file() {
  case "$1" in
    *mistakes*.ctea|*fallacies*.ctea|*negative*.ctea) return 0 ;;
    *) return 1 ;;
  esac
}

allows_incomplete() {
  case "$1" in
    docs/book/code/*-exercises.ctea|docs/cs250/code/09_modular.ctea) return 0 ;;
    *) return 1 ;;
  esac
}

needs_later_milestone() {
  grep -qE '^data |\bList\b|\bTree\b' "$1"
}

tier_flags() {
  if grep -qE '\bNat\b|\bsucc\(|\badd\(|\bmul\(|\ble\(|\bsub\(|^defrec |[0-9]' "$1"; then
    printf -- '--tier fol_nat'
  fi
}

mapfile -t files < <(find lib examples docs/cs250/code docs/book/code -type f -name '*.ctea' | sort)

status=0
checked=0
skipped=0
for file in "${files[@]}"; do
  if [[ "$file" == std/* ]]; then
    continue
  fi
  if needs_later_milestone "$file"; then
    skipped=$((skipped + 1))
    continue
  fi
  checked=$((checked + 1))
  flags="$(tier_flags "$file")"
  # shellcheck disable=SC2086
  output="$("$checker" $flags "$file" 2>&1)"
  code=$?
  if is_negative_file "$file"; then
    if [[ $code -eq 0 ]]; then
      printf 'error: %s passed, but is expected to fail\n' "$file" >&2
      status=1
      continue
    fi
    # shellcheck disable=SC2086
    json_output="$("$checker" --json $flags "$file" 2>/dev/null)"
    mapfile -t negative_theorems < <(
      sed -nE 's/^[[:space:]]*theorem[[:space:]]+([A-Za-z_][A-Za-z0-9_.]*).*/\1/p' "$file"
    )
    for theorem in "${negative_theorems[@]}"; do
      if printf '%s' "$json_output" | grep -q "\"name\":\"$theorem\",\"kind\":\"theorem\",\"status\":\"accepted\""; then
        printf 'error: theorem %s in %s passed, but every theorem in a negative file must fail\n' "$theorem" "$file" >&2
        status=1
      fi
    done
    continue
  fi
  if [[ $code -ne 0 ]]; then
    printf 'error: %s failed, but is expected to check\n' "$file" >&2
    printf '%s\n' "$output" | grep -E '^(error|  note|  try)' | head -12 >&2
    status=1
    continue
  fi
  if [[ "$output" == *"incomplete theorem"* ]] && ! allows_incomplete "$file"; then
    printf 'error: %s checked with unexpected incomplete theorem(s)\n' "$file" >&2
    status=1
  fi
done

printf 'checked %s files, skipped %s for later milestones\n' "$checked" "$skipped"
exit "$status"
