#!/usr/bin/env bash
set -u

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root" || exit 1

if ! cargo build -q -p cetacea_cli; then
  exit 1
fi
checker="$root/target/debug/cetacea_cli"

is_negative_file() {
  case "$1" in
    *mistakes*.ctea|*fallacies*.ctea|*negative*.ctea)
      return 0
      ;;
    *)
      return 1
      ;;
  esac
}

allows_incomplete() {
  case "$1" in
    docs/book/code/*-exercises.ctea|docs/book/hol-code/*-exercises.ctea|docs/cs250/code/09_modular.ctea)
      return 0
      ;;
    *)
      return 1
      ;;
  esac
}

mapfile -t files < <(find std examples docs/cs250/code docs/book/code docs/book/hol-code -type f -name '*.ctea' | sort)

status=0
book_error_lines=""
book_receipt_lines=""

contains_line() {
  local lines="$1"
  local expected="$2"
  local line
  while IFS= read -r line; do
    if [[ "$line" == "$expected" ]]; then
      return 0
    fi
  done <<< "$lines"
  return 1
}

for file in "${files[@]}"; do
  output="$("$checker" "$file" 2>&1)"
  code=$?

  if [[ "$file" == docs/book/code/* || "$file" == docs/book/hol-code/* ]]; then
    if is_negative_file "$file"; then
      while IFS= read -r line; do
        book_error_lines+="$line"$'\n'
      done < <(printf '%s\n' "$output" | sed -n '/^error: /p')
    else
      while IFS= read -r line; do
        book_receipt_lines+="$line"$'\n'
      done < <(printf '%s\n' "$output" | sed -n '/^\(accepted theorem\|incomplete theorem\|trusted axiom\) /p')
    fi
  fi

  if is_negative_file "$file"; then
    if [[ $code -eq 0 ]]; then
      printf 'error: %s passed, but is expected to fail\n' "$file" >&2
      if [[ -n "$output" ]]; then
        printf '%s\n' "$output" >&2
      fi
      status=1
    elif [[ $code -ne 1 ]]; then
      printf 'error: %s exited with %s, but is expected to exit 1\n' "$file" "$code" >&2
      if [[ -n "$output" ]]; then
        printf '%s\n' "$output" >&2
      fi
      status=1
    fi

    json_output="$("$checker" --json "$file" 2>/dev/null)"
    json_code=$?
    if [[ $json_code -ne 1 ]]; then
      printf 'error: %s JSON check exited with %s, but is expected to exit 1\n' \
        "$file" "$json_code" >&2
      status=1
    fi

    mapfile -t negative_theorems < <(
      sed -nE \
        's/^[[:space:]]*theorem[[:space:]]+([A-Za-z_][A-Za-z0-9_.]*).*/\1/p' \
        "$file"
    )
    if [[ ${#negative_theorems[@]} -eq 0 ]]; then
      printf 'error: %s is marked negative but declares no theorems\n' "$file" >&2
      status=1
    fi
    for theorem in "${negative_theorems[@]}"; do
      theorem_accepted="$(
        printf '%s' "$json_output" | python3 -c '
import json
import sys

name = sys.argv[1]
result = json.load(sys.stdin)
accepted = any(
    entry.get("name") == name and not entry.get("is_imported", False)
    for entry in result.get("theorems", [])
)
print(1 if accepted else 0)
' "$theorem"
      )"
      if [[ $theorem_accepted -eq 1 ]]; then
        printf 'error: theorem %s in %s passed, but every theorem in a negative file must fail\n' \
          "$theorem" "$file" >&2
        status=1
      fi
    done
    continue
  fi

  if [[ $code -ne 0 ]]; then
    printf 'error: %s failed, but is expected to check\n' "$file" >&2
    if [[ -n "$output" ]]; then
      printf '%s\n' "$output" >&2
    fi
    status=1
    continue
  fi

  if [[ "$output" == *"incomplete theorem"* ]] && ! allows_incomplete "$file"; then
    printf 'error: %s checked with unexpected incomplete theorem(s)\n' "$file" >&2
    printf '%s\n' "$output" >&2
    status=1
  fi
done

mapfile -t assignment_manifests < <(
  find docs/book/hol-code -type f -name '*-solutions.ctea-assignment' | sort
)
for manifest in "${assignment_manifests[@]}"; do
  submission="${manifest%.ctea-assignment}.ctea"
  output="$("$checker" --assignment "$manifest" "$submission" 2>&1)"
  code=$?
  if [[ $code -ne 0 ]]; then
    printf 'error: %s failed its assignment policy\n' "$submission" >&2
    printf '%s\n' "$output" >&2
    status=1
  fi
done

mapfile -t restrictive_manifests < <(
  find docs/book/hol-code -type f -name '*-solutions-fol.ctea-assignment' | sort
)
for manifest in "${restrictive_manifests[@]}"; do
  submission="${manifest%-fol.ctea-assignment}.ctea"
  output="$("$checker" --assignment "$manifest" "$submission" 2>&1)"
  code=$?
  if [[ $code -ne 1 || "$output" != *'exceeds profile maximum `fol+induction`'* ]]; then
    printf 'error: %s did not produce its expected fragment-policy rejection\n' \
      "$manifest" >&2
    printf '%s\n' "$output" >&2
    status=1
  fi
done

while IFS= read -r expected; do
  if ! contains_line "$book_error_lines" "$expected"; then
    printf 'error: quoted book diagnostic is stale: %s\n' "$expected" >&2
    status=1
  fi
done < <(sed -n '/^error: /p' docs/book/*.md)

while IFS= read -r expected; do
  if ! contains_line "$book_receipt_lines" "$expected"; then
    printf 'error: quoted book acceptance receipt is stale: %s\n' "$expected" >&2
    status=1
  fi
done < <(sed -n '/^\(accepted theorem\|incomplete theorem\|trusted axiom\) /p' docs/book/*.md)

if [[ $status -eq 0 ]]; then
  printf 'checked %s .ctea files\n' "${#files[@]}"
fi

exit "$status"
