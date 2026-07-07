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
    docs/book/code/*-exercises.ctea|docs/cs250/code/09_modular.ctea)
      return 0
      ;;
    *)
      return 1
      ;;
  esac
}

mapfile -t files < <(find std examples docs/cs250/code docs/book/code -type f -name '*.ctea' | sort)

status=0

for file in "${files[@]}"; do
  output="$("$checker" "$file" 2>&1)"
  code=$?

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

  if [[ "$output" == *"incomplete: uses sorry"* ]] && ! allows_incomplete "$file"; then
    printf 'error: %s checked with unexpected incomplete theorem(s)\n' "$file" >&2
    printf '%s\n' "$output" >&2
    status=1
  fi
done

if [[ $status -eq 0 ]]; then
  printf 'checked %s .ctea files\n' "${#files[@]}"
fi

exit "$status"
