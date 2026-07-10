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
      theorem_accepted=0
      while IFS= read -r json_record; do
        if [[ "$json_record" == *"\"name\":\"$theorem\""* ]] && \
          [[ "$json_record" == *'"is_imported":false'* ]]; then
          theorem_accepted=1
          break
        fi
      done < <(printf '%s\n' "$json_output" | sed 's/},{/}\n{/g')
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
