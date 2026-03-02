#!/usr/bin/env bash
set -euo pipefail

# Check Lean file size policy.
# Usage:
#   scripts/check_lean_file_length.sh [max_lines] [path1 path2 ...]
# Defaults:
#   max_lines = 2000
#   paths     = StringGeometry

max_lines="${1:-2000}"
if [[ "$#" -gt 0 ]]; then
  shift
fi

if [[ "$#" -gt 0 ]]; then
  paths=("$@")
else
  paths=("StringGeometry")
fi

tmp_all="$(mktemp)"
tmp_bad="$(mktemp)"
trap 'rm -f "$tmp_all" "$tmp_bad"' EXIT

find "${paths[@]}" -type f -name '*.lean' -print0 \
  | xargs -0 wc -l \
  | sed '$d' \
  > "$tmp_all"

awk -v max="$max_lines" '$1 > max {print}' "$tmp_all" > "$tmp_bad"

if [[ -s "$tmp_bad" ]]; then
  echo "Lean file length check failed (max ${max_lines} lines). Offenders:"
  sort -nr "$tmp_bad"
  exit 1
fi

echo "Lean file length check passed (max ${max_lines} lines)."
