#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

fail=0

have_rg=0
if command -v rg >/dev/null 2>&1; then
  have_rg=1
fi

search_matches() {
  local pattern="$1"
  local path="$2"
  if [[ "$have_rg" -eq 1 ]]; then
    rg -n "$pattern" "$path" -g "*.lean" || true
  else
    grep -R -nE "$pattern" "$path" --include='*.lean' || true
  fi
}

check_forbidden() {
  local name="$1"
  local pattern="$2"
  local path="$3"
  local matches
  matches="$(search_matches "$pattern" "$path")"
  if [[ -n "$matches" ]]; then
    echo "[FAIL] $name"
    echo "$matches"
    fail=1
  else
    echo "[PASS] $name"
  fi
}

check_required() {
  local name="$1"
  local pattern="$2"
  local path="$3"
  local matches
  matches="$(search_matches "$pattern" "$path")"
  if [[ -z "$matches" ]]; then
    echo "[FAIL] $name"
    echo "  Required pattern not found: $pattern"
    fail=1
  else
    echo "[PASS] $name"
  fi
}

check_forbidden \
  "Analytic track must not import SchemeTheoretic or GAGA" \
  '^import StringGeometry\\.RiemannSurfaces\\.(SchemeTheoretic|GAGA)' \
  'StringGeometry/RiemannSurfaces/Analytic'

check_forbidden \
  "SchemeTheoretic track must not import Analytic or GAGA" \
  '^import StringGeometry\\.RiemannSurfaces\\.(Analytic|GAGA)' \
  'StringGeometry/RiemannSurfaces/SchemeTheoretic'

check_forbidden \
  "Analytic Riemann-Roch file must stay independent" \
  '^import StringGeometry\\.RiemannSurfaces\\.(SchemeTheoretic|GAGA)' \
  'StringGeometry/RiemannSurfaces/Analytic/RiemannRoch.lean'

check_forbidden \
  "Scheme-theoretic Riemann-Roch file must stay independent" \
  '^import StringGeometry\\.RiemannSurfaces\\.(Analytic|GAGA)' \
  'StringGeometry/RiemannSurfaces/SchemeTheoretic/RiemannRoch.lean'

check_forbidden \
  "CanonicalDivisor must not smuggle degree theorem as a structure field" \
  'degree_eq[[:space:]]*:[[:space:]]*representative\\.degree' \
  'StringGeometry/RiemannSurfaces/Analytic/RiemannRoch.lean'

check_forbidden \
  "FiniteGoodCover must not bundle vanishing theorem as a structure field" \
  '^[[:space:]]+vanishing[[:space:]]*:' \
  'StringGeometry/RiemannSurfaces/GAGA/Cohomology/CechTheory.lean'

check_forbidden \
  "Point-exact bridge must not reintroduce bundled theorem-data structure" \
  '^structure PointExactData' \
  'StringGeometry/RiemannSurfaces/GAGA/Cohomology/PointExactProof.lean'

check_forbidden \
  "GAGA Riemann-Roch must not require bundled SerreDuality structure input" \
  '\(SD[[:space:]]*:[[:space:]]*SerreDuality' \
  'StringGeometry/RiemannSurfaces/GAGA/Cohomology/RiemannRoch.lean'

check_forbidden \
  "SerreDuality structure must not bundle dimension-equality theorem field" \
  '^[[:space:]]+dimension_eq[[:space:]]*:[[:space:]]*h_i[[:space:]]+pairing\\.H1D' \
  'StringGeometry/RiemannSurfaces/GAGA/Cohomology/SerreDuality.lean'

check_forbidden \
  "Cech recursion helper must not call wrapped point theorem directly" \
  'have hpt := eulerChar_point_exact_cech L gc' \
  'StringGeometry/RiemannSurfaces/GAGA/Cohomology/CechTheory.lean'

check_required \
  "CechTheory must keep explicit-assumption recursion theorem" \
  '^theorem eulerChar_point_exact_cech_of' \
  'StringGeometry/RiemannSurfaces/GAGA/Cohomology/CechTheory.lean'

check_required \
  "CechTheory must keep explicit-input Euler-characteristic formula theorem" \
  '^theorem eulerChar_formula_cech_of' \
  'StringGeometry/RiemannSurfaces/GAGA/Cohomology/CechTheory.lean'

if [[ "$fail" -ne 0 ]]; then
  echo
  echo "Riemann-Roch independence checks failed."
  exit 1
fi

echo
echo "Riemann-Roch independence checks passed."
