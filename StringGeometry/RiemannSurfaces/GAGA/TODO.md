# GAGA TODO

## Scope
- Keep GAGA as the transport/equivalence layer between analytic and algebraic viewpoints.
- Avoid reintroducing theorem-bearing data structures as hidden assumptions.

## Current Status
- `ToCompactAlgebraicCurve.lean` has been API-aligned with current SchemeTheoretic naming/instances and now builds again.
- SchemeTheoretic dependency cleanup removed direct `:= sorry` definition placeholders in the sheaf/duality stack, reducing bridge breakage from placeholder definitions.
- Removed the over-strong `localParameter_nonpos_away` field from compact-curve structures and bridge constructors; this drops one bridge blocker that did not represent a general smooth-projective-curve property.
- Remaining open theorems in that bridge are:
  - `scheme_argumentPrinciple`
  - `scheme_regularIsConstant`
  - `scheme_leadingCoefficientUniqueness`
- These are the immediate blockers for removing bridge-level placeholders without smuggling assumptions.
- File-size policy update:
  - split `AlgebraicCurves/Cohomology/PointExactSequence.lean` into:
    - `PointExactSequence/Core.lean`
    - `PointExactSequence/Constraint.lean`
    - with `PointExactSequence.lean` as a thin compatibility import file.
  - `scripts/check_lean_file_length.sh 2000` now passes for the repository.
  - compile note: current `PointExactSequence/*` frontier is blocked by pre-existing
    `AlgebraicCurves/Cohomology/AlgebraicCech.lean` instance-synthesis failures
    (missing `Module`/`Module.Finite`/`IsNoetherian` instances for `RiemannRochSubmodule`),
    not by the file split.

## Key Dependency Flowchart
```text
Bridge layer
  Bridge/{DivisorCoreBridge,ToSmoothProjectiveCurve,EulerCharBridge,...}
  AlgebraicStructure.lean
        |
        v
Cech/cohomology transport
  Cohomology/{MathlibBridge,GeneralCechBridge,ExactSequence,PointExactProof}.lean
  Cohomology/CechTheory.lean
        |
        v
Euler-char recursion + RR statements
  CechTheory.point_recursion_cech(_of_data/_of_exists)
  CechTheory.eulerChar_formula_cech(_of)
  Cohomology/RiemannRoch.lean (riemann_roch_* family)
        |
        v
Top-level transfer
  GAGA/Basic.lean
  riemann_roch_gaga_transfer
```

## Priority TODOs
1. Keep the explicit-data RR pathway (`*_from_point_exact_data`) as the canonical proof route.
2. Ensure point-exact recursion and Euler-characteristic formulas remain theorem-driven (not bundled assumptions).
3. Keep bridge theorems thin and compositional so SchemeTheoretic/Analytic changes do not fork logic.
4. Maintain one-way architecture: GAGA consumes results; it does not own core model definitions.
5. Keep enforcing the 2000-line Lean file policy in GAGA for future growth.

## Done Criteria
- GAGA RR transfer theorems build with explicit dependency data.
- No hidden assumption bundles are introduced in bridge/cohomology layers.
- This TODO remains the single planning/status document in `GAGA/`.
