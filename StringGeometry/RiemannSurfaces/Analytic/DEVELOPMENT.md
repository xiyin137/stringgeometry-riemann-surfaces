# Analytic Development Guide

This document tracks implementation strategy for the analytic Riemann-surface path.

## Scope and architecture

1. `Analytic/*` is developed independently from `SchemeTheoretic/*`.
2. Cross-track comparison lives in `GAGA/*` only.
3. The analytic RR chain should be internally complete before relying on bridge results.
4. `Analytic/Jacobian/*` and `Analytic/Applications/*` are low priority until the RR chain is stabilized.

## Development focus

1. Emphasize deep theorem closure and reusable infrastructure over shallow cleanup.
2. Prioritize RR-chain blockers with highest dependency impact.
3. Treat API-drift fixes as infrastructure work only when they directly unblock deep proofs.
4. Defer peripheral-module enhancements until RR-chain progress is concrete.

## Active chain (dependency order)

1. `HodgeTheory/Dolbeault.lean`
2. `HodgeTheory/DolbeaultCohomology.lean`
3. `HodgeTheory/HodgeDecomposition.lean`
4. `HodgeTheory/SerreDuality.lean`
5. `Helpers/ArgumentPrinciple.lean`
6. `RiemannRoch.lean`

## Current blocker clusters

1. Fiber-multiplicity bridge in `Helpers/ArgumentPrinciple.lean`
   - `fiberMultiplicity_constant`
   - missing bridge target: connect point-value fibers
     `{p | f p = c ∧ 0 ≤ ord_p(f)}`
     to the germ-level zero multiplicity of `f - c` (likely via corrected-value infrastructure).
   - continuity-based variant is now available:
     `fiberMultiplicity_constant_of_continuous_regular`;
     remaining gap is removing/justifying this extra regularity assumption.
2. Hodge/duality infrastructure theorem gaps in:
   - `HodgeTheory/DolbeaultCohomology.lean`
   - `HodgeTheory/HodgeDecomposition.lean`
   - `HodgeTheory/SerreDuality.lean`
3. RR endpoint theorem gaps in `RiemannRoch.lean`.

## Working method

1. Prove local lemmas first; avoid long monolithic proofs.
2. Prefer robust type-stable rewrites (explicit casts and neighborhoods).
3. Keep theorem statements fixed; no definition weakening.
4. Theorem-level `sorry` is allowed for unresolved mathematics; never hide gaps in defs.

## Compile discipline

1. Never run bare `lake build`.
2. For each change, run:
   - touched module build,
   - nearest umbrella module build.
3. Update `TODO.md` when blocker status changes.

## Reference orientation

Use foundational notes aligned with Griffiths-Harris style:

1. `references/foundational/deopurkar_miranda_course/*.pdf`
2. `references/foundational/bertin_lectures_notes_on_compact_riemann_surfaces_1805.06405v1.pdf`
3. `references/foundational/rainer_introduction_to_riemann_surfaces_2018.pdf`

For extraction/search:

- `python3 read_references.py`
- `python3 read_references.py --search "<term>"`
