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

## Recent progress (2026-03-02)

1. `HodgeDecomposition.del_real` was refactored to
   `del_real f := (dbar_real_hd f.conj).conj`.
2. This removed the separate `del_real_smooth_section` proof obligation and closed
   one theorem-level `sorry` in the Hodge core.
3. `del_real_add`, `del_real_zero`, `del_real_const_mul` now derive from
   `dbar_real_hd_*` linearity plus conjugation lemmas.
4. Compile frontier checked:
   - `HodgeTheory/HodgeDecomposition.lean`
   - `HodgeTheory/SerreDuality`
   - `Analytic/RiemannRoch`
   (all passing with warnings only).
5. Argument-principle constancy interface cleanup:
   - removed stale unresolved `Foundation.fiberMultiplicity_constant`;
   - added canonical proved `fiberMultiplicity_constant` in
     `Helpers/ArgumentPrinciple/FiberMultiplicity.lean` with explicit
     regular-value compatibility hypothesis.

## Current blocker clusters

1. Fiber-multiplicity bridge in `Helpers/ArgumentPrinciple.lean`
   - canonical theorem now uses explicit compatibility hypothesis:
     `fiberMultiplicity_constant` (in `FiberMultiplicity.lean`) requires
     `hcompat : f p = correctedValue ...` on regular points.
   - missing bridge target remains: derive this compatibility from natural
     analytic regularity assumptions in the core chain (not ad hoc wrappers).
   - continuity-based and compatibility-based variants are both available;
     remaining deep task is promoting them to the strongest intended hypothesis
     profile for RR consumers.
2. AMF/global-argument-principle interface
   - bridge now available:
     `MeromorphicFunction.analyticArgumentPrinciple_of_chartData`
     (chart-meromorphic regularValue + chart/order compatibility).
   - `MeromorphicFunction.analyticArgumentPrinciple` is now the
     hypothesis-explicit interface (no theorem-level `sorry` in this declaration).
   - practical impact:
     `LineBundles.linearSystem_empty_negative_degree` now uses this chart-data
     bridge directly, reducing dependence on underdetermined abstract AMF claims.
3. Hodge/duality infrastructure theorem gaps in:
   - `HodgeTheory/DolbeaultCohomology.lean`
   - `HodgeTheory/HodgeDecomposition.lean`
   - `HodgeTheory/SerreDuality.lean`
   - note: `HodgeDecomposition.l2_inner_product_10_exists` and
     `del_real_smooth_section` are now closed; the primary remaining low-level
     Hodge infrastructure blocker is `dbar_real_hd_smooth_section`.
4. RR endpoint theorem gaps in `RiemannRoch.lean`.

## Working method

1. Prove local lemmas first; avoid long monolithic proofs.
2. Prefer robust type-stable rewrites (explicit casts and neighborhoods).
3. Keep theorem statements fixed when coherent; if a statement is currently
   underdetermined by available infrastructure, prefer explicit hypotheses over
   hidden proof gaps.
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
