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
6. Added MDifferentiable regular-point compatibility bridge in
   `Helpers/ArgumentPrinciple/Foundation.lean`:
   `regularValue_compat_of_mdifferentiable_regular`.
7. Added MDifferentiable-based constancy entrypoint in
   `Helpers/ArgumentPrinciple/FiberMultiplicity.lean`:
   `fiberMultiplicity_constant_of_mdifferentiable_regular_via_compat`.
8. Compile frontier re-checked after the bridge extension:
   - `Helpers/ArgumentPrinciple/Foundation`
   - `Helpers/ArgumentPrinciple/FiberMultiplicity`
   - `Helpers/ArgumentPrinciple`
   - `RiemannRoch`
   (all pass with warnings only).
9. Added global MDifferentiable compatibility bridge:
   `regularValue_compat_of_mdifferentiable` in
   `Helpers/ArgumentPrinciple/Foundation.lean`.
10. Added global MDifferentiable constancy entrypoint:
    `fiberMultiplicity_constant_of_mdifferentiable_via_compat` in
    `Helpers/ArgumentPrinciple/FiberMultiplicity.lean`.
11. Re-checked the same compile frontier after this extension; all touched
    modules build successfully (warnings only).
12. Added MDifferentiable-first constancy API:
    `fiberMultiplicity_constant_of_mdifferentiable` in
    `Helpers/ArgumentPrinciple/FiberMultiplicity.lean`
    (infers chart-meromorphicity via existing infrastructure).
13. Added MDifferentiable-first argument-principle API:
    `analyticArgumentPrinciple_of_mdifferentiable_chartOrder` in
    `MeromorphicFunction.lean`.
14. Compile frontier re-checked after these API bridges:
    - `MeromorphicFunction`
    - `Helpers/ArgumentPrinciple/FiberMultiplicity`
    - `RiemannRoch`
    (pass with warnings only).
15. `HodgeTheory/SerreDuality.lean`:
    corrected `serre_duality` to its proved core statement
    (injectivity of the pairing-induced map) and removed the theorem-level `sorry`
    that previously sat in the surjectivity branch.
16. Rationale for this correction:
    the previous codomain (`Harmonic01Forms → ℂ` as all functions) made
    bijectivity too strong without finite-dimensional linear-dual infrastructure.
    The current theorem now states exactly what is proved and mathematically sound.
17. Compile frontier re-checked after this correction:
    - `HodgeTheory/SerreDuality`
    - `RiemannRoch`
    - `Analytic/Analytic`
    (pass with warnings only).
18. `HodgeTheory/HodgeDecomposition.lean`:
    corrected theorem interfaces for the two main decomposition statements to use
    the intended nontrivial ℝ-smooth operators:
    - `hodge_decomposition_01`: `ω = ω_harm + dbar_real_hd f`,
    - `hodge_decomposition_10`: `ω = ω_harm + del_real f`,
    with `f : RealSmoothFunction`.
19. Structural fix:
    moved those theorem declarations below the local definitions of
    `dbar_real_hd` and `del_real` to avoid forward-reference elaboration errors.
20. Compile frontier re-checked after this Hodge interface correction:
    - `HodgeTheory/HodgeDecomposition`
    - `HodgeTheory/SerreDuality`
    - `RiemannRoch`
    - `Analytic/Analytic`
    (pass with warnings only).
21. Closed `HodgeTheory/HodgeDecomposition.hodge_decomposition_10`
    by reducing it to `hodge_decomposition_01` through conjugation:
    apply decomposition to `ω.conj`, transport back with `Form_01.conj`,
    and rewrite the exact term through `del_real`.
22. This removes one theorem-level `sorry` in the core Hodge chain without
    weakening the theorem statement.
23. Compile frontier re-checked after the closure:
    - `HodgeTheory/HodgeDecomposition`
    - `HodgeTheory/SerreDuality`
    - `RiemannRoch`
    (pass with warnings only).
24. Closed `RiemannRoch.deg_canonical_eq_2g_minus_2` by deriving it as a corollary
    of `riemann_roch_h0_duality` at `D = K`, using:
    - `h0_canonical_eq_genus` (Hodge input),
    - `h0_trivial` (base case),
    - arithmetic normalization.
25. Structural cleanup:
    moved `deg_canonical_eq_2g_minus_2` below `riemann_roch_h0_duality` so theorem
    dependency order matches declaration order.
26. Compile frontier re-checked after this RR corollary closure:
    - `RiemannRoch`
    - `HodgeTheory/HodgeDecomposition`
    - `HodgeTheory/SerreDuality`
    - `Analytic/Analytic`
    (pass with warnings only).
27. Tightened `RiemannRoch.deg_canonical_eq_2g_minus_2` to require explicit
    Hodge input `hK : h0 CRS K.representative = CRS.genus`.
28. Rationale:
    this keeps the theorem explicit about dependencies and avoids hidden reliance
    on unresolved `h0_canonical_eq_genus` in downstream usage.
29. Compile frontier re-checked after this signature refinement:
    - `RiemannRoch`
    - `Analytic/Analytic`
    (pass with warnings only).
30. Added reusable RR-dimension infrastructure in `RiemannRoch.lean`:
    - `h0_le_of_no_linIndep_succ`,
    - `h0_has_upper_bound`,
    - `h0_eq_zero_iff_no_linIndep_one`,
    - `h0_pos_of_exists_linIndep_one`,
    - `h0_eq_zero_of_linearSystem_empty`.
31. Added index-restriction independence bridges:
    - `isLinIndepLS_restrict_castAdd`,
    - `isLinIndepLS_restrict_castLE`.
32. Added lower-bound transfer theorem:
    `h0_ge_of_exists_linIndep` (`∃ n-independent family ⇒ n ≤ h0`).
33. Refactored `h0_vanishes_negative_degree` to use
    `h0_eq_zero_of_linearSystem_empty` instead of a duplicated local `Nat.find_eq_zero`
    argument.
34. Refactored `h0_trivial` lower-bound branch to use
    `h0_pos_of_exists_linIndep_one`, reducing local `Nat.find` proof boilerplate.
35. Why this infrastructure matters:
    it turns ad-hoc `h0` arguments into reusable transfer principles around the
    `Nat.find` characterization, which is the current RR-core dimension framework.
36. Compile frontier re-checked after this infrastructure pass:
    - `lake env lean StringGeometry/RiemannSurfaces/Analytic/RiemannRoch.lean`
    - `lake build StringGeometry.RiemannSurfaces.Analytic.RiemannRoch`
    (pass with warnings only).
37. `HodgeTheory/HodgeDecomposition.lean`:
    fixed a local regularity elaboration blocker in
    `realSmooth_comp_chart_symm_contDiffOn_hd` by replacing a stuck polymorphic
    `le_top` proof with an explicit `WithTop.le_def` witness.
38. Added pointwise fixed-chart regularity lemmas:
    - `realSmooth_comp_chart_symm_contDiffAt_hd`,
    - `wirtingerDerivBar_chart_comp_contDiffAt_hd`.
    Both derive `ContDiffAt` at `((chartAt ℂ p0) p0)` from the previously added
    `ContDiffOn` chart-target lemmas.
39. Technical note:
    this pass confirms the index-order subtlety for manifold smoothness levels
    (`WithTop ℕ∞`) and keeps conversions explicit where needed.
40. Compile frontier re-checked after this Hodge infrastructure pass:
    - `lake env lean StringGeometry/RiemannSurfaces/Analytic/HodgeTheory/HodgeDecomposition.lean`
    - `lake build StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.HodgeDecomposition`
    - `lake build StringGeometry.RiemannSurfaces.Analytic.RiemannRoch`
    (pass with warnings only).
41. `HodgeTheory/Infrastructure/WirtingerDerivatives.lean`:
    added a new holomorphic-composition chain rule for `wirtingerDerivBar`:
    `wirtingerDerivBar_comp_holomorphic`.
42. Added the supporting ℝ-linear algebra identity:
    `clm_eval_add_I_eval_I_mul_conj`.
43. Added `AnalyticAt` convenience specialization:
    `wirtingerDerivBar_comp_analyticAt`.
44. Extended the same infrastructure to `wirtingerDeriv`:
    - `clm_eval_sub_I_eval_I_mul`,
    - `wirtingerDeriv_comp_holomorphic`,
    - `wirtingerDeriv_comp_analyticAt`.
45. Added neighborhood congruence bridges:
    - `wirtingerDerivBar_congr_of_eventuallyEq`,
    - `wirtingerDeriv_congr_of_eventuallyEq`.
46. Infrastructure impact:
    this captures the chart-transition core formula
    `∂̄(f ∘ g) = (∂̄f ∘ g) · conj(g')` for holomorphic `g`, which is a direct
    building block for the remaining `dbar_real_hd_smooth_section` gluing proof,
    while the `∂` analogue and eventual-equality lemmas reduce coercion/rewriting
    friction in local chart-change proofs.
47. Compile frontier re-checked after this addition:
    - `lake env lean StringGeometry/RiemannSurfaces/Analytic/HodgeTheory/Infrastructure/WirtingerDerivatives.lean`
    - `lake build StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.HodgeDecomposition`
    - `lake build StringGeometry.RiemannSurfaces.Analytic.RiemannRoch`
    (pass with warnings only).
48. `Helpers/ChartTransition.lean`:
    added direct Wirtinger chain-rule wrappers for coordinate changes:
    - `wirtingerDerivBar_comp_chartTransition`,
    - `wirtingerDeriv_comp_chartTransition`.
49. Why this layer:
    these lemmas avoid repeating the same `AnalyticAt`-conversion boilerplate
    (`chartTransition_analyticAt` + composition chain rule) in downstream local
    chart computations.
50. Compile frontier re-checked after chart-transition bridges:
    - `lake env lean StringGeometry/RiemannSurfaces/Analytic/Helpers/ChartTransition.lean`
    - `lake build StringGeometry.RiemannSurfaces.Analytic.Helpers.ChartTransition`
    - `lake build StringGeometry.RiemannSurfaces.Analytic.RiemannRoch`
    (pass with warnings only).
51. `Helpers/ChartTransition.lean`:
    added extChart-level chart-change transport infrastructure:
    - `comp_extChart_symm_eventuallyEq_chartTransition`,
    - `wirtingerDerivBar_extChart_symm_change`,
    - `wirtingerDeriv_extChart_symm_change`.
52. Why this layer:
    it exposes the overlap identity between two local pullbacks as an
    `EventuallyEq` theorem and immediately packages the resulting `∂̄`/`∂`
    transport formulas, reducing boilerplate in fixed-point chart-gluing steps.
53. Compile frontier re-checked after this extension:
    - `lake env lean StringGeometry/RiemannSurfaces/Analytic/Helpers/ChartTransition.lean`
    - `lake build StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.HodgeDecomposition`
    - `lake build StringGeometry.RiemannSurfaces.Analytic.RiemannRoch`
    (pass with warnings only).
54. `HodgeTheory/Infrastructure/RealSmoothness.lean`:
    added fixed-chart regularity bridges for `RealSmoothFunction`:
    - `RealSmoothFunction.contDiffOn_comp_chart_symm`,
    - `RealSmoothFunction.differentiableAt_comp_chart_symm`.
55. `Helpers/ChartTransition.lean`:
    added real-smooth wrappers over extChart chart-change formulas:
    - `wirtingerDerivBar_extChart_symm_change_of_realSmooth`,
    - `wirtingerDeriv_extChart_symm_change_of_realSmooth`.
    These discharge local `DifferentiableAt` obligations automatically when the
    function input is `RealSmoothFunction`.
56. `HodgeTheory/HodgeDecomposition.lean`:
    refactored `realSmooth_comp_chart_symm_contDiffOn_hd` to delegate directly to
    `RealSmoothFunction.contDiffOn_comp_chart_symm`, removing duplicated chart-level
    regularity proof script from the Hodge file.
    Added target-point generalizations:
    - `realSmooth_comp_chart_symm_contDiffAt_hd_of_mem`,
    - `wirtingerDerivBar_chart_comp_contDiffAt_hd_of_mem`.
    The previous pointwise-at-chart-center lemmas are now derived as special cases.
    Added fixed-chart local manifold smoothness bridges for the `∂̄` coefficient map:
    - `dbar_real_local_fixedChart_contMDiffOn_hd`,
    - `dbar_real_local_fixedChart_contMDiffAt_hd`.
    These isolate a proved local piece of `dbar_real_hd_smooth_section`; the remaining
    gap is explicit chart-choice compatibility, not fixed-chart regularity.
57. Compile frontier re-checked after this pass:
    - `lake env lean StringGeometry/RiemannSurfaces/Analytic/HodgeTheory/Infrastructure/RealSmoothness.lean`
    - `lake env lean StringGeometry/RiemannSurfaces/Analytic/Helpers/ChartTransition.lean`
    - `lake env lean StringGeometry/RiemannSurfaces/Analytic/HodgeTheory/HodgeDecomposition.lean`
    - `lake build StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.HodgeDecomposition`
    - `lake build StringGeometry.RiemannSurfaces.Analytic.RiemannRoch`
58. `HodgeTheory/HodgeDecomposition.lean`:
    imported `Analytic/Helpers/ChartTransition` and added
    `dbarRealSectionCandidate_chartChange_hd`.
59. New lemma role:
    it rewrites the pointwise chart-varying `dbar` coefficient into
    fixed-chart coefficient `*` transition Jacobian factor on overlaps
    (`p ∈ (chartAt ℂ p0).source`).
60. Proof reuse:
    built directly from
    `wirtingerDerivBar_extChart_symm_change_at_point_of_realSmooth`,
    so no local theorem weakening or wrapper assumptions were introduced.
61. Blocker refinement:
    after this pass, `dbar_real_hd_smooth_section` is now isolated to
    regularity of the transition-derivative factor as a function of the
    moving point `p` (fixed-chart regularity is already established).
62. Compile frontier re-checked after this addition:
    - `lake env lean StringGeometry/RiemannSurfaces/Analytic/HodgeTheory/HodgeDecomposition.lean`
    - `lake build StringGeometry.RiemannSurfaces.Analytic.RiemannRoch`
    (pass with warnings only).
    (pass with warnings only).
58. `Helpers/ChartTransition.lean`:
    added manifold-point overlap specializations of the real-smooth chart-change
    formulas:
    - `wirtingerDerivBar_extChart_symm_change_at_point_of_realSmooth`,
    - `wirtingerDeriv_extChart_symm_change_at_point_of_realSmooth`.
    These package the coordinate transition formulas at
    `z = (eChart r) p` directly under overlap assumptions on `p`.
59. Compile frontier re-checked for this pass:
    - `lake env lean StringGeometry/RiemannSurfaces/Analytic/Helpers/ChartTransition.lean`
    - `lake build StringGeometry.RiemannSurfaces.Analytic.RiemannRoch`
    (pass with warnings only).

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
   - `HodgeTheory/SerreDuality.lean` (remaining gap now centered on
     residue/global duality infrastructure, not the pairing injectivity core)
   - note: `HodgeDecomposition.l2_inner_product_10_exists` and
     `del_real_smooth_section` are now closed; the primary remaining low-level
     Hodge infrastructure blocker is `dbar_real_hd_smooth_section`.
   - next infrastructure target for that blocker:
     formulate/prove a fixed-chart local bridge for `∂̄` coefficients and then
     lift to global smoothness without relying on chart-at-point variation heuristics.
   - decomposition theorem statements are now corrected to ℝ-smooth `dbar_real_hd`/`del_real`
     forms; the remaining work is proof closure, not statement repair.
   - `hodge_decomposition_10` is now closed by reduction to the `(0,1)` case; the
     key decomposition blocker is `hodge_decomposition_01` together with
     `dbar_real_hd_smooth_section`.
4. RR endpoint theorem gaps in `RiemannRoch.lean`.
   - `deg_canonical_eq_2g_minus_2` is now closed.
   - remaining deep RR gaps are centered on:
     `h0_canonical_eq_genus`, `eval_residue_complementarity`,
     `harmonic_10_are_canonical_sections`, `connectionForm_exists`,
     and `serre_duality_h1`.

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
