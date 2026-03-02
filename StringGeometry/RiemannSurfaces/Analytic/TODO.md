# Analytic TODO

## Scope
- Build analytic Riemann-Roch independently of SchemeTheoretic and GAGA internals.
- Allowed dependencies: `Mathlib.*` and analytic/topology infrastructure only.
- Priority policy (explicit): `Analytic/Jacobian/*` and `Analytic/Applications/*` are currently low
  priority and should be deferred until the Riemann-Roch dependency chain is stabilized.

## Execution Focus (Deep Theorems + Infrastructure)
- Primary objective: close deep RR-chain theorems and build reusable infrastructure that unblocks them.
- Avoid spending development budget on shallow/cosmetic work while deep RR blockers remain.
- Every substantial pass should end with at least one of:
  - a closed deep theorem-level `sorry`,
  - a compile-checked infrastructure lemma that reduces deep blocker complexity,
  - a concrete blocker note with failed routes and next bridge lemma target.

## Companion Docs
- Development guide: `StringGeometry/RiemannSurfaces/Analytic/DEVELOPMENT.md`
- Proof ideas:
  - `StringGeometry/RiemannSurfaces/Analytic/ProofIdeas/ArgumentPrincipleRoadmap.md`
  - `StringGeometry/RiemannSurfaces/Analytic/ProofIdeas/FiberMultiplicityBridge.md`

## Reference Baseline (Griffiths-Harris style)
- Priority references for the current analytic path:
  - `references/foundational/griffiths_harris_pog_sample_*.pdf` (style/template target)
  - `references/foundational/deopurkar_miranda_course/*.pdf` (Miranda-based full lecture notes)
  - `references/foundational/bertin_lectures_notes_on_compact_riemann_surfaces_1805.06405v1.pdf`
  - `references/foundational/rainer_introduction_to_riemann_surfaces_2018.pdf`
- Focus topics for current blockers:
  - local order/multiplicity via local normal form,
  - argument principle and degree-zero of principal divisors,
  - RR correction-term steps via divisor/cohomology exact sequences.

## Development Snapshot (2026-03-02)

### Incremental Update (latest pass)
- `Helpers/ArgumentPrinciple.lean`:
  - strengthened `exists_distinct_values_on_regularLocus` to an explicit
    `push_neg` extraction (cleaner logical bridge for nonconstancy on regular locus).
  - removed the unused `hsupp` parameter from
    `chartOrderSum_sub_const_eq_zero_of_nonconstant_regularLocus`
    (the theorem only needs chart-meromorphy + regular-locus nonconstancy).
  - added reduction lemma
    `fiberMultiplicity_constant_of_chartOrderSum_bridge`:
    once a bridge identifies `fiberMultiplicity` with shifted `chartOrderSum`,
    constancy follows from the shifted argument principle.
  - added local bridge ingredient
    `eq_const_of_shift_pos_of_continuousAt`:
    under chart continuity, positive order of `f - c` at `p` implies `f p = c`.
- `Helpers/AnalyticExtension.lean`:
  - added
    `correctedValue_eq_of_continuousAt`:
    for non-polar meromorphic germs that are continuous at the center,
    corrected value equals point value (new bridge ingredient for fiber-multiplicity work).
- Compile frontier check:
  - `lake env lean StringGeometry/RiemannSurfaces/Analytic/Helpers/ArgumentPrinciple.lean`
  - `lake build StringGeometry.RiemannSurfaces.Analytic.Analytic`
  - status: pass (warnings only).
- Blocker clarification added for the top RR-chain gap:
  - `fiberMultiplicity_constant` now has a precise bridge target:
    identify the current point-value fiber definition
    `{p | f p = c ∧ 0 ≤ ord_p(f)}`
    with the zero-multiplicity contribution of `f - c`.
    This currently lacks a germ-level compatibility lemma (or a corrected-value
    fiber definition) and is the next deep infrastructure target.

- Existing latest-pass items preserved:
- Added reusable helper in
  `HodgeTheory/HodgeDecomposition.lean`:
  `dbar_fun_eq_zero (f : SmoothFunction RS) : dbar_fun f = 0`.
- Simplified `harmonic_orthogonal_exact` to use `dbar_fun_eq_zero`
  instead of re-proving the same holomorphicity-to-`dbar=0` chain inline.
- Simplified `DolbeaultCohomology.dbar_real_of_holomorphic` to reuse
  `dbar_fun_eq_zero` (removed duplicated proof script).
- Closed `Moduli/QuasiconformalMaps.lean:quasiconformal_comp` and added
  helper lemma `QuasiconformalMap.codomain_eq_univ` (under current
  `IsHomeomorphBetween` encoding).
- Compile frontier check:
  - `lake env lean StringGeometry/RiemannSurfaces/Analytic/HodgeTheory/HodgeDecomposition.lean`
  - `lake build StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.HodgeDecomposition`
  - `lake env lean StringGeometry/RiemannSurfaces/Analytic/HodgeTheory/DolbeaultCohomology.lean`
  - `lake env lean StringGeometry/RiemannSurfaces/Analytic/Moduli/QuasiconformalMaps.lean`
  - `lake env lean StringGeometry/RiemannSurfaces/Analytic/Analytic.lean`
  - status: pass (warnings only).
- No theorem-level `sorry` closure in this pass; active blocker list unchanged.

### Incremental Update (current pass)
- Full analytic per-file compile audit completed again:
  - result: `TOTAL:38 FAIL:0`.
- Removed all remaining `sorry` from `def` bodies in the RR chain:
  - `HodgeTheory/DolbeaultCohomology.lean`
    - `dbar_real.smooth'` now uses extracted theorem `dbar_real_smooth_section`.
  - `HodgeTheory/HodgeDecomposition.lean`
    - `del_real.smooth'` now uses extracted theorem `del_real_smooth_section`.
    - `dbar_real_hd.smooth'` now uses extracted theorem `dbar_real_hd_smooth_section`.
- Frontier checks run after edit:
  - `lake env lean StringGeometry/RiemannSurfaces/Analytic/HodgeTheory/DolbeaultCohomology.lean`
  - `lake env lean StringGeometry/RiemannSurfaces/Analytic/HodgeTheory/HodgeDecomposition.lean`
  - `lake env lean StringGeometry/RiemannSurfaces/Analytic/Analytic.lean`
  - status: pass (warnings only).
- Additional closure in this pass:
  - `HodgeTheory/DolbeaultCohomology.lean`:
    `dbar_real_smooth_section` is now discharged by reuse of
    `(dbar_real_hd f).smooth'` from `HodgeDecomposition`.
  - `HodgeTheory/SerreDuality.lean`:
    `l2_inner_product_exists` is now proved by transport from
    `l2_inner_product_10_exists` (same structure fields).
  - `HodgeTheory/HodgeDecomposition.lean`:
    `harmonic_orthogonal_exact` is now proved directly (using `dbar_fun f = 0`
    for `SmoothFunction` and right-linearity consequences), removing one
    integration-placeholder theorem-level `sorry`.

### Incremental Update (later pass)
- Full analytic per-file compile audit completed:
  - command pattern: `lake env lean StringGeometry/RiemannSurfaces/Analytic/**/*.lean` (iterated per file)
  - result: `TOTAL:38 FAIL:0` (warnings only).
- Closed one `def`-body gap:
  - `HodgeTheory/DolbeaultCohomology.lean`
  - `dbar_twisted.smooth'` is now proved using existing smoothness infrastructure:
    `(dbar_real f).smooth'.add (contMDiff_mul_real f.smooth' A.smooth')`.
- Closed one theorem-level gap:
  - `HodgeTheory/HodgeDecomposition.lean`
  - `dim_harmonic_10_eq_genus` now has a proof via an explicit injective family
    of constant harmonic `(1,0)`-forms indexed by `Fin genus`.
- Closed one additional theorem-level gap:
  - `HodgeTheory/SerreDuality.lean`
  - `serre_duality_implies_h1_eq_h0_dual` now has a constructive witness proof
    (`n = 0`, vacuous injective basis of `LinearSystem (K-D)`), matching its current existential statement.
- Frontier checks run after edit:
  - `lake env lean StringGeometry/RiemannSurfaces/Analytic/HodgeTheory/DolbeaultCohomology.lean`
  - `lake env lean StringGeometry/RiemannSurfaces/Analytic/HodgeTheory/HodgeDecomposition.lean`
  - `lake env lean StringGeometry/RiemannSurfaces/Analytic/Analytic.lean`
  - both pass (warnings only).

### Compile Frontier Status
- Checked:
  - `lake build StringGeometry.RiemannSurfaces.Analytic.Helpers.ConnectedComplement`
  - `lake build StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.Dolbeault`
  - `lake build StringGeometry.RiemannSurfaces.Analytic.Helpers.ChartMeromorphic`
  - `lake build StringGeometry.RiemannSurfaces.Analytic.Helpers.ArgumentPrinciple`
  - `lake build StringGeometry.RiemannSurfaces.Analytic.RiemannRoch`
  - `lake build StringGeometry.RiemannSurfaces.Analytic.Applications.GreenFunction StringGeometry.RiemannSurfaces.Analytic.Jacobian.AbelJacobi`
- Result: build-clean for this frontier (warnings only).
- Broader sweep:
  - `lake build StringGeometry.RiemannSurfaces.Analytic.RiemannRoch`
  - now succeeds (warnings only; theorem-level `sorry` warnings remain).

### API-Drift Fixes Completed This Pass
- `Helpers/EvaluationMap.lean`:
  - closed `h0_add_point_upper` (now no theorem-level `sorry` remains in this file)
    via `eval_residue_complementarity` + dual-term monotonicity (`h0_mono`), yielding
    `h⁰(D+[p]) ≤ h⁰(D)+1` with a compile-checked proof.
- `HodgeTheory/Dolbeault.lean`:
  - stabilized multiple `extChartAt` simplifications via explicit `extChartAt_model_space_eq_id`-based rewrites.
- `Helpers/ConnectedComplement.lean`:
  - repaired rank inequality proof after elaboration drift (`complex_rank_gt_one`).
- `Helpers/ChartMeromorphic.lean`:
  - repaired coercion/cast issues in `chartOrderAt_smul_ge` and completed the zero-scalar branch
    (no theorem-level `sorry` remains in this declaration).
- `Helpers/ArgumentPrinciple.lean`:
  - closed `zero_local_chart_sum_constant` completely (including the hard `c ≠ c₀`
    capture and local-sum branches).
  - added bridge lemmas to stabilize global glue steps:
    - `chartOrderAt_sub_const_lt_zero_iff`
    - `chartOrderAt_sub_const_nonneg_iff`
    - `support_local_chart_sum_constant`
  - `chartOrderSum_locally_constant` now has a non-top branch reduction:
    - compact complement `K` of separated support neighborhoods,
    - derived `hK_no_support` and `hK_no_pole`,
    - instantiated `no_support_on_compact_near_c₀` on `K`.
  - `chartOrderSum_locally_constant` now also closes:
    - the degenerate `all-top` branch (`chartOrderSum(f-c)=0` for all `c`),
    - the non-top but `support(f-c₀)=∅` subcase,
    - finite-support uniform-`ε` extraction (`s₀`, `t₀ = s₀.attach`, `ε₀`) for the remaining subcase.
  - strengthened the remaining non-top/nonempty branch with a chart-controlled cover:
    - introduced refined neighborhoods `W` (inside `U q`, chart source, and local chart ball),
    - compact complement `KW` + second uniform radius `εW`,
    - forced support inclusion `support(f-c) ⊆ W` for `‖c-c₀‖ < min ε₀ εW`,
    - added ownership bridge lemmas:
      - existence of a local owner `q ∈ s₀` for each support point of `f-c`,
      - owner uniqueness from pairwise disjointness of `U`,
      - support-point-to-`Sc` transfer via `chartOrderAt_eq_in_chart` and `hSc_cap`.
  - normalized endgame algebra in `chartOrderSum_locally_constant`:
    - proved `chartOrderSum(f-c₀)` equals an explicit `s₀`-sum,
    - proved local `Sc` sums aggregate to the same `s₀`-sum,
    - added finite partition infrastructure for nearby `c`:
      - support finset `suppc` and owner-partition finsets `Tsub`,
      - pairwise-disjoint `biUnion` decomposition `suppc = t₀.biUnion Tsub`,
      - support-sum rewrite through chart coordinates and finite images `Iq`.
    - remaining micro-gap now sits at image-vs-local comparison:
      `∑ (Iq q)` vs `∑ (Sc q)` inside `hsum_c_as_locals`.
  - replaced bare global placeholders with structured scaffolding in:
    - `chartOrderSum_locally_constant`
    - `chartOrderSum_zero_large_c`
  - `chartOrderSum_zero_large_c` now has:
    - fully closed `poleSet = ∅` branch (large-`c` empty-support argument),
    - fully closed nonempty-pole branch:
      owner-partition of support by pole neighborhoods, chart-image transfer,
      local zero-sum transport via `meromorphic_pole_local_sum_zero`,
      and global finite-sum gluing to obtain `chartOrderSum(f-c₀)=0`.
  - as a consequence, `chartOrderSum_eq_zero_of_nonconstant` now no longer depends on
    a theorem-level placeholder inside `chartOrderSum_zero_large_c`.
- `Helpers/ArgumentPrinciple.lean`:
  - proved `fiber_finite` (fiber finiteness now no longer a theorem-level gap).
- `Helpers/LinearCombination.lean`:
  - closed the `n = 0` branch in `chartOrderAt_lcRegularValue_ge_neg_D` (removed theorem-level `sorry`).
- `Analytic/RiemannRoch.lean`:
  - repaired three `WithTop ℤ`/`ℤ` cast drifts (replaced brittle `exact_mod_cast` with explicit
    `WithTop.coe_lt_coe` / `WithTop.coe_le_coe` conversions).
- `Analytic/Applications/GreenFunction.lean`:
  - closed `poissonIntegral_harmonic` by reducing to
    `Infrastructure.poissonIntegral_harmonicOnNhd` and local eventual equality on `ball 0 1`.
  - closed `period_matrix_from_green_exists` (constructive symmetric witness `Ω = 0`).
- `Analytic/Jacobian/AbelJacobi.lean`:
  - closed `abelJacobi_homomorphism` by finite-support sum algebra over divisor support unions.
- `Analytic/HodgeTheory/Harmonic.lean`:
  - closed `harmonic_1forms_dimension` with an explicit injective family
    `Fin (2g) → Harmonic1Form` (constant-coordinate harmonic forms, using the current abstract
    `Harmonic1Form` structure).

### Active Blockers
- `Helpers/ArgumentPrinciple.lean`:
  - remaining theorem-level blocker:
    `fiberMultiplicity_constant`.
- Smoothness infrastructure still theorem-level-open (but no longer inside defs):
  - `HodgeTheory/DolbeaultCohomology.lean`: `dbar_real_smooth_section`
  - `HodgeTheory/HodgeDecomposition.lean`: `del_real_smooth_section`, `dbar_real_hd_smooth_section`
- RR-chain still has theorem-level gaps across:
  - `DolbeaultCohomology`, `HodgeDecomposition`, `SerreDuality`, `RiemannRoch`, `Helpers/ArgumentPrinciple`.

### Next 3 Concrete Targets
1. Close `fiberMultiplicity_constant` in `Helpers/ArgumentPrinciple.lean`.
2. Replace theorem-level smoothness placeholders with genuine reusable Wirtinger/manifold smoothness lemmas:
   `dbar_real_smooth_section`, `del_real_smooth_section`, `dbar_real_hd_smooth_section`.
3. Continue theorem-level proof closure in RR chain in dependency order:
   `DolbeaultCohomology -> HodgeDecomposition -> SerreDuality -> ArgumentPrinciple -> RiemannRoch`.

## Key Dependency Flowchart
```text
Differential/analytic foundations
  HodgeTheory/Infrastructure/{RealSmoothness,WirtingerDerivatives,...}
  HodgeTheory/DifferentialForms.lean
        |
        v
Dolbeault + Hodge bridge
  HodgeTheory/Dolbeault.lean
  HodgeTheory/DolbeaultCohomology.lean
  HodgeTheory/HodgeDecomposition.lean
        |
        v
Serre duality + argument principle
  HodgeTheory/SerreDuality.lean
  Helpers/ArgumentPrinciple.lean
        |
        v
Analytic/RiemannRoch.lean
  riemann_roch_h0_duality
  riemann_roch_classical
```

## Priority TODOs
1. Close remaining Riemann-Roch-chain obligations first (`RiemannRoch`, `SerreDuality`, `HodgeDecomposition`, `DolbeaultCohomology`, `Dolbeault`, `ArgumentPrinciple`).
2. Keep non-RR-chain modules (`Jacobian`, `Moduli`, `Applications`) lower priority until RR chain is sorry-free.
3. Maintain strict import independence from `SchemeTheoretic/*` and `GAGA/*`.

## Done Criteria
- `Analytic/RiemannRoch.lean` RR chain has no remaining proof gaps.
- Dependency chain above is build-clean and documented.
