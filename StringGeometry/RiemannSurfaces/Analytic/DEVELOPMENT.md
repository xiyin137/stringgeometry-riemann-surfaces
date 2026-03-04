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
2. `HodgeTheory/HodgeDecomposition/Core.lean`
3. `HodgeTheory/HodgeDecomposition/DeRhamCore.lean`
4. `HodgeTheory/HodgeDecomposition/ExactPair.lean`
5. `HodgeTheory/HodgeDecomposition/DimensionGenus.lean`
6. `HodgeTheory/HodgeDecomposition/DeRhamBridge.lean`
7. `HodgeTheory/HodgeDecomposition/InnerProductAndDolbeault.lean`
8. `HodgeTheory/DolbeaultCohomology.lean`
9. `HodgeTheory/SerreDuality.lean`
10. `Helpers/ArgumentPrinciple.lean`
11. `RiemannRoch.lean`

## RR Path Status (2026-03-04)

### Compile status
1. `lake build StringGeometry.RiemannSurfaces.Analytic.RiemannRoch`: passes.
2. Status is warning-only from theorem-level `sorry`s (no def-level placeholders introduced by recent passes).
3. `lake build StringGeometry.RiemannSurfaces`: passes (2026-03-04, warning-only).
4. `scripts/check_lean_file_length.sh 2000`: passes; `HodgeDecomposition/Core.lean` is 1845 lines.

### Dependency gates
1. Gate A (local analytic infrastructure for `∂̄`): substantially advanced.
   - Fixed-chart overlap transition-factor smoothness/nonvanishing API is in place.
   - Remaining blocker is global moving-selector smoothness closure:
     `HodgeTheory/HodgeDecomposition/Core.lean::dbarRealTransitionFactor_contMDiffAt_hd`.
2. Gate B (Hodge decomposition core):
   - `hodge_decomposition_10` is closed.
   - `hodge_decomposition_01` remains open and is the main upstream blocker.
3. Gate C (Dolbeault/Hodge identification):
   - `dolbeault_hodge_iso` is now closed as a transport theorem from
     `dolbeault_isomorphism_01` plus `SheafH1O_eq_DolbeaultH01`.
   - Remaining deep blocker in this gate is now concentrated in
     `HodgeTheory/HodgeDecomposition/InnerProductAndDolbeault.lean::dolbeault_isomorphism_01`.
   - Exact-harmonic `(0,1)` vanishing is now centralized in
     `HodgeTheory/HodgeDecomposition/Core.lean::exact_harmonic01_vanishes`
     and consumed by Gate C bridge theorems.
   - New infrastructure added for harmonic `(0,1)` algebra symmetry and conjugation equivalences:
     `harmonicSubmodule01`, `Harmonic01Forms.equivSubmodule`,
     `conjugate_harmonic_equiv`, `conjugate_harmonic_submodule_equiv`,
     `dim_harmonic_01_eq_genus`.
   - New transported algebra/linear API for harmonic subtype carriers:
     `AddCommMonoid`/`Module ℂ` instances on `Harmonic10Forms` and `Harmonic01Forms`,
     plus `Harmonic10Forms.linearEquivSubmodule` and
     `Harmonic01Forms.linearEquivSubmodule`.
4. Gate D (`h¹(O)=g` closure):
   - `DolbeaultCohomology.h1_trivial_eq_genus` is now discharged through core criteria.
   - Remaining deep obligations are split between:
     1) `HodgeTheory/HodgeDecomposition/Core.lean::exact_harmonic01_vanishes`
        (`∂̄f` harmonic implies `∂̄f=0`),
     2) `HodgeTheory/HodgeDecomposition/DimensionGenus.lean::finrank_harmonic10_eq_genus`.
   - New bridge in `DolbeaultCohomology`:
     `dolbeault_has_genus_injective_family_of_bijective`,
     `dolbeault_has_genus_injective_family`,
     `h1_trivial_eq_genus_of_linearMap_bijective`.
5. Gate E (Serre duality integration bridge):
   - `HodgeTheory/SerreDuality.lean::residue_theorem` remains open (Stokes-level requirement).
6. Gate F (RR terminal theorems in `RiemannRoch.lean`):
   - Remaining theorem-level `sorry`s are concentrated at lines currently around
     `605`, `1057`, `1467`, `1534`, `1554`, each depending on earlier gates (B-D, E).
   - The point-step complementarity block is now reduced to one explicit deep obligation:
     `exists_evalResidueFiveTermMaps_and_ids`.
     `exists_evalResidueFiveTermData` is now composed from this package.
   - Divisor-level twisted-Dolbeault wrappers were tightened to explicit witness form:
     `serre_duality_h1_of_divisor` and `riemann_roch_classical_of_divisor` now return
     `∃ A, IsConnectionFormFor CRS D A ∧ ...` rather than exposing theorem-level `.choose`
     in statement shape.
   - Active model-risk note:
     current `IsConnectionFormFor` asks for local `1/\\bar z` singular behavior in an
     ambient type `Form_01` that is globally smooth; this mismatch is likely the core blocker
     behind `connectionForm_exists` and should be resolved via a representation refactor.

### Immediate hard targets (next pass)
1. Gate A closure path:
   add a selector-independent globalization lemma for `dbarRealSectionCandidate_hd`
   using the existing fixed-chart overlap API, so the universal `dbar_real_hd` smoothness
   theorem no longer depends on the moving-selector transition factor.
2. Gate B closure path:
   split `hodge_decomposition_01` into explicit helper lemmas
   (existence + exactness + harmonicity package) and close at least one helper without `sorry`.
3. Gate C/D bridge path:
   close the centralized core-level criteria used by both bridges:
   - `HodgeTheory/HodgeDecomposition/Core.lean::exact_harmonic01_vanishes`,
   - `HodgeTheory/HodgeDecomposition/Core.lean::closed_exactPair_commonPotential`
     (now reduced by infrastructure to an unconditional mixed-identity gap).
4. Gate F model repair path:
   refactor the connection-form encoding so twisted Dolbeault uses a mathematically coherent
   object (smooth connection in a smooth trivialization + meromorphic gauge data) before
   attempting to close `connectionForm_exists`/`serre_duality_h1`.

### Latest infrastructure step (2026-03-04)
1. Refined RR Gate F dependency decomposition in `RiemannRoch.lean`:
   - added deep-data anchor theorem `exists_evalResidueFiveTermData_core`.
   - map+id existence (`exists_evalResidueFiveTermMaps_and_ids`) now derives from full
     five-term data via `toMaps` and `toFinrankIdentifications`.
   - rewired `eval_residue_complementarity` and
     `Helpers/EvaluationMap.h0_add_point_upper` to consume full data directly.
   - refactored twisted-Dolbeault `h¹` API to explicit connection-form input:
     `h1_dolbeault CRS A`, with `serre_duality_h1`/`riemann_roch_classical`
     now parameterized by `(A, hA : IsConnectionFormFor CRS D A)` to avoid
     definition-level witness choice from unresolved existence.
   - added compile-checked base-case connection lemmas for the trivial divisor:
     `isConnectionFormFor_zero` and `connectionForm_exists_zero`.
   - added `EvalResidueFinrankIdentifications`,
   - consolidated to theorem-level obligation
     `exists_evalResidueFiveTermMaps_and_ids`,
   - rewired `exists_evalResidueFiveTermData` as an explicit composition through
     `EvalResidueFiveTermMaps.toData`.
2. This keeps the blocker explicit while avoiding an unnecessarily strong
   “for all map packages” rank-identification requirement.
3. Added chart-local `WithinAt` smoothness bridges in
   `HodgeTheory/HodgeDecomposition/Core.lean`:
   - `dbarRealSectionCandidate_contMDiffWithinAt_of_chartAt_eventuallyEq_hd`
   - `dbarRealSectionCandidate_contMDiffWithinAt_of_chartAtLocallyConstant_hd`
4. Added global `ContMDiffOn` assembly lemmas and rewired the existing global
   chart-stabilized smoothness theorems through them:
   - `dbarRealSectionCandidate_contMDiffOn_of_chartAt_eventuallyEq_hd`
   - `dbarRealSectionCandidate_contMDiffOn_of_chartAtLocallyConstant_hd`
   - `dbar_real_hd_smooth_section_of_chartAt_eventuallyEq`
   - `dbar_real_hd_smooth_section_of_chartAtLocallyConstant`
5. Added C/D finrank transport bridges:
   - `Harmonic10Forms.finrank_eq_submodule_finrank`
   - `Harmonic01Forms.finrank_eq_submodule_finrank`
   - `h1_trivial_eq_genus_of_linearEquiv` (in `DolbeaultCohomology.lean`)
6. Added harmonic-to-de Rham infrastructure in
   `HodgeTheory/HodgeDecomposition/Core.lean` and
   `HodgeTheory/HodgeDecomposition/DeRhamBridge.lean`:
   - `del_01_eq_zero_of_isHarmonic01`
   - `harmonicPair_mem_closedForms1`
   - `harmonicPairClosedRep`
   - `harmonicPairToDeRham`
   - `harmonicPairToDeRham_eq_iff`
   - `hodge_isomorphism` now explicitly uses `harmonicPairToDeRham`; remaining gap is
     bijectivity only.
   - corrected the harmonic-side domain model from Lean `Sum` (`⊕`, disjoint union) to
     product `Harmonic10Forms × Harmonic01Forms`, matching the intended direct-sum data.
7. Added de Rham quotient interface lemmas in
   `HodgeTheory/HodgeDecomposition/Core.lean`:
   - `exactClosedForms1AddSubgroup`
   - `deRham_mk_eq_mk_iff`
   - `deRham_mk_eq_zero_iff`
   These give explicit criteria for class equality/vanishing in `DeRhamH1` and
   are intended to support the future injectivity branch of `hodge_isomorphism`.
8. Added hodge/de Rham reduction criteria in
   `HodgeTheory/HodgeDecomposition/DeRhamBridge.lean`:
   - `harmonicPairToDeRham_surjective_of_cohomologous_harmonicPair`
   - `harmonicPairToDeRham_surjective_of_hodgeDecomposition_and_commonPotential`
   - `harmonicPairToDeRham_injective_of_exact_kernel`
   - `harmonicPairToDeRham_injective_of_exact_kernel_exists`
   - `harmonicPairToDeRham_injective_of_exact_harmonicPair_vanishes`
   - `harmonicPairToDeRham_bijective_of_cohomologous_harmonicPair_of_exact_kernel`
   - `harmonicPairToDeRham_bijective_of_hodgeDecomposition_and_commonPotential_and_exact_harmonicPair_vanishes`
   - `hodge_isomorphism_of_commonPotential_and_exact_harmonicPair_vanishes`
   These isolate `hodge_isomorphism` into two explicit obligations:
   a common-potential compatibility bridge for closed componentwise-exact pairs,
   and exact-harmonic vanishing (`(∂f, ∂̄f)` harmonic implies zero).
   The `hodge_isomorphism` proof body now delegates to the combined packaging theorem
   `hodge_isomorphism_of_commonPotential_and_exact_harmonicPair_vanishes`, with the
   same two deep obligations isolated as theorem-level `sorry`s.
7. Structural split:
   - created `HodgeTheory/HodgeDecomposition/DeRhamBridge.lean` for the de Rham bridge layer.
   - `HodgeTheory/HodgeDecomposition.lean` now imports `DeRhamBridge`.
   - file-size policy re-check passes (`Core.lean` back under 2000 lines).
8. Purpose:
   these are direct local-to-global assembly hooks for later `contMDiff_iff` chart
   gluing, plus linear-structure-aware bridges for the Dolbeault finrank closure path.
9. Additional closure step:
   - closed `DolbeaultCohomology.dolbeault_hodge_iso` by transporting
     `dolbeault_isomorphism_01` across `SheafH1O_eq_DolbeaultH01` and inverting the induced
     equivalence.
   - added reusable equivalence wrappers for downstream proofs:
     `DolbeaultCohomology.dolbeaultHodgeEquiv`,
     `HodgeDecomposition/DeRhamBridge.hodgeIsomorphismEquiv`.
   - generalized quotient codomains to universe-polymorphic `Type _` in:
     `HodgeTheory/HodgeDecomposition/InnerProductAndDolbeault.lean::SheafH1O`,
     `HodgeTheory/HodgeDecomposition/Core.lean::DeRhamH1`.
11. Added Gate D and Gate F criterion theorems to isolate deep obligations:
   - `DolbeaultCohomology.h1_trivial_eq_genus_of_linearMap_bijective`.
   - `DolbeaultCohomology.h1_trivial_eq_genus` now reduces to:
     1) existence of a linear bijection `DolbeaultH01 →ₗ Harmonic01Forms`,
     2) harmonic `(0,1)` finrank identity.
   - `RiemannRoch.h0_canonical_eq_genus_of_h0_eq_harmonic_finrank`.
   - `RiemannRoch.h0_canonical_eq_genus` now reduces to:
     1) `h0(K)` equals harmonic `(1,0)` finrank,
     2) harmonic `(1,0)` finrank equals genus.
12. Added Gate C (Dolbeault/sheaf) bridge infrastructure in
    `HodgeTheory/HodgeDecomposition/InnerProductAndDolbeault.lean`:
    - `harmonic01ToSheafH1O`
    - `harmonic01ToSheafH1O_eq_iff`
    - `harmonic01ToSheafH1O_surjective_of_hodgeDecomposition`
    - `harmonic01ToSheafH1O_surjective` (specialized via `hodge_decomposition_01`)
    - `harmonic01ToSheafH1O_injective_of_exact_kernel`
    - `harmonic01ToSheafH1O_injective_of_exact_harmonic01_vanishes`
    - `harmonic01ToSheafH1O_bijective_of_hodgeDecomposition_and_exact_kernel`
    - `harmonic01ToSheafH1OLinear`
    - `harmonic01ToSheafH1OLinear_bijective_of_exact_harmonic01_vanishes`
13. Added local mixed-Wirtinger and chart-stabilized exact-pair infrastructure:
    - `Infrastructure/WirtingerDerivatives.lean`:
      `laplacian_eq_four_wirtinger_mixed_at` (`ContDiffAt` form), plus existing global wrapper.
    - `HodgeTheory/HodgeDecomposition/Core.lean`:
      `dbar_10_del_real_add_del_01_dbar_real_hd_eq_zero_of_chartAtLocallyConstant`.
    - `HodgeTheory/HodgeDecomposition/ExactPair.lean`:
      `exactPair_commonPotential_of_closed_of_chartAtLocallyConstant_and_exact_harmonic01_vanishes`.
    - `HodgeTheory/HodgeDecomposition/DeRhamBridge.lean`:
      `harmonicPairToDeRham_surjective_of_hodgeDecomposition_and_chartAtLocallyConstant_and_exact_harmonic01_vanishes`,
      `harmonicPairToDeRham_bijective_of_hodgeDecomposition_and_chartAtLocallyConstant_and_exact_harmonic01_vanishes`,
      `hodge_isomorphism_of_chartAtLocallyConstant_and_exact_harmonic01_vanishes`.
    This closes the mixed-identity branch under chart-stabilization assumptions and
    isolates the remaining unconditional gap as selector-independent/globalization work.
14. Added selector-localization infrastructure for the `RiemannSphere` nonzero region:
    - `HodgeTheory/Infrastructure/ChartSelection.lean`:
      `chartAt_eventuallyEq_center_riemannSphere_coe_of_ne_zero`.
    - new module `HodgeTheory/HodgeDecomposition/MixedIdentity.lean`:
      `dbar_10_del_real_add_del_01_dbar_real_hd_toSection_eq_zero_of_chartAt_eventuallyEq`,
      `dbar_10_del_real_add_del_01_dbar_real_hd_toSection_eq_zero_riemannSphere_coe_of_ne_zero`.
    This refines the mixed-identity obstruction picture:
    away from selector-switch points (e.g. finite nonzero sphere points), the mixed identity
    is now compile-checked pointwise; unresolved behavior is localized to non-stabilized points
    (notably `0` for the current sphere selector).
    - `dolbeault_isomorphism_01_of_exact_kernel`
    - `dolbeault_isomorphism_01_linear_of_exact_harmonic01_vanishes`
    and refactored `dolbeault_isomorphism_01` to reduce to two explicit deep obligations:
    1) `(0,1)` Hodge decomposition existence,
    2) exact harmonic `(0,1)` kernel vanishing.
    Follow-up reduction: the decomposition obligation is now discharged via
    `hodge_decomposition_01`, so the remaining explicit deep blocker in
    `dolbeault_isomorphism_01` is exact harmonic `(0,1)` kernel vanishing.
13. Added linear transport of the Dolbeault/sheaf bridge in
    `HodgeTheory/DolbeaultCohomology.lean`:
    - `dolbeault_hodge_linear_bijective_of_exact_harmonic01_vanishes`
    via the linear sheaf-side bridge and `SheafH1O_eq_DolbeaultH01`.
    `h1_trivial_eq_genus` previously reduced to:
    1) exact-harmonic `(0,1)` vanishing,
    2) harmonic `(0,1)` finrank identity.
    The finrank piece is now discharged (`finrank_harmonic01_eq_genus`), so
    the remaining deep blocker on this branch is exact-harmonic vanishing.
14. Consolidated repeated exact-harmonic `(0,1)` blocker into one core theorem:
    - `HodgeTheory/HodgeDecomposition/Core.lean::exact_harmonic01_vanishes`
    - `DeRhamBridge.hodge_isomorphism`,
      `InnerProductAndDolbeault.dolbeault_isomorphism_01`, and
      `DolbeaultCohomology.h1_trivial_eq_genus` now reuse this shared theorem
      instead of carrying duplicate local `sorry` blocks.
15. Consolidated Gate C common-potential compatibility into one core theorem:
    - `HodgeTheory/HodgeDecomposition/Core.lean::closed_exactPair_commonPotential`
    - `DeRhamBridge.hodge_isomorphism` now delegates directly to
      core-level `closed_exactPair_commonPotential` + `exact_harmonic01_vanishes`
      via `hodge_isomorphism_of_commonPotential_and_exact_harmonic01_vanishes`.
16. Consolidated harmonic finrank identities into a dedicated decomposition module:
    - `HodgeTheory/HodgeDecomposition/DimensionGenus.lean::finrank_harmonic01_eq_genus`
    - `HodgeTheory/HodgeDecomposition/DimensionGenus.lean::finrank_harmonic10_eq_genus`
    - `DolbeaultCohomology.h1_trivial_eq_genus` and the harmonic-finrank branch of
      `RiemannRoch.h0_canonical_eq_genus` now consume these shared theorems.
17. Added conjugation/Wirtinger bridge infrastructure in
    `HodgeTheory/Infrastructure/WirtingerDerivatives.lean`:
    - `wirtingerDerivBar_comp_conj_real` (`∂̄(conj ∘ g)=conj(∂g)` for `ℝ`-differentiable `g`)
    - `wirtingerDeriv_comp_conj_real` (`∂(conj ∘ g)=conj(∂̄g)` for `ℝ`-differentiable `g`)
    - rewired `wirtingerDerivBar_comp_conj` and `wirtingerDeriv_comp_conj` through the new real-level lemmas.
18. Refactored downstream uses to consume the new real-level bridge directly:
    - `HodgeTheory/HodgeDecomposition/Core.lean::del_01_eq_zero_of_isHarmonic01`
      now avoids an intermediate holomorphicity reconstruction step.
    - `HodgeTheory/Dolbeault.lean::dbar_conj_eq_conj_d_chart`
      now uses chart differentiability + `wirtingerDerivBar_comp_conj_real`,
      replacing heavier `MDifferentiableAt` unpacking boilerplate.
19. Added new core conjugation compatibility and harmonicity criteria in
    `HodgeTheory/HodgeDecomposition/Core.lean`:
    - `dbar_10_conj` (`∂̄(ω̄) = -conj(∂ω)` for `(0,1)`-forms)
    - `del_01_conj` (`∂(η̄) = -conj(∂̄η)` for `(1,0)`-forms)
    - `isHarmonic01_of_del_01_eq_zero`
    - `isHarmonic01_iff_del_01_eq_zero`
    This upgrades `(0,1)` harmonicity from one-way implication to a usable iff
    with `∂`-closedness, and removes duplicated local conjugation algebra in
    downstream proofs.
20. Refactored de Rham/additive packaging out of `Core.lean` into
    `HodgeTheory/HodgeDecomposition/DeRhamCore.lean`:
    - moved `dbarRealAddHom_hd`, `dbarRealLinearMap_hd`,
      `exactForms1AddHom`, `exactForms1LinearMap`
    - moved `closedForms1`, `exactForms1`, `DeRhamH1`,
      `exactClosedForms1AddSubgroup`, and associated quotient criteria
    - rewired `ExactPair`, `DeRhamBridge`, `InnerProductAndDolbeault`,
      and `HodgeDecomposition.lean` imports
    - restored `< 2000` file-size policy for `Core.lean`
      (`scripts/check_lean_file_length.sh 2000`: pass).
21. Added fixed-chart transition cocycle infrastructure to support selector-independent
    overlap gluing on the Gate A path:
    - `Helpers/ChartTransition.lean`:
      `chartTransition_comp_eventuallyEq`, `chartTransition_deriv_comp`.
    - `HodgeTheory/Infrastructure/TransitionFactor.lean`:
      `chartTransitionDerivInCharts_cocycle`,
      `chartTransitionFactorInCharts_cocycle`,
      `chartTransitionFactorByCharts_cocycle`.
    These package triple-overlap composition/derivative/Jacobian identities
    in reusable theorem form for downstream `dbar_real_hd` smoothness assembly.
22. Added fixed-chart normalization/inverse infrastructure and wrapper layer:
    - `TransitionFactor.lean`:
      `chartTransitionFactorInCharts_self`,
      `chartTransitionFactorByCharts_self`,
      `chartTransitionFactorByCharts_mul_reverse_eq_one`,
      `chartTransitionFactorByCharts_eq_inv_reverse`.
    - `HodgeTheory/HodgeDecomposition/TransitionFactorGlue.lean`:
      `dbarRealTransitionFactorByCharts_cocycle_hd`,
      `dbarRealTransitionFactorByCharts_self_hd`,
      `dbarRealTransitionFactorByCharts_mul_reverse_eq_one_hd`,
      `dbarRealTransitionFactorByCharts_eq_inv_reverse_hd`.
    - reciprocal regularity additions:
      `chartTransitionFactorByCharts_inv_continuousAt`,
      `chartTransitionFactorByCharts_inv_contMDiffAt`,
      `dbarRealTransitionFactorByCharts_inv_continuousAt_hd`,
      `dbarRealTransitionFactorByCharts_inv_contMDiffAt_hd`.
    This extends the fixed-chart transition API from cocycle-only to full
    overlap groupoid algebra (identity + inverse + composition), reducing
    ad hoc algebra in upcoming Gate A gluing proofs.
23. Added inverse-factor local `∂̄` overlap transport in
    `HodgeTheory/HodgeDecomposition/TransitionFactorGlue.lean`:
    - `dbarRealLocalCoeff_chartChange_fixedCharts_inv_hd`
    - `dbarRealLocalCoeff_eventuallyEq_fixedCharts_inv_hd`
    - `dbarRealLocalCoeff_rhs_inv_contMDiffAt_fixedCharts_hd`
    - `dbarRealLocalCoeff_transferred_contMDiffAt_fixedCharts_hd`
    - `dbarRealLocalCoeff_rhs_inv_contMDiffWithinAt_fixedCharts_hd`
    - `dbarRealLocalCoeff_transferred_contMDiffWithinAt_fixedCharts_hd`
    - `dbarRealLocalCoeff_transferred_contMDiffOn_overlap_fixedCharts_hd`
    - `dbarRealLocalCoeff_rhs_inv_contMDiffOn_overlap_fixedCharts_hd`
    This provides a second (inverse-factor) transport route complementary to the
    forward-factor identity, and gives a reusable smoothness entrypoint for the
    transferred chart-local coefficient expression.
24. Strengthened exact-pair algebra infrastructure in
    `HodgeTheory/HodgeDecomposition/ExactPair.lean`:
    - `del_real_sub_eq_zero_iff`
    - `dbar_real_hd_sub_eq_zero_iff`
    - `dbar_10_del_real_sub`
    - `del_01_dbar_real_hd_sub`
    - `exactPair_commonPotential_of_equal_derivatives`
    - `closed_exactPair_primitives_relation`
    - `closed_exactPair_primitives_relation_eq_neg`
    These normalize sub-zero/equality rewrites for potential-comparison arguments
    on the Gate C common-potential path.
10. Compile frontier checked:
   - `lake build StringGeometry.RiemannSurfaces.Analytic.Helpers.ChartTransition`
   - `lake build StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.Infrastructure.TransitionFactor`
   - `lake build StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.HodgeDecomposition`
   - `lake build StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.HodgeDecomposition.Core`
   - `lake build StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.HodgeDecomposition.DeRhamBridge`
   - `lake build StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.DolbeaultCohomology`
   - `lake build StringGeometry.RiemannSurfaces.Analytic.RiemannRoch`
   (pass, warning-only).

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
63. `HodgeTheory/HodgeDecomposition.lean`:
    extracted reusable local decomposition infrastructure for the `dbar` chart-varying
    section candidate:
    - `dbarRealFixedPart_hd`,
    - `dbarRealTransitionFactor_hd`,
    - `dbarRealSectionCandidate_eventuallyEq_fixed_mul_transition_hd`.
64. Refactor impact:
    `dbar_real_hd_smooth_section` now uses these helpers directly, so the remaining
    blocker is concentrated in the transition-factor smoothness closure rather than
    mixed with chart-change rewriting boilerplate.
65. Compile frontier re-checked after this refactor:
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
