# dbar_real_hd Smoothness Plan

## Blocker

Target declaration:
- `HodgeTheory/HodgeDecomposition.lean`
- `dbar_real_hd_smooth_section`

Current issue:
- the section is defined pointwise using `chartAt` at the same point.
- this creates a chart-varying expression with difficult global `ContMDiff` obligations.
- structural friction in current encoding:
  - `(1,0)` / `(0,1)` forms are represented as raw coefficient functions
    `RS.carrier → ℂ` rather than chart-free cotangent-bundle sections.
  - because `chartAt` is a choice function, moving-chart coefficient expressions
    are hard to control directly with local smoothness lemmas.

Resolved recently:
- smoothness-index normalization now uses project alias
  `smoothOrder : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)`.
- `RealSmoothFunction`, `Form_10`, and `Form_01` now consistently use `smoothOrder`.
- chart differentiability bridge now has reusable nonzero/smoothOrder specializations:
  - `differentiableAt_chart_comp_of_ne_zero`
  - `differentiableAt_chart_comp_smoothOrder`

## Infrastructure-first route

1. Add a fixed-chart local operator. (partially complete)
- Define a local coefficient function on `((chartAt ℂ p0).source)` using one fixed chart `e := chartAt ℂ p0`.
- Work with `ContMDiffOn`/`ContDiffOn` first (not global `ContMDiff`).
  - done infrastructure:
    - `RealSmoothFunction.contDiffOn_comp_chart_symm`
    - `RealSmoothFunction.differentiableAt_comp_chart_symm`
    - `realSmooth_comp_chart_symm_contDiffOn_hd` now delegates to the infrastructure theorem.

2. Prove fixed-chart regularity. (mostly complete)
- Bridge `RealSmoothFunction.smooth'` to chart coordinates with existing lemmas.
- Prove local `ContDiffOn` for `wirtingerDerivBar` of the chart expression.
- Export a reusable lemma: fixed-chart `∂̄` coefficient is smooth on chart source.
  - done infrastructure:
    - `wirtingerDerivBar_chart_comp_contDiffOn_hd`
    - `wirtingerDerivBar_chart_comp_contDiffAt_hd`
    - `dbar_real_local_fixedChart_contMDiffOn_hd`
    - `dbar_real_local_fixedChart_contMDiffAt_hd`

3. Prove chart-transition compatibility for local definitions. (partially complete)
- On overlaps of two charts, prove equality between local `∂̄` coefficient descriptions via transition maps.
- Keep this lemma explicit and reusable; avoid implicit wrapper assumptions.
  - done infrastructure:
    - `comp_extChart_symm_eventuallyEq_chartTransition`
    - `wirtingerDerivBar_extChart_symm_change`
    - `wirtingerDerivBar_extChart_symm_change_of_realSmooth`
    - `wirtingerDeriv_extChart_symm_change_of_realSmooth`
    - `wirtingerDerivBar_extChart_symm_change_at_point_of_realSmooth`
    - `dbarRealSectionCandidate_chartChange_hd`
  - remaining gap:
    - promote overlap compatibility to a chart-local `ContMDiffWithinAt`/`ContDiffWithinAt`
      transport lemma directly usable by `contMDiff_iff` local-to-global assembly.
    - control regularity in the moving-point factor
      `p ↦ starRingEnd ℂ (deriv (chartTransition p0 p) ((chartAt ℂ p) p))`.
    - now partially bridged:
      under eventual chart stabilization
      `chartAt p = chartAt p0` near `p0`, this factor is eventually `1` and smooth.

4. Lift local regularity to global section smoothness.
- Use manifold-local-to-global `ContMDiff` criteria:
  `contMDiff_iff` / chart-local reformulations.
- Conclude `dbar_real_hd_smooth_section` from local fixed-chart smoothness + overlap compatibility.
  - active blocker is now solely transition-factor regularity under moving chart choice.

## Immediate next bridge lemmas

1. `dbar_real_local_overlap_contDiffWithinAt`:
   overlap-transport lemma in the exact `ContDiffWithinAt` shape expected by
   `contMDiffWithinAt_iff_of_mem_source`.
2. `chartAt` stabilization bridge (missing):
   prove or encode a usable local eventual-equality statement for chart choice near `p0`,
   then feed it into the now-available conditional smoothness lemma
   `dbarRealTransitionFactor_contMDiffAt_of_eventuallyEq_chart_hd`.
   Current named blocker theorem:
   `chartAt_eventuallyEq_center_hd`.

## Attempted route (tangent-bundle infrastructure)

Tried:
- rewrite transition Jacobian factor via tangent-bundle core / chart derivatives:
  - `TangentBundle.continuousLinearMapAt_trivializationAt_eq_core`
  - `TangentBundle.continuousLinearMapAt_trivializationAt`
  - `tangentBundleCore_coordChange_achart`
  - derivative-to-scalar projection by evaluation at `1`.

Outcome:
- gives good structural identities, but does not remove the root obstruction:
  the moving index `achart H p` (equivalently `chartAt p`) remains selection-dependent.
- smoothness APIs in `VectorBundle` / `ContMDiffMFDeriv` control fixed-chart/fixed-index
  coordinate changes, not arbitrary point-dependent chart choices.

Conclusion:
- without an additional chart-selection regularity axiom, the clean path remains:
  either prove `chartAt_eventuallyEq_center_hd` in this specific setting,
  or refactor the formalization to chart-free bundle sections where smoothness is
  invariant under chart choice.
3. `dbar_real_chart_local_contMDiffAt`:
   chart-local `ContMDiffAt` statement for the section candidate at an arbitrary point.
4. `dbar_real_hd_smooth_section` via local-to-global assembly.
5. eliminate dependence on the ad hoc moving chart expression by replacing
   `p ↦ chartAt ℂ p` in the coefficient definition with a chart-localized
   formulation that glues via overlap equalities.
6. medium-term refactor target:
   migrate form representation toward chart-free section data (or an equivalent
   bundle-level interface), so smoothness proofs are invariant under chart
   choice and no longer depend on regularity of the selected `chartAt`.

## Constraints

- No theorem weakening and no assumption-smuggling wrappers.
- Keep theorem-level `sorry` only at genuine global endpoints if needed.
- Prefer reusable infrastructure lemmas over one-off proof scripts.
