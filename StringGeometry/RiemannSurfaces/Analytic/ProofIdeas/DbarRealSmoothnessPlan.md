# dbar_real_hd Smoothness Plan

## Blocker

Target declaration:
- `HodgeTheory/HodgeDecomposition.lean`
- `dbar_real_hd_smooth_section`

Current issue:
- the section is defined pointwise using `chartAt` at the same point.
- this creates a chart-varying expression with difficult global `ContMDiff` obligations.
- structural friction in current encoding:
  - `chartTransition (q r)` here is selector-based notation for
    `(extChartAt q) ∘ (extChartAt r).symm`; it is not a canonical map determined only
    by the center points.
  - `(1,0)` / `(0,1)` forms are represented as raw coefficient functions
    `RS.carrier → ℂ` rather than chart-free cotangent-bundle sections.
  - because `chartAt` is a choice function, moving-chart coefficient expressions
    are hard to control directly with local smoothness lemmas.

Resolved recently:
- local chart-selection infrastructure now exists in
  `HodgeTheory/Infrastructure/ChartSelection.lean`:
  - `chartAt_eventuallyEq_of_forall_eq`,
  - `chartAt_eventuallyEq_center_self`,
  - `chartAt_eventuallyEq_center_complexPlane`,
  - `ChartAtLocallyConstant` (project-level predicate for local chart stability).
  - `not_chartAtLocallyConstant_riemannSphere` (negative model result).
  This gives reusable building blocks for model-space / constant-chart situations.
  It also confirms the eventual-chart-stability route cannot be the global proof
  strategy for general surfaces represented like `RiemannSphere` under the current
  explicit `chartAt` selector (this is about selector behavior, not manifold smoothness).
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
    - reusable extraction completed:
      transition-factor definitions/bridges were moved into
      `HodgeTheory/Infrastructure/TransitionFactor.lean`, and the
      duplicated local scripts in `HodgeDecomposition.lean` were removed.
      this keeps the obstruction visible at a single declaration boundary.
    - chart-indexed infrastructure pass completed:
      - `chartTransitionDerivInCharts` and
        `chartTransitionDerivInCharts_contDiffAt` provide fixed-chart overlap
        `C^∞` regularity for the transition derivative over `ℂ`.
      - `chartTransitionDerivInCharts_contDiffAt_real` provides the same
        fixed-chart overlap regularity over `ℝ` (scalar-restricted).
      - chart-transition cocycle layer is now explicit:
        `chartTransition_comp_eventuallyEq`, `chartTransition_deriv_comp`,
        `chartTransitionDerivInCharts_cocycle`,
        `chartTransitionFactorInCharts_cocycle`,
        `chartTransitionFactorByCharts_cocycle`.
      - inverse/normalization layer is now explicit:
        `chartTransitionFactorInCharts_self`,
        `chartTransitionFactorByCharts_self`,
        `chartTransitionFactorByCharts_mul_reverse_eq_one`,
        `chartTransitionFactorByCharts_eq_inv_reverse`.
      - reciprocal regularity layer on overlaps:
        `chartTransitionFactorByCharts_inv_continuousAt`,
        `chartTransitionFactorByCharts_inv_contMDiffAt`.
      - local `∂̄` overlap transport now has inverse-factor forms in core:
        `dbarRealLocalCoeff_chartChange_fixedCharts_inv_hd`,
        `dbarRealLocalCoeff_eventuallyEq_fixedCharts_inv_hd`,
        `dbarRealLocalCoeff_rhs_inv_contMDiffAt_fixedCharts_hd`,
        `dbarRealLocalCoeff_transferred_contMDiffAt_fixedCharts_hd`.
      - overlap `WithinAt/On` smoothness packages for the inverse-factor branch
        (in `HodgeDecomposition/TransitionFactorGlue.lean`):
        `dbarRealLocalCoeff_rhs_inv_contMDiffWithinAt_fixedCharts_hd`,
        `dbarRealLocalCoeff_transferred_contMDiffWithinAt_fixedCharts_hd`,
        `dbarRealLocalCoeff_transferred_contMDiffOn_overlap_fixedCharts_hd`,
        `dbarRealLocalCoeff_rhs_inv_contMDiffOn_overlap_fixedCharts_hd`.
      - `chartTransitionFactorInCharts_continuousAt` provides fixed-chart overlap
        continuity for the starred factor (selector-free at the chart-pair level).
      - `chartTransitionFactorInCharts_contDiffAt_real` upgrades this to
        fixed-chart overlap `C^∞` regularity over `ℝ`.
      - surface pullback continuity now available:
        `chartTransitionFactorByCharts_continuousAt` and
        `chartTransitionFactorByCharts_continuousOn_overlap`.
      - surface pullback smoothness now available:
        `chartTransitionFactorByCharts_contMDiffAt` (`smoothOrder`, overlap points).
      - fixed-chart transition-map smoothness now available:
        `chartTransitionByCharts_contMDiffAt`.
      - neighborhood-level overlap nonvanishing now available:
        `chartTransitionFactorByCharts_eventually_ne_zero`.
      - `HodgeDecomposition.lean` now has
        `dbarRealLocalCoeff_chartChange_fixedCharts_hd` and
        `dbarRealLocalCoeff_eventuallyEq_fixedCharts_hd` plus
        `dbarRealLocalCoeff_rhs_contMDiffAt_fixedCharts_hd` /
        `dbarRealLocalCoeff_contMDiffAt_fixedCharts_hd` /
        `dbarRealLocalCoeff_contMDiffWithinAt_fixedCharts_hd` /
        `dbarRealLocalCoeff_contDiffWithinAt_chartOverlap_fixedCharts_hd` /
        `dbarRealTransitionFactorByCharts_contMDiffAt_hd` /
        `dbarRealTransitionFactorByCharts_continuousAt_hd` /
        `dbarRealTransitionFactorByCharts_ne_zero_hd` /
        `dbarRealTransitionFactorByCharts_eventually_ne_zero_hd` to consume this
        chart-indexed layer directly.
      - additive operator packaging completed for quotient interfaces:
        `dbarRealAddHom_hd`, `exactForms1AddHom`,
        `dbarImage_hd_toAddSubgroup_eq_range`,
        `exactForms1_toAddSubgroup_eq_range`.
      - linear operator packaging completed after adding
        `Module ℂ (RealSmoothFunction RS)` in `Infrastructure/RealSmoothness.lean`:
        `dbar_real_hd_smul`, `del_real_smul`,
        `dbarRealLinearMap_hd`, `exactForms1LinearMap`,
        `dbarImage_hd_eq_range_linearMap`, `exactForms1_eq_range_linearMap`.
      - canonical (non-local-copy) Dolbeault module now mirrors the same
        image-as-range package:
        `dbar_real_smul`, `dbarRealAddHom`, `dbarRealLinearMap`,
        `dbarImage_toAddSubgroup_eq_range`, `dbarImage_eq_range_linearMap`.
      - twisted Dolbeault image layer is now packaged identically:
        `dbar_twisted_smul`, `dbarTwistedAddHom`, `dbarTwistedLinearMap`,
        `twistedDbarImage_toAddSubgroup_eq_range`,
        `twistedDbarImage_eq_range_linearMap`.
      - added continuity bridge:
        `dbarRealSectionCandidate_continuousAt_of_transitionFactor_continuousAt_hd`
        (parallel to the smoothness bridge, useful for lower-regularity closure steps).
    - explicit model diagnostic added:
      `chartTransitionFactor_riemannSphere_zero_nonzero` now computes the factor
      at nonzero finite points (center `0`) as `-conj(z)^2`, giving a concrete
      local formula for analyzing the unconditional smoothness failure mode.
    - obstruction now formalized:
      `not_continuousAt_chartTransitionFactor_riemannSphere_zero` and
      `not_contMDiffAt_chartTransitionFactor_riemannSphere_zero` are proved in
      `TransitionFactor.lean` for the current explicit sphere selector.
    - cleanup completed:
      the intermediate theorem asserting local eventual equality of `chartAt` was removed.
      the remaining theorem-level blocker is now explicit and isolated at
      `dbarRealTransitionFactor_contMDiffAt_hd`.
    - added assumption-explicit closure route:
      `dbar_real_hd_smooth_section_of_chartAt_eventuallyEq`
      proves the full smoothness chain if one assumes local eventual stabilization of
      `chartAt` at every point.
    - closed model-surface slice:
      `dbar_real_hd_smooth_section_complexPlane` now proves the full smoothness
      theorem on `ComplexPlane` by supplying the chart-stability hypothesis from
      `complexPlane_chartAt_eventuallyEq_center_hd`.
    - refactor completed:
      extracted
      `dbarRealSectionCandidate_contMDiffAt_of_transitionFactor_contMDiffAt_hd`
      as the single local-to-global assembly lemma parameterized by transition-factor
      smoothness, and rewired both conditional and unconditional routes through it.
    - added predicate-level route:
      - `dbarRealTransitionFactor_contMDiffAt_of_chartAtLocallyConstant_hd`
      - `dbarRealSectionCandidate_contMDiffAt_of_chartAtLocallyConstant_hd`
      - `dbar_real_hd_smooth_section_of_chartAtLocallyConstant`
      so assumption-driven closure no longer repeats ad hoc `hchart p0` plumbing.

4. Lift local regularity to global section smoothness.
- Use manifold-local-to-global `ContMDiff` criteria:
  `contMDiff_iff` / chart-local reformulations.
- Conclude `dbar_real_hd_smooth_section` from local fixed-chart smoothness + overlap compatibility.
  - active blocker is now solely transition-factor regularity under moving chart choice.

## Immediate next bridge lemmas

1. `dbar_real_local_overlap_contDiffWithinAt`:
   overlap-transport lemma in the exact `ContDiffWithinAt` shape expected by
   `contMDiffWithinAt_iff_of_mem_source`.
   current status: chart-indexed predecessor now formalized as
   `dbarRealLocalCoeff_contMDiffWithinAt_fixedCharts_hd` plus
   coordinate-level `dbarRealLocalCoeff_contDiffWithinAt_chartOverlap_fixedCharts_hd`.
   Remaining step is to consume this in the
   moving-selector/global section assembly.
2. Transition-factor smoothness bridge (missing):
   prove
   `dbarRealTransitionFactor_contMDiffAt_hd`
   directly by chart-free/tangent-bundle infrastructure, or replace the coefficient
   model by a chart-invariant section interface.
   current fallback route (already formalized): provide a hypothesis
   `∀ p0, chartAt p =ᶠ[nhds p0] chartAt p0`.

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
  either prove smoothness of the moving transition Jacobian factor directly,
  or refactor the formalization to chart-free bundle sections where smoothness is
  invariant under chart choice.
- any proved non-smoothness of the selector-dependent transition-factor expression
  should be read as an encoding/selection obstruction, not as a claim that
  `RiemannSphere` (or any target manifold) is non-smooth.
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
