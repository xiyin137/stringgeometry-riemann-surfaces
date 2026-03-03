# Transition-Factor Proof Strategy

## Objective
- Close the `dbar_real_hd` smoothness chain in `HodgeDecomposition.lean` without wrappers/smuggling.
- Keep theorem statements mathematically honest under the current explicit `chartAt` selector.
- Scope clarification:
  all obstructions in this note concern selector-dependent formulas; they do **not**
  claim any failure of manifold smoothness of `RiemannSphere`.

## Canonicality Clarification
- `chartTransition (q r)` in current infrastructure means
  `(extChartAt q) ∘ (extChartAt r).symm` for the currently selected charts.
- This is a useful local computational interface, but it is not a canonical
  transition map determined only by the center points `q, r`.
- Therefore `chartTransitionFactor (p0, p)` is selector-dependent data.
- Non-continuity/non-smoothness results for this object are diagnostics about that
  selector-dependent encoding, not about smoothness of the underlying manifold.
- Universal theorem targets should be phrased in chart-indexed overlap form (or
  chart-free bundle form), then proved chart-invariant.

Primary blocker declaration:
- `dbarRealTransitionFactor_contMDiffAt_hd` in
  `Analytic/HodgeTheory/HodgeDecomposition.lean`.

## What Is Already Proved

Core reusable infrastructure:
- `Analytic/HodgeTheory/Infrastructure/TransitionFactor.lean`
  - `chartTransitionFactor`
  - `chartTransitionDerivInCharts`
  - `chartTransitionFactorInCharts`
  - `chartTransitionFactorByCharts`
  - `chartTransitionByCharts_contMDiffAt`
  - `chartTransitionFactor_eq_one_of_chartEq`
  - `chartTransitionFactor_center`
  - `chartTransitionFactor_ne_zero_of_mem_source`
  - `chartTransitionFactor_eventually_ne_zero`
  - `chartTransitionFactor_contMDiffAt_of_eventuallyEq_chart`
  - `chartTransitionFactor_contMDiffAt_of_chartAtLocallyConstant`
  - chart-transition composition/cocycle primitives:
    - `chartTransition_comp_eventuallyEq`
    - `chartTransition_deriv_comp`
    - `chartTransitionDerivInCharts_cocycle`
    - `chartTransitionFactorInCharts_cocycle`
    - `chartTransitionFactorByCharts_cocycle`
    - `chartTransitionFactorInCharts_self`
    - `chartTransitionFactorByCharts_self`
    - `chartTransitionFactorByCharts_mul_reverse_eq_one`
    - `chartTransitionFactorByCharts_eq_inv_reverse`
    - `chartTransitionFactorByCharts_inv_continuousAt`
    - `chartTransitionFactorByCharts_inv_contMDiffAt`
  - chart-indexed regularity:
    - `chartTransitionDerivInCharts_contDiffAt` (fixed-chart transition derivative is `C^∞` over `ℂ` on overlap)
    - `chartTransitionDerivInCharts_contDiffAt_real` (same derivative is `C^∞` over `ℝ` by scalar restriction)
    - `chartTransitionFactorInCharts_continuousAt` (fixed-chart starred factor is continuous on overlap)
    - `chartTransitionFactorInCharts_contDiffAt_real` (fixed-chart starred factor is `C^∞` over `ℝ`)
    - `chartTransitionByCharts_contMDiffAt` (surface-level fixed-chart transition map is `ContMDiffAt` on overlap)
    - `chartTransitionFactorByCharts_contMDiffAt` (surface pullback is `ContMDiffAt` on overlaps at `smoothOrder`)
    - `chartTransitionFactorInCharts_ne_zero` / `chartTransitionFactorByCharts_ne_zero`
      (nonvanishing on overlap, usable for inverse-factor infrastructure)
    - `chartTransitionFactorByCharts_eventually_ne_zero`
      (neighborhood-level nonvanishing near overlap points)

Model diagnostics on `RiemannSphere` (center `0`):
- `chartTransitionFactor_riemannSphere_zero_nonzero`
  - explicit formula at nonzero finite points: `-conj(z)^2`.
- `not_continuousAt_chartTransitionFactor_riemannSphere_zero`.
- `not_contMDiffAt_chartTransitionFactor_riemannSphere_zero`.
- `dbarRealTransitionFactor_not_forall_contMDiffAt_riemannSphere_hd`
  (globalized non-uniform-smoothness diagnostic for the moving-selector factor).

## Mathematical Consequence
- Under the current explicit sphere chart selector, the centered transition factor is not even continuous at `0`.
- Therefore a universal unconditional theorem asserting smoothness of this selector-dependent factor is not a viable closure path.

## Strategy Going Forward

### A) Keep assumption-explicit closure path (already available)
- Use:
  - `dbar_real_hd_smooth_section_of_chartAt_eventuallyEq`
  - `dbar_real_hd_smooth_section_of_chartAtLocallyConstant`
- Use this path on models where local chart stabilization is true (e.g. `ComplexPlane`).

### B) Replace selector-dependent target for the universal theorem
- The universal theorem should not depend on regularity of `p ↦ chartAt p`.
- Move to chart-invariant packaging:
  - chart-local fixed representations,
  - overlap identities as gluing data,
  - then local-to-global smoothness on a selector-independent object.

### C) Keep `TransitionFactor` module as diagnostic/bridge layer
- Keep explicit formulas and non-smoothness diagnostics in infrastructure.
- Reuse this module to prevent reintroducing hidden selector assumptions.

## Concrete Next Steps
1. Refactor the unconditional `dbar_real_hd_smooth_section` target to avoid direct dependence on moving `chartAt` selection.
2. Keep current assumption-explicit theorems as the executable closure route during refactor.
3. Add a short theorem-level note in `HodgeDecomposition.lean` near the blocker that references the proven sphere obstruction.
4. Continue building chart-free local-to-global infrastructure lemmas in reusable modules, then port back into Hodge and RR chain.

## Build Frontier
- `lake build StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.HodgeDecomposition`
- `lake build StringGeometry.RiemannSurfaces.Analytic.RiemannRoch`
