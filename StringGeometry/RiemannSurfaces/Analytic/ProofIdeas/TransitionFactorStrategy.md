# Transition-Factor Proof Strategy

## Objective
- Close the `dbar_real_hd` smoothness chain in `HodgeDecomposition.lean` without wrappers/smuggling.
- Keep theorem statements mathematically honest under the current explicit `chartAt` selector.
- Scope clarification:
  all obstructions in this note concern selector-dependent formulas; they do **not**
  claim any failure of manifold smoothness of `RiemannSphere`.

Primary blocker declaration:
- `dbarRealTransitionFactor_contMDiffAt_hd` in
  `Analytic/HodgeTheory/HodgeDecomposition.lean`.

## What Is Already Proved

Core reusable infrastructure:
- `Analytic/HodgeTheory/Infrastructure/TransitionFactor.lean`
  - `chartTransitionFactor`
  - `chartTransitionFactor_eq_one_of_chartEq`
  - `chartTransitionFactor_center`
  - `chartTransitionFactor_ne_zero_of_mem_source`
  - `chartTransitionFactor_eventually_ne_zero`
  - `chartTransitionFactor_contMDiffAt_of_eventuallyEq_chart`
  - `chartTransitionFactor_contMDiffAt_of_chartAtLocallyConstant`

Model diagnostics on `RiemannSphere` (center `0`):
- `chartTransitionFactor_riemannSphere_zero_nonzero`
  - explicit formula at nonzero finite points: `-conj(z)^2`.
- `not_continuousAt_chartTransitionFactor_riemannSphere_zero`.
- `not_contMDiffAt_chartTransitionFactor_riemannSphere_zero`.

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
