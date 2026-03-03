# dbar_real_hd Smoothness Plan

## Blocker

Target declaration:
- `HodgeTheory/HodgeDecomposition.lean`
- `dbar_real_hd_smooth_section`

Current issue:
- the section is defined pointwise using `chartAt` at the same point.
- this creates a chart-varying expression with difficult global `ContMDiff` obligations.

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

4. Lift local regularity to global section smoothness.
- Use manifold-local-to-global `ContMDiff` criteria:
  `contMDiff_iff` / chart-local reformulations.
- Conclude `dbar_real_hd_smooth_section` from local fixed-chart smoothness + overlap compatibility.

## Immediate next bridge lemmas

1. `dbar_real_local_overlap_contDiffWithinAt`:
   overlap-transport lemma in the exact `ContDiffWithinAt` shape expected by
   `contMDiffWithinAt_iff_of_mem_source`.
2. `chartTransition_self_derivFactor_contMDiffAt` (new bridge target):
   local regularity of
   `p ↦ starRingEnd ℂ (deriv (chartTransition p0 p) ((chartAt ℂ p) p))`
   near `p0`.
3. `dbar_real_chart_local_contMDiffAt`:
   chart-local `ContMDiffAt` statement for the section candidate at an arbitrary point.
4. `dbar_real_hd_smooth_section` via local-to-global assembly.

## Constraints

- No theorem weakening and no assumption-smuggling wrappers.
- Keep theorem-level `sorry` only at genuine global endpoints if needed.
- Prefer reusable infrastructure lemmas over one-off proof scripts.
