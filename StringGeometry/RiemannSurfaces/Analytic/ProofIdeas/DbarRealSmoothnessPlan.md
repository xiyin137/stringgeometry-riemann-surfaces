# dbar_real_hd Smoothness Plan

## Blocker

Target declaration:
- `HodgeTheory/HodgeDecomposition.lean`
- `dbar_real_hd_smooth_section`

Current issue:
- the section is defined pointwise using `chartAt` at the same point.
- this creates a chart-varying expression with difficult global `ContMDiff` obligations.

## Infrastructure-first route

1. Add a fixed-chart local operator.
- Define a local coefficient function on `((chartAt ℂ p0).source)` using one fixed chart `e := chartAt ℂ p0`.
- Work with `ContMDiffOn`/`ContDiffOn` first (not global `ContMDiff`).

2. Prove fixed-chart regularity.
- Bridge `RealSmoothFunction.smooth'` to chart coordinates with existing lemmas.
- Prove local `ContDiffOn` for `wirtingerDerivBar` of the chart expression.
- Export a reusable lemma: fixed-chart `∂̄` coefficient is smooth on chart source.

3. Prove chart-transition compatibility for local definitions.
- On overlaps of two charts, prove equality between local `∂̄` coefficient descriptions via transition maps.
- Keep this lemma explicit and reusable; avoid implicit wrapper assumptions.

4. Lift local regularity to global section smoothness.
- Use manifold-local-to-global `ContMDiff` criteria:
  `contMDiff_iff` / chart-local reformulations.
- Conclude `dbar_real_hd_smooth_section` from local fixed-chart smoothness + overlap compatibility.

## Immediate next bridge lemmas

1. `dbar_real_local_contDiffOn_chart` (fixed chart smoothness).
2. `dbar_real_local_overlap_compat` (transition compatibility).
3. `dbar_real_hd_smooth_section` via local-to-global assembly.

## Constraints

- No theorem weakening and no assumption-smuggling wrappers.
- Keep theorem-level `sorry` only at genuine global endpoints if needed.
- Prefer reusable infrastructure lemmas over one-off proof scripts.
