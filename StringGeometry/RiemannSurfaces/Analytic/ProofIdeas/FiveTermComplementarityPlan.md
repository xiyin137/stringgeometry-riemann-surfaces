# Five-Term Complementarity Plan

## Scope
This note documents the concrete closure plan for the analytic Riemann-Roch point-step blockers in
`StringGeometry/RiemannSurfaces/Analytic/RiemannRoch.lean`:

- `exists_evalResidueFiveTermMaps`
- `exists_evalResidueFinrankIdentifications`

The dimension algebra endpoint is already closed:

- `eval_residue_complementarity_of_fiveTermMaps`
- `eval_residue_complementarity_of_exists_fiveTermMaps_and_ids`

## Current decomposition
The deep point-step obligation is now split into:

1. Map-level exact package
   - construct vector spaces `V₁,V₂,V₄,V₅` and maps `f₁,f₂,f₃,f₄`
   - prove `inj_f₁`, `exact_V₂`, `exact_V₃`, `exact_V₄`, `surj_f₄`

2. Rank identification package
   - identify `finrank(V₁)=h0(D)`
   - identify `finrank(V₂)=h0(D+[p])`
   - identify `finrank(V₄)=h0(K-D)`
   - identify `finrank(V₅)=h0(K-D-[p])`

These are encoded as:

- `EvalResidueFiveTermMaps`
- `EvalResidueFinrankIdentifications`

## Concrete implementation route
### Step A: choose analytic models for V_i
Use already available analytic modules where possible:

- `V₁` as sections corresponding to `L(D)`
- `V₂` as sections corresponding to `L(D+[p])`
- `V₄,V₅` as dual/cohomological counterparts used in the residue pairing branch

Avoid introducing ad hoc wrappers. If a model is missing, add reusable infrastructure lemma(s) first.

### Step B: realize the five-term sequence
Construct maps as the standard point exact-sequence maps:

- inclusion map on sections (`f₁`)
- evaluation/principal-part map at `p` (`f₂`)
- connecting map (`f₃`)
- tail map (`f₄`)

Exactness goals should be proved as standalone helper lemmas before assembling the structure.

### Step C: rank bridge layer
For each `V_i`, connect the chosen model to existing `h0` definitions.

Because `h0` is currently defined via maximal linearly independent families
(not via a ready-made module finrank theorem), this likely needs explicit bridge lemmas.

### Step D: assemble final data
Use the now-available compositional infrastructure:

- `exists_evalResidueFiveTermData_of_exists_fiveTermMaps_and_ids`
- `eval_residue_complementarity_of_exists_fiveTermMaps_and_ids`

No additional dimension algebra is needed after this step.

## Required guardrails
- No placeholder definitions.
- No weakened theorem statements.
- Keep assumptions explicit at theorem boundaries.
- Prefer small reusable helper lemmas over one-off proof scripts.

## Fast verification loop
Run after each meaningful step:

- `lake build StringGeometry.RiemannSurfaces.Analytic.RiemannRoch`
- `lake build StringGeometry.RiemannSurfaces.Analytic.Helpers.EvaluationMap`

Then run broader analytic sweep before merge:

- `lake build StringGeometry.RiemannSurfaces.Analytic.Analytic`
