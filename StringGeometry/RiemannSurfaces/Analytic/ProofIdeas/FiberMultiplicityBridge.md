# Fiber Multiplicity Bridge Plan

## Goal

Close `Helpers/ArgumentPrinciple.lean: fiberMultiplicity_constant` by proving the missing bridge:

`fiberMultiplicity CRS f c hfib = chartOrderSum CRS (fun x => f x - c) ...`

or a corrected equivalent that still yields constancy.

## Current reduction already available

`fiberMultiplicity_constant_of_chartOrderSum_bridge` is now proved.

So the top blocker is fully isolated to the bridge lemma above.

## Why the bridge is nontrivial

`fiberMultiplicity` currently indexes points by **point value**:

`{ p | f p = c ∧ 0 ≤ ord_p(f) }`

while chart-order data is germ/punctured-neighborhood based. Without an extra compatibility lemma,
point value and germ value can diverge at isolated points.

## Candidate proof path A (keep current definition)

1. Prove a compatibility lemma at regular points:
   `f p = correctedValue(...)` under a local regularity hypothesis strong enough for RR chain usage.
2. Derive:
   `f p = c ∧ 0 ≤ ord_p(f)` iff `ord_p(f-c) > 0` on the regular locus.
3. Show pole contribution for `f-c` is independent of `c`.
4. Use `chartOrderSum_split` on `f-c` + `chartOrderSum_sub_const_eq_zero_of_nonconstant_regularLocus`.
5. Conclude bridge, then apply `fiberMultiplicity_constant_of_chartOrderSum_bridge`.

## Candidate proof path B (definition-level correction)

Introduce a corrected fiber notion using germ-compatible value (e.g. corrected value at non-poles),
prove constancy for that notion first, then provide a transfer lemma to current `fiberMultiplicity`
under explicit regularity assumptions.

## Next concrete Lean targets

1. Added:
   `correctedValue_eq_of_continuousAt` in `Helpers/AnalyticExtension.lean`.
2. Added:
   `eq_const_of_shift_pos_of_continuousAt` in `Helpers/ArgumentPrinciple.lean`.
3. Added:
   reverse/local-global continuity bridge chain in `Helpers/ArgumentPrinciple.lean`:
   - `shift_pos_of_eq_const_of_continuousAt`
   - `shift_pos_iff_eq_const_of_continuousAt`
   - `fiberSet_eq_zeroSet_sub_const_of_continuous_regular`
   - `fiberMultiplicity_eq_zeroSum_of_continuous_regular`
   - `totalPoleOrder_sub_const_eq_of_chartMeromorphic`
   - `fiberMultiplicity_eq_totalPoleOrder_sub_const_of_continuous_regular`
   - `fiberMultiplicity_constant_of_continuous_regular`
4. Added corrected-value shift algebra (toward removing continuity hypothesis):
   - `correctedValue_sub_const_eq`
   - `correctedValue_eq_const_of_sub_pos`
5. Remaining high-priority gap:
   upgrade from continuity-based variant to the original
   `fiberMultiplicity_constant` statement (currently no continuity/regularity assumption),
   or refactor statement/definition to a germ-compatible formulation.
