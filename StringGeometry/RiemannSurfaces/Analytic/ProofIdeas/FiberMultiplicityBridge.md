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

1. Add a local lemma schema (name TBD):
   `regular_point_value_matches_correctedValue`.
2. Add a bridge lemma schema:
   `regular_value_eq_c_iff_shift_order_pos`.
3. Finish the chartOrderSum/fiber equality lemma and use
   `fiberMultiplicity_constant_of_chartOrderSum_bridge`.
