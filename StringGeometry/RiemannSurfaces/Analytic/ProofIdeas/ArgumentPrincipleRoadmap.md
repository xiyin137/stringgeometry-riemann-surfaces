# Argument Principle Roadmap

Target file:
- `StringGeometry/RiemannSurfaces/Analytic/Helpers/ArgumentPrinciple.lean`

## Goal

Close the local-to-global counting chain proving:

- `chartOrderSum_eq_zero_of_nonconstant`

without changing theorem statements or introducing placeholder infrastructure.

## Remaining declarations and strategy

1. `meromorphic_pole_local_sum_zero`
   - Use current skeleton: pole order extraction, inverse extension `H`, local mapping theorem.
   - Construct `S = {z₀} ∪ preimages(H = c⁻¹)` in a small ball.
   - Show:
     - `z₀` contributes `-n`,
     - each preimage contributes `+1`,
     - no other nonzero finite-order points occur.

2. `pole_local_chart_sum_constant`
   - Transfer `meromorphic_pole_local_sum_zero` from chart function `g` to manifold chart order.
   - Core step: `chartOrderAt_eq_in_chart` and eventual equality transfer.

3. `zero_local_chart_sum_constant`
   - For positive zero order at `q`, apply local mapping theorem directly to local analytic extension.
   - Separate cases:
     - `c = c₀` (single order-`k` contribution at center),
     - `c ≠ c₀` (exactly `k` simple preimages, each order 1).

4. `chartOrderSum_locally_constant`
   - Build finite disjoint neighborhood data around support at `c₀`.
   - Combine:
     - pole-local constancy,
     - zero-local constancy,
     - no-support on compact complement.

5. `chartOrderSum_zero_large_c`
   - Split surface into pole neighborhoods plus compact complement.
   - Use:
     - local pole cancellation from item (1)/(2),
     - large-`|c|` no-support on complement.
   - Sum contributions to get global zero.

## Micro-lemma checklist

1. Finite-set packaging around local mapping fibers.
2. Sum decomposition for `Finset.insert` with center point `z₀`.
3. Bridge lemmas:
   - `meromorphicOrderAt` in chart vs `chartOrderAt` on manifold,
   - eventual equality transport across chart transitions.
4. Simplicity lemma:
   - `deriv ≠ 0` at noncentral local preimages implies local order `= 1`.

## Suggested proof order

1. Finish `meromorphic_pole_local_sum_zero`.
2. Close `pole_local_chart_sum_constant`.
3. Close `zero_local_chart_sum_constant`.
4. Close `chartOrderSum_locally_constant`.
5. Close `chartOrderSum_zero_large_c`.

## Scratch workflow

1. Prototype brittle steps in a small scratch theorem near target section.
2. Confirm with targeted build:
   - `lake build StringGeometry.RiemannSurfaces.Analytic.Helpers.ArgumentPrinciple`
3. Move stabilized lemmas to reusable private theorems in same file.

