# SchemeTheoretic TODO

## Scope
- Keep this branch purely algebraic (no analytic imports).
- No axiom smuggling, no fake witness structures, no weakened statements.

## Current Focus
- Stabilize core sheaf/cohomology infrastructure so `SGRSSchemeTheoretic` builds without new regressions.
- Close critical theorem obligations that feed Riemann-Roch.

## Current Status
- `Divisors.lean` core degree/principal-divisor algebra lemmas are now closed (`degree_zero/add/neg`, `PrincipalDivisor.mul/inv`, `linearlyEquivalent_refl`, `principalDivisor_degree_zero`).
- `Helpers/ConstantValuation.lean` API-compatibility with current Mathlib has been repaired; the stalk-factorization lemma for constants is now proved.
- Remaining high-impact blockers are still in sheaf/cohomology infrastructure and point-exact morphism construction.

## Key Dependency Flowchart
```text
Basic hierarchy + local ring infrastructure
  Basic.lean
  Helpers/{NoetherianStalks,StalkDVR,ValuationExtension,ConstantValuation}.lean
  LocalRings.lean
        |
        v
Divisor and line-bundle layer
  Divisors.lean
  Sheaves/{Coherent,LineBundles,Skyscraper}.lean
  Helpers/PointExactMorphisms.lean
        |
        v
Cech/cohomology layer
  Cohomology/CechComplex.lean
  Helpers/{CohomologyModuleStructure,CohomologyFunctoriality,FlasqueSheaves}.lean
  Cohomology/SheafCohomology.lean
        |
        v
Riemann-Roch inputs
  h0_structure_sheaf_eq_one
  h0_skyscraper_eq_one
  h1_skyscraper_eq_zero
  cohomology_long_exact_sequence / euler_char_additive
        |
        v
RiemannRoch.lean (riemann_roch_euler)
```

## Priority TODOs
1. Make `Helpers/CohomologyModuleStructure.lean` and `Helpers/FlasqueSheaves.lean` API-stable against current Mathlib signatures.
2. Finish `Cohomology/SheafCohomology.lean` bridge lemmas for `H^0 <-> global sections`.
3. Finish skyscraper cohomology compatibility proofs used by `Sheaves/Skyscraper.lean`.
4. Close point-exact sequence morphism proofs used by Euler-characteristic induction.
5. Keep a running list of theorem blockers directly above `RiemannRoch.lean`.

## Done Criteria
- `lake build SGRSSchemeTheoretic` succeeds.
- No new placeholders introduced by ongoing changes.
- Riemann-Roch dependency chain is explicitly documented and up to date in this file.
