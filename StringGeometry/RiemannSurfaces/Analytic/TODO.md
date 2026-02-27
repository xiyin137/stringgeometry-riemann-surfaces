# Analytic TODO

## Scope
- Build analytic Riemann-Roch independently of SchemeTheoretic and GAGA internals.
- Allowed dependencies: `Mathlib.*` and analytic/topology infrastructure only.

## Key Dependency Flowchart
```text
Differential/analytic foundations
  HodgeTheory/Infrastructure/{RealSmoothness,WirtingerDerivatives,...}
  HodgeTheory/DifferentialForms.lean
        |
        v
Dolbeault + Hodge bridge
  HodgeTheory/Dolbeault.lean
  HodgeTheory/DolbeaultCohomology.lean
  HodgeTheory/HodgeDecomposition.lean
        |
        v
Serre duality + argument principle
  HodgeTheory/SerreDuality.lean
  Helpers/ArgumentPrinciple.lean
        |
        v
Analytic/RiemannRoch.lean
  riemann_roch_h0_duality
  riemann_roch_classical
```

## Priority TODOs
1. Close remaining Riemann-Roch-chain obligations first (`RiemannRoch`, `SerreDuality`, `HodgeDecomposition`, `DolbeaultCohomology`, `Dolbeault`, `ArgumentPrinciple`).
2. Keep non-RR-chain modules (`Jacobian`, `Moduli`, `Applications`) lower priority until RR chain is sorry-free.
3. Maintain strict import independence from `SchemeTheoretic/*` and `GAGA/*`.

## Done Criteria
- `Analytic/RiemannRoch.lean` RR chain has no remaining proof gaps.
- Dependency chain above is build-clean and documented.
