# GAGA TODO

## Scope
- Keep GAGA as the transport/equivalence layer between analytic and algebraic viewpoints.
- Avoid reintroducing theorem-bearing data structures as hidden assumptions.

## Key Dependency Flowchart
```text
Bridge layer
  Bridge/{DivisorCoreBridge,ToSmoothProjectiveCurve,EulerCharBridge,...}
  AlgebraicStructure.lean
        |
        v
Cech/cohomology transport
  Cohomology/{MathlibBridge,GeneralCechBridge,ExactSequence,PointExactProof}.lean
  Cohomology/CechTheory.lean
        |
        v
Euler-char recursion + RR statements
  CechTheory.point_recursion_cech(_of_data/_of_exists)
  CechTheory.eulerChar_formula_cech(_of)
  Cohomology/RiemannRoch.lean (riemann_roch_* family)
        |
        v
Top-level transfer
  GAGA/Basic.lean
  riemann_roch_gaga_transfer
```

## Priority TODOs
1. Keep the explicit-data RR pathway (`*_from_point_exact_data`) as the canonical proof route.
2. Ensure point-exact recursion and Euler-characteristic formulas remain theorem-driven (not bundled assumptions).
3. Keep bridge theorems thin and compositional so SchemeTheoretic/Analytic changes do not fork logic.
4. Maintain one-way architecture: GAGA consumes results; it does not own core model definitions.

## Done Criteria
- GAGA RR transfer theorems build with explicit dependency data.
- No hidden assumption bundles are introduced in bridge/cohomology layers.
- This TODO remains the single planning/status document in `GAGA/`.
