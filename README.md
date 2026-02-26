# stringgeometry-riemann-surfaces

Lean formalization of Riemann surfaces with three complementary tracks:

- `Analytic` (complex-analytic and Hodge-theoretic development)
- `SchemeTheoretic` (algebraic-geometry development on curves)
- `GAGA` (bridge layer between analytic and algebraic viewpoints)

## Build

```bash
lake update
lake build
```

## Architecture

### Core interface layer

A new shared interface layer now lives in:

- `StringGeometry/RiemannSurfaces/Core/DivisorModel.lean`
- `StringGeometry/RiemannSurfaces/Core/AnalyticDivisor.lean`
- `StringGeometry/RiemannSurfaces/Core/AlgebraicDivisor.lean`
- `StringGeometry/RiemannSurfaces/Core/SchemeDivisor.lean`
- `StringGeometry/RiemannSurfaces/Core/AnalyticAlgebraicBridge.lean`

This layer provides:

- a model-independent `DivisorModel` contract
- executable adapters for existing divisor implementations
- explicit transport data (`DivisorTransport`) for GAGA-facing interoperability

### GAGA wiring

The GAGA bridge now imports and uses the core divisor transport contract via:

- `StringGeometry/RiemannSurfaces/GAGA/Bridge/DivisorCoreBridge.lean`

## Package targets

The package is split into multiple `lean_lib` targets in `lakefile.lean`:

- `SGRSCore`
- `SGRSTopologySheaves`
- `SGRSAnalytic`
- `SGRSSchemeTheoretic`
- `SGRSGAGA`
- `SGRSCombinatorial`
- `SGRiemannSurfaces` (umbrella import target)

This keeps one repository while enabling domain-specific CI and dependency boundaries.

## Design policy

- Keep `Analytic` and `SchemeTheoretic` as separate engines.
- Keep `GAGA` as a thin bridge layer.
- Add shared abstractions only in `Core`; avoid duplicating foundational definitions across engines.
