# stringgeometry-riemann-surfaces

Lean formalization of Riemann surface theory with two primary engines and a
GAGA bridge:

- `Analytic` (complex-analytic and Hodge-theoretic development)
- `SchemeTheoretic` (algebraic-geometry development on curves)
- `GAGA` (bridge layer between analytic and algebraic viewpoints)

This repository is the source-of-truth for Riemann surfaces in the split
`StringGeometry` architecture.

## Build

```bash
lake update
lake build
```

## Architecture

### Design principles

- Keep `Analytic` and `SchemeTheoretic` as independent proof engines.
- Keep `GAGA` as a bridge layer, not as a foundational source for either engine.
- Put shared interfaces only in `Core`.
- Avoid circularity and theorem-smuggling across tracks.

### Layer map

1. `Core`:
   shared interfaces and transports (`DivisorModel`, principal divisor model,
   analytic/algebraic adapters).
2. `Analytic`:
   complex-analytic engine, Hodge/Dolbeault/Serre-duality side, analytic
   Riemann-Roch line.
3. `SchemeTheoretic`:
   algebraic-geometric engine on curves, coherent/sheaf/cohomology and
   scheme-theoretic Riemann-Roch line.
4. `Topology.Sheaves`:
   reusable Cech + long exact sequence infrastructure used by bridge theorems.
5. `GAGA`:
   explicit bridge theorems and transport lemmas joining analytic and algebraic
   viewpoints without collapsing boundaries.
6. `Combinatorial`:
   ribbon graph/moduli-oriented combinatorial infrastructure.

### Core interface layer

- `StringGeometry/RiemannSurfaces/Core/DivisorModel.lean`
- `StringGeometry/RiemannSurfaces/Core/AnalyticDivisor.lean`
- `StringGeometry/RiemannSurfaces/Core/AlgebraicDivisor.lean`
- `StringGeometry/RiemannSurfaces/Core/SchemeDivisor.lean`
- `StringGeometry/RiemannSurfaces/Core/AnalyticAlgebraicBridge.lean`
- `StringGeometry/RiemannSurfaces/Core/PrincipalDivisorModel.lean`

This layer provides:

- a model-independent `DivisorModel` contract
- executable adapters for existing divisor implementations
- explicit transport data (`DivisorTransport`) for GAGA-facing interoperability

### Bridge wiring

The GAGA bridge now imports and uses the core divisor transport contract via:

- `StringGeometry/RiemannSurfaces/GAGA/Bridge/DivisorCoreBridge.lean`

### Repository map

- `StringGeometry/RiemannSurfaces/Analytic/`
  - analytic geometry, Hodge theory, Jacobian/theta, analytic RR infrastructure.
- `StringGeometry/RiemannSurfaces/SchemeTheoretic/`
  - algebraic curves, coherent sheaves, cohomology helpers, scheme RR line.
- `StringGeometry/RiemannSurfaces/GAGA/`
  - bridge layer: algebraic-curve side, cohomology bridges, point exact sequence,
    Euler characteristic transport, RR bridge theorems.
- `StringGeometry/RiemannSurfaces/Core/`
  - shared interfaces and adapters.
- `StringGeometry/RiemannSurfaces/Combinatorial/`
  - ribbon graph/combinatorial moduli structures.
- `StringGeometry/Topology/Sheaves/`
  - Cech cohomology and long exact sequence primitives reused by GAGA.

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

## Integrity Guard

- Run `./scripts/check_rr_independence.sh` to enforce Riemann-Roch track independence and anti-smuggling checks.

This guard checks, among other invariants:

1. no forbidden cross-imports between analytic and scheme-theoretic engines
2. explicit theorem interfaces for point-exact/Cech/Serre/RR bridges
3. anti-smuggling constraints on bundled theorem-data structures

## CI

GitHub Actions workflow:

- `.github/workflows/lean-ci.yml`

Current triggers are intentionally limited to:

- `pull_request`
- `workflow_dispatch`

The workflow runs the independence guard before `lake build`.
