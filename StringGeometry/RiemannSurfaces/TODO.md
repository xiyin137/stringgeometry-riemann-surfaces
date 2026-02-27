# RiemannSurfaces TODO Index

This file is an index only. Planning is consolidated into exactly one TODO file per active engine:

- `StringGeometry/RiemannSurfaces/SchemeTheoretic/TODO.md`
- `StringGeometry/RiemannSurfaces/Analytic/TODO.md`
- `StringGeometry/RiemannSurfaces/GAGA/TODO.md`

## Current Build Checkpoint

- Verified on 2026-02-27:
  - `lake build SGRSSchemeTheoretic` succeeds (warnings only)
  - `lake build StringGeometry.RiemannSurfaces` succeeds (warnings only)

## Dependency Split (High Level)

```text
SchemeTheoretic  -> algebraic engine + sheaf/cohomology infrastructure
Analytic         -> analytic engine + Dolbeault/Hodge/Serre-duality chain
GAGA             -> transport/equivalence layer consuming the two engines
```

## Rules Reminder

- No axiom smuggling.
- No definition-body placeholders (`:= sorry`) in active modules.
- Keep theorem obligations explicit and tracked in the three TODO files above.
