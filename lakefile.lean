import Lake
open Lake DSL

package "stringgeometry-riemann-surfaces" where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"


lean_lib SGRSCore where
  roots := #[`StringGeometry.RiemannSurfaces.Core]

lean_lib SGRSTopologySheaves where
  roots := #[
    `StringGeometry.Topology.Sheaves.CechCohomology,
    `StringGeometry.Topology.Sheaves.LongExactSequence
  ]

lean_lib SGRSAnalytic where
  roots := #[`StringGeometry.RiemannSurfaces.Analytic.Analytic]

lean_lib SGRSSchemeTheoretic where
  roots := #[`StringGeometry.RiemannSurfaces.SchemeTheoretic]

lean_lib SGRSGAGA where
  roots := #[`StringGeometry.RiemannSurfaces.GAGA.Basic]

lean_lib SGRSCombinatorial where
  roots := #[`StringGeometry.RiemannSurfaces.Combinatorial.Combinatorial]

lean_lib SGRiemannSurfaces where
  roots := #[`StringGeometry.RiemannSurfaces]
