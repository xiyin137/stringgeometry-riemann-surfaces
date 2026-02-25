import Lake
open Lake DSL

package "stringgeometry-riemann-surfaces" where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"


lean_lib SGRiemannSurfaces where
  roots := #[`StringGeometry.RiemannSurfaces]
