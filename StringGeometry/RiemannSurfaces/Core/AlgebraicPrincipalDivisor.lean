import StringGeometry.RiemannSurfaces.Core.PrincipalDivisorModel
import StringGeometry.RiemannSurfaces.Core.AlgebraicDivisor
import StringGeometry.RiemannSurfaces.GAGA.AlgebraicCurves.Divisors

namespace RiemannSurfaces.Core

open RiemannSurfaces

/-- Adapter exposing algebraic principal divisors and linear equivalence through
`PrincipalDivisorModel`. -/
noncomputable instance algebraicPrincipalDivisorModel
    (RS : RiemannSurface) (A : RiemannSurfaces.Algebraic.AlgebraicStructureOn RS) :
    PrincipalDivisorModel RS.carrier (RiemannSurfaces.Algebraic.Divisor RS) where
  IsPrincipal := RiemannSurfaces.Algebraic.IsPrincipal A
  zero_isPrincipal := RiemannSurfaces.Algebraic.zero_isPrincipal A
  add_isPrincipal := by
    intro D₁ D₂ h₁ h₂
    exact RiemannSurfaces.Algebraic.add_isPrincipal A h₁ h₂
  neg_isPrincipal := by
    intro D hD
    exact RiemannSurfaces.Algebraic.neg_isPrincipal A hD

end RiemannSurfaces.Core
