import StringGeometry.RiemannSurfaces.Core.DivisorModel
import StringGeometry.RiemannSurfaces.GAGA.AlgebraicCurves.Divisors

namespace RiemannSurfaces.Core

open RiemannSurfaces

/-- Adapter exposing algebraic (RS-level) divisors through the shared core interface. -/
noncomputable instance algebraicDivisorModel (RS : RiemannSurface) :
    DivisorModel RS.carrier (RiemannSurfaces.Algebraic.Divisor RS) where
  coeff := fun D p => D.coeff p
  finiteSupport := fun D => D.finiteSupport
  degree := RiemannSurfaces.Algebraic.Divisor.degree
  point := RiemannSurfaces.Algebraic.Divisor.point
  coeff_zero := by
    intro p
    rfl
  coeff_add := by
    intro D₁ D₂ p
    rfl
  coeff_neg := by
    intro D p
    rfl
  degree_zero := RiemannSurfaces.Algebraic.Divisor.degree_zero
  degree_add := RiemannSurfaces.Algebraic.Divisor.degree_add
  degree_neg := RiemannSurfaces.Algebraic.Divisor.degree_neg
  degree_point := RiemannSurfaces.Algebraic.Divisor.degree_point

end RiemannSurfaces.Core
