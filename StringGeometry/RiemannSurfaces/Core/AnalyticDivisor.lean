import StringGeometry.RiemannSurfaces.Core.DivisorModel
import StringGeometry.RiemannSurfaces.Analytic.Divisors

namespace RiemannSurfaces.Core

open RiemannSurfaces

/-- Adapter exposing analytic divisors through the shared core interface. -/
noncomputable instance analyticDivisorModel (RS : RiemannSurface) :
    DivisorModel RS.carrier (RiemannSurfaces.Analytic.Divisor RS) where
  coeff := fun D p => D.coeff p
  finiteSupport := fun D => D.finiteSupport
  degree := RiemannSurfaces.Analytic.Divisor.degree
  point := RiemannSurfaces.Analytic.Divisor.point
  coeff_zero := by
    intro p
    rfl
  coeff_add := by
    intro D₁ D₂ p
    rfl
  coeff_neg := by
    intro D p
    rfl
  degree_zero := RiemannSurfaces.Analytic.Divisor.degree_zero
  degree_add := RiemannSurfaces.Analytic.Divisor.degree_add
  degree_neg := RiemannSurfaces.Analytic.Divisor.degree_neg
  degree_point := RiemannSurfaces.Analytic.Divisor.degree_point

end RiemannSurfaces.Core
