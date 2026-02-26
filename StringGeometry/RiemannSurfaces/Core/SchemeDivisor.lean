import StringGeometry.RiemannSurfaces.Core.DivisorModel
import StringGeometry.RiemannSurfaces.SchemeTheoretic.Divisors

namespace RiemannSurfaces.Core

/-- Adapter exposing scheme-theoretic divisors through the shared core interface. -/
noncomputable instance schemeDivisorModel (C : RiemannSurfaces.SchemeTheoretic.AlgebraicCurve) :
    DivisorModel C.PointType (RiemannSurfaces.SchemeTheoretic.Divisor C) where
  coeff := fun D p => D p
  finiteSupport := by
    intro D
    classical
    have hs : { p : C.PointType | D p ≠ 0 } = (D.support : Set C.PointType) := by
      ext p
      simp [Finsupp.mem_support_iff]
    simpa [hs] using D.support.finite_toSet
  degree := RiemannSurfaces.SchemeTheoretic.Divisor.degree
  point := RiemannSurfaces.SchemeTheoretic.Divisor.point
  coeff_zero := by
    intro p
    simp
  coeff_add := by
    intro D₁ D₂ p
    simp
  coeff_neg := by
    intro D p
    simp
  degree_zero := RiemannSurfaces.SchemeTheoretic.Divisor.degree_zero
  degree_add := RiemannSurfaces.SchemeTheoretic.Divisor.degree_add
  degree_neg := RiemannSurfaces.SchemeTheoretic.Divisor.degree_neg
  degree_point := RiemannSurfaces.SchemeTheoretic.Divisor.degree_point

end RiemannSurfaces.Core
