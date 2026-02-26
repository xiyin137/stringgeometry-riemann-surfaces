import StringGeometry.RiemannSurfaces.Core.DivisorModel
import StringGeometry.RiemannSurfaces.Core.AnalyticDivisor
import StringGeometry.RiemannSurfaces.Core.AlgebraicDivisor

namespace RiemannSurfaces.Core

open RiemannSurfaces

/-- Transport an analytic divisor into the algebraic RS-level divisor model by
reusing the same coefficient function and finite-support witness. -/
noncomputable def analyticToAlgebraicDivisor {RS : RiemannSurface}
    (D : RiemannSurfaces.Analytic.Divisor RS) : RiemannSurfaces.Algebraic.Divisor RS where
  coeff := D.coeff
  finiteSupport := D.finiteSupport

/-- Transport an algebraic RS-level divisor into the analytic model by
reusing the same coefficient function and finite-support witness. -/
noncomputable def algebraicToAnalyticDivisor {RS : RiemannSurface}
    (D : RiemannSurfaces.Algebraic.Divisor RS) : RiemannSurfaces.Analytic.Divisor RS where
  coeff := D.coeff
  finiteSupport := D.finiteSupport

@[simp] theorem algebraicToAnalytic_left_inv {RS : RiemannSurface}
    (D : RiemannSurfaces.Analytic.Divisor RS) :
    algebraicToAnalyticDivisor (analyticToAlgebraicDivisor D) = D := by
  ext p
  rfl

@[simp] theorem analyticToAlgebraic_left_inv {RS : RiemannSurface}
    (D : RiemannSurfaces.Algebraic.Divisor RS) :
    analyticToAlgebraicDivisor (algebraicToAnalyticDivisor D) = D := by
  ext p
  rfl

@[simp] theorem analyticToAlgebraic_map_zero {RS : RiemannSurface} :
    analyticToAlgebraicDivisor (0 : RiemannSurfaces.Analytic.Divisor RS) =
      (0 : RiemannSurfaces.Algebraic.Divisor RS) := by
  ext p
  rfl

@[simp] theorem analyticToAlgebraic_map_add {RS : RiemannSurface}
    (D₁ D₂ : RiemannSurfaces.Analytic.Divisor RS) :
    analyticToAlgebraicDivisor (D₁ + D₂) =
      analyticToAlgebraicDivisor D₁ + analyticToAlgebraicDivisor D₂ := by
  ext p
  rfl

@[simp] theorem analyticToAlgebraic_map_neg {RS : RiemannSurface}
    (D : RiemannSurfaces.Analytic.Divisor RS) :
    analyticToAlgebraicDivisor (-D) = -analyticToAlgebraicDivisor D := by
  ext p
  rfl

@[simp] theorem analyticToAlgebraic_map_point {RS : RiemannSurface} (p : RS.carrier) :
    analyticToAlgebraicDivisor (RiemannSurfaces.Analytic.Divisor.point p) =
      RiemannSurfaces.Algebraic.Divisor.point p := by
  ext q
  rfl

@[simp] theorem analyticToAlgebraic_map_coeff {RS : RiemannSurface}
    (D : RiemannSurfaces.Analytic.Divisor RS) (p : RS.carrier) :
    DivisorModel.coeff (Point := RS.carrier) (Divisor := RiemannSurfaces.Algebraic.Divisor RS)
      (analyticToAlgebraicDivisor D) p =
    DivisorModel.coeff (Point := RS.carrier) (Divisor := RiemannSurfaces.Analytic.Divisor RS)
      D p :=
  rfl

@[simp] theorem analyticToAlgebraic_map_degree {RS : RiemannSurface}
    (D : RiemannSurfaces.Analytic.Divisor RS) :
    DivisorModel.degree (Point := RS.carrier) (Divisor := RiemannSurfaces.Algebraic.Divisor RS)
      (analyticToAlgebraicDivisor D) =
    DivisorModel.degree (Point := RS.carrier) (Divisor := RiemannSurfaces.Analytic.Divisor RS)
      D := by
  rfl

/-- Concrete transport package used by GAGA bridge code. -/
noncomputable def analyticAlgebraicDivisorTransport (RS : RiemannSurface) :
    DivisorTransport RS.carrier
      (RiemannSurfaces.Analytic.Divisor RS)
      (RiemannSurfaces.Algebraic.Divisor RS) where
  toFun := analyticToAlgebraicDivisor
  invFun := algebraicToAnalyticDivisor
  left_inv := by
    intro D
    exact algebraicToAnalytic_left_inv D
  right_inv := by
    intro D
    exact analyticToAlgebraic_left_inv D
  map_zero := analyticToAlgebraic_map_zero
  map_add := analyticToAlgebraic_map_add
  map_neg := analyticToAlgebraic_map_neg
  map_point := analyticToAlgebraic_map_point
  map_coeff := analyticToAlgebraic_map_coeff
  map_degree := analyticToAlgebraic_map_degree

end RiemannSurfaces.Core
