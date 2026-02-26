import StringGeometry.RiemannSurfaces.Core

namespace RiemannSurfaces.GAGA.Bridge

open RiemannSurfaces

/-- The canonical transport between analytic and algebraic RS-level divisors
used by GAGA bridge statements. -/
noncomputable def analyticAlgebraicDivisorTransport (RS : RiemannSurface) :=
  RiemannSurfaces.Core.analyticAlgebraicDivisorTransport RS

/-- Degree is preserved under the canonical analytic→algebraic divisor transport. -/
theorem analytic_to_algebraic_degree
    {RS : RiemannSurface}
    (D : RiemannSurfaces.Analytic.Divisor RS) :
    RiemannSurfaces.Core.DivisorModel.degree
        (Point := RS.carrier)
        (Divisor := RiemannSurfaces.Algebraic.Divisor RS)
        (RiemannSurfaces.Core.analyticToAlgebraicDivisor D) =
      RiemannSurfaces.Core.DivisorModel.degree
        (Point := RS.carrier)
        (Divisor := RiemannSurfaces.Analytic.Divisor RS)
        D := by
  simpa using
    (analyticAlgebraicDivisorTransport RS).map_degree D

/-- Coefficients are preserved pointwise under the canonical transport. -/
theorem analytic_to_algebraic_coeff
    {RS : RiemannSurface}
    (D : RiemannSurfaces.Analytic.Divisor RS)
    (p : RS.carrier) :
    RiemannSurfaces.Core.DivisorModel.coeff
        (Point := RS.carrier)
        (Divisor := RiemannSurfaces.Algebraic.Divisor RS)
        (RiemannSurfaces.Core.analyticToAlgebraicDivisor D) p =
      RiemannSurfaces.Core.DivisorModel.coeff
        (Point := RS.carrier)
        (Divisor := RiemannSurfaces.Analytic.Divisor RS)
        D p := by
  simpa using
    (analyticAlgebraicDivisorTransport RS).map_coeff D p

end RiemannSurfaces.GAGA.Bridge
