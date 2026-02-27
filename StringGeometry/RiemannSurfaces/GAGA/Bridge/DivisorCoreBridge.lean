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
  exact (analyticAlgebraicDivisorTransport RS).map_degree D

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
  exact (analyticAlgebraicDivisorTransport RS).map_coeff D p

/-- If principal divisors are transported by a `PrincipalDivisorTransport`,
then linear equivalence is transported as well. -/
theorem analytic_to_algebraic_linearlyEquivalent
    {RS : RiemannSurface}
    [RiemannSurfaces.Core.PrincipalDivisorModel
      RS.carrier
      (RiemannSurfaces.Algebraic.Divisor RS)]
    (P : RiemannSurfaces.Core.PrincipalDivisorTransport
      RS.carrier
      (RiemannSurfaces.Analytic.Divisor RS)
      (RiemannSurfaces.Algebraic.Divisor RS)
      (analyticAlgebraicDivisorTransport RS))
    {D₁ D₂ : RiemannSurfaces.Analytic.Divisor RS}
    (h : RiemannSurfaces.Core.PrincipalDivisorModel.LinearlyEquivalent
      (Point := RS.carrier)
      (Divisor := RiemannSurfaces.Analytic.Divisor RS)
      D₁ D₂) :
    RiemannSurfaces.Core.PrincipalDivisorModel.LinearlyEquivalent
      (Point := RS.carrier)
      (Divisor := RiemannSurfaces.Algebraic.Divisor RS)
      (RiemannSurfaces.Core.analyticToAlgebraicDivisor D₁)
      (RiemannSurfaces.Core.analyticToAlgebraicDivisor D₂) := by
  exact RiemannSurfaces.Core.PrincipalDivisorTransport.map_linearlyEquivalent P h

end RiemannSurfaces.GAGA.Bridge
