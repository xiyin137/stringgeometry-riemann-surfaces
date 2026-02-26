import StringGeometry.RiemannSurfaces.Core.PrincipalDivisorModel
import StringGeometry.RiemannSurfaces.Core.AnalyticDivisor
import StringGeometry.RiemannSurfaces.Analytic.Divisors

namespace RiemannSurfaces.Core

open RiemannSurfaces

/-- Adapter exposing analytic principal divisors and linear equivalence through
`PrincipalDivisorModel`. -/
noncomputable instance analyticPrincipalDivisorModel (RS : RiemannSurface) :
    PrincipalDivisorModel RS.carrier (RiemannSurfaces.Analytic.Divisor RS) where
  IsPrincipal := RiemannSurfaces.Analytic.Divisor.IsPrincipal
  zero_isPrincipal := by
    refine ⟨(1 : RiemannSurfaces.Analytic.AnalyticMeromorphicFunction RS), ?_⟩
    simpa using (RiemannSurfaces.Analytic.divisorOf_one (RS := RS))
  add_isPrincipal := by
    intro D₁ D₂ h₁ h₂
    rcases h₁ with ⟨f, hf⟩
    rcases h₂ with ⟨g, hg⟩
    refine ⟨f * g, ?_⟩
    rw [RiemannSurfaces.Analytic.divisorOf_mul, hf, hg]
  neg_isPrincipal := by
    intro D hD
    rcases hD with ⟨f, hf⟩
    refine ⟨f⁻¹, ?_⟩
    rw [RiemannSurfaces.Analytic.divisorOf_inv, hf]

end RiemannSurfaces.Core
