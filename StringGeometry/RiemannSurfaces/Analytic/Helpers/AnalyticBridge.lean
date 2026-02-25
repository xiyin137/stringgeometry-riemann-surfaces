import StringGeometry.RiemannSurfaces.Analytic.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Analytic Bridge: MDifferentiable ↔ AnalyticAt in Charts

This file bridges manifold-level holomorphicity (`MDifferentiableAt`) on Riemann surfaces
to chart-local analyticity (`AnalyticAt`), and provides key consequences:
identity principle and isolated zeros.

## Main Results

* `rs_identity_principle_compact` — On compact RS, holomorphic f with f(p) = 0 ⟹ f ≡ 0
* `mdifferentiableAt_finset_sum` — Finite sum of MDifferentiableAt functions
* `mdifferentiableAt_const_mul` — Scalar multiple of MDifferentiableAt function

## References

* Mathlib.Analysis.Complex.CauchyIntegral — DifferentiableOn → AnalyticAt
* Mathlib.Geometry.Manifold.Complex — MDifferentiable.exists_eq_const_of_compactSpace
-/

namespace RiemannSurfaces.Analytic

open Complex
open scoped Manifold Topology

/-!
## Identity Principle (Compact Case)

On a compact connected Riemann surface, every holomorphic function is constant.
Therefore any holomorphic function with a zero is identically zero.
-/

section IdentityPrinciple

/-- **Compact RS identity principle.**

    On a compact connected Riemann surface, a holomorphic function
    with f(p) = 0 for some p must be identically zero.

    This follows immediately from `holomorphicIsConstant` (maximum modulus principle). -/
theorem rs_identity_principle_compact (CRS : CompactRiemannSurface)
    (f : CRS.carrier → ℂ) (hf : CRS.toRiemannSurface.IsHolomorphic f)
    (p : CRS.carrier) (hp : f p = 0) :
    ∀ x : CRS.carrier, f x = 0 := by
  obtain ⟨c, hc⟩ := CRS.holomorphicIsConstant f hf
  have : c = 0 := by rw [← hp, hc p]
  intro x; rw [hc x, this]

/-- Two holomorphic functions on a compact RS that agree at one point agree everywhere. -/
theorem rs_holomorphic_eq_of_eq_at_point (CRS : CompactRiemannSurface)
    (f g : CRS.carrier → ℂ)
    (hf : CRS.toRiemannSurface.IsHolomorphic f)
    (hg : CRS.toRiemannSurface.IsHolomorphic g)
    (p : CRS.carrier) (hp : f p = g p) :
    ∀ x, f x = g x := by
  -- f - g is holomorphic and (f-g)(p) = 0
  have hfg : CRS.toRiemannSurface.IsHolomorphic (fun x => f x - g x) := by
    letI := CRS.toRiemannSurface.topology
    letI := CRS.toRiemannSurface.chartedSpace
    haveI := CRS.toRiemannSurface.isManifold
    intro x
    exact (hf x).sub (hg x)
  have hfgp : (fun x => f x - g x) p = 0 := by simp [hp]
  have hall := rs_identity_principle_compact CRS _ hfg p hfgp
  intro x
  have := hall x
  exact sub_eq_zero.mp this

end IdentityPrinciple

/-!
## Sum of MDifferentiable Functions

Finite sums and scalar multiples of MDifferentiable functions.
-/

section MDifferentiableSum

variable {RS : RiemannSurface}

/-- A finite sum of MDifferentiableAt functions is MDifferentiableAt. -/
theorem mdifferentiableAt_finset_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → RS.carrier → ℂ) (p : RS.carrier)
    (hf : ∀ i ∈ s, @MDifferentiableAt ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ)
      RS.carrier RS.topology RS.chartedSpace ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ℂ _ _ (f i) p) :
    @MDifferentiableAt ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ)
      RS.carrier RS.topology RS.chartedSpace ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ℂ _ _
      (fun x => s.sum (fun i => f i x)) p := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact mdifferentiableAt_const
  | @insert a s ha ih =>
    have heq : (fun x => ∑ i ∈ insert a s, f i x) =
        (fun x => f a x + ∑ i ∈ s, f i x) := by
      ext x; exact Finset.sum_insert ha
    rw [heq]
    exact (hf _ (Finset.mem_insert_self _ _)).add
      (ih (fun i hi' => hf i (Finset.mem_insert_of_mem hi')))

/-- Scalar multiplication of an MDifferentiableAt function is MDifferentiableAt. -/
theorem mdifferentiableAt_const_mul (c : ℂ) (f : RS.carrier → ℂ) (p : RS.carrier)
    (hf : @MDifferentiableAt ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ)
      RS.carrier RS.topology RS.chartedSpace ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ℂ _ _ f p) :
    @MDifferentiableAt ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ)
      RS.carrier RS.topology RS.chartedSpace ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ℂ _ _
      (fun x => c * f x) p := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  exact mdifferentiableAt_const.mul hf

/-- A finite sum of the form Σ cᵢ * fᵢ is MDifferentiableAt when each fᵢ is. -/
theorem mdifferentiableAt_linear_combination {n : ℕ}
    (f : Fin n → RS.carrier → ℂ) (c : Fin n → ℂ) (p : RS.carrier)
    (hf : ∀ i, @MDifferentiableAt ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ)
      RS.carrier RS.topology RS.chartedSpace ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ℂ _ _ (f i) p) :
    @MDifferentiableAt ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ)
      RS.carrier RS.topology RS.chartedSpace ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ℂ _ _
      (fun x => Finset.univ.sum (fun i => c i * f i x)) p := by
  apply mdifferentiableAt_finset_sum
  intro i _
  exact mdifferentiableAt_const_mul (c i) (f i) p (hf i)

end MDifferentiableSum

end RiemannSurfaces.Analytic
