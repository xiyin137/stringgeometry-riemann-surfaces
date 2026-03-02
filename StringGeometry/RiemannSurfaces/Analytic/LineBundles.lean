import StringGeometry.RiemannSurfaces.Analytic.Divisors
import StringGeometry.RiemannSurfaces.Analytic.Helpers.ChartMeromorphic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Holomorphic Line Bundles on Riemann Surfaces

This file develops the theory of holomorphic line bundles on Riemann surfaces
from the **analytic** perspective.

## Mathematical Background

A holomorphic line bundle L → Σ is a complex line bundle with holomorphic
transition functions. The key correspondence is:

  **Divisors ↔ Line Bundles ↔ Pic(Σ)**

Given a divisor D, the associated line bundle O(D) has:
- Sections: meromorphic functions f with (f) + D ≥ 0
- The space of global sections: L(D) = H⁰(Σ, O(D))

### Key Definitions

- **O(D)**: The line bundle associated to divisor D
- **L(D) = H⁰(O(D))**: Space of global sections
- **h⁰(D) = dim L(D)**: Dimension of section space

## References

* Griffiths, Harris "Principles of Algebraic Geometry" Ch 2
* Farkas, Kra "Riemann Surfaces" Ch III
-/

namespace RiemannSurfaces.Analytic

open Divisor
open scoped Manifold

/-!
## Holomorphic Line Bundles

A holomorphic line bundle is a complex line bundle with holomorphic structure.
-/

/-- A holomorphic line bundle on a Riemann surface.

    In the analytic approach, a line bundle is characterized by:
    - Its underlying topological line bundle
    - Holomorphic transition functions
    - The associated divisor (up to linear equivalence)

    For simplicity, we define it via its associated divisor class.
    Line bundles form a group under tensor product: O(D₁) ⊗ O(D₂) = O(D₁ + D₂). -/
structure HolomorphicLineBundle (RS : RiemannSurface) where
  /-- The associated divisor (well-defined up to linear equivalence) -/
  divisor : Divisor RS

namespace HolomorphicLineBundle

variable {RS : RiemannSurface}

/-- The trivial line bundle O -/
def trivial : HolomorphicLineBundle RS where
  divisor := 0

/-- The line bundle O(D) associated to divisor D -/
def ofDivisor (D : Divisor RS) : HolomorphicLineBundle RS where
  divisor := D

/-- Tensor product of line bundles: O(D₁) ⊗ O(D₂) = O(D₁ + D₂) -/
def tensor (L₁ L₂ : HolomorphicLineBundle RS) : HolomorphicLineBundle RS where
  divisor := L₁.divisor + L₂.divisor

/-- Dual line bundle: O(D)* = O(-D) -/
def dual (L : HolomorphicLineBundle RS) : HolomorphicLineBundle RS where
  divisor := -L.divisor

instance : One (HolomorphicLineBundle RS) := ⟨trivial⟩
instance : Mul (HolomorphicLineBundle RS) := ⟨tensor⟩
instance : Inv (HolomorphicLineBundle RS) := ⟨dual⟩

/-- The degree of a line bundle: deg(O(D)) = deg(D) -/
noncomputable def degree (L : HolomorphicLineBundle RS) : ℤ :=
  L.divisor.degree

/-- Degree is additive under tensor product -/
theorem degree_tensor (L₁ L₂ : HolomorphicLineBundle RS) :
    (L₁ * L₂).degree = L₁.degree + L₂.degree := by
  show (tensor L₁ L₂).divisor.degree = L₁.divisor.degree + L₂.divisor.degree
  simp only [tensor, degree_add]

end HolomorphicLineBundle

/-!
## Global Sections

L(D) = { f meromorphic : (f) + D ≥ 0 }

This is the space of meromorphic functions whose poles are "cancelled" by D.
-/

/-- The linear system L(D): meromorphic functions f with (f) + D ≥ 0.

    This is a ℂ-vector space (in fact, finite-dimensional for compact surfaces).

    **TODO:** Add vector space structure to compute h⁰(D) = dim L(D). -/
structure LinearSystem (RS : RiemannSurface) (D : Divisor RS) where
  /-- A section is a meromorphic function with (f) + D ≥ 0 -/
  fn : AnalyticMeromorphicFunction RS
  /-- The divisor condition: div(f) + D is effective -/
  effective : Divisor.Effective (divisorOf fn + D)
  /-- The regularValue function is holomorphic (MDifferentiable in charts) at non-pole points.

      This is the key analytical condition connecting the abstract AMF structure
      to the complex geometry of the Riemann surface. At any point p where
      fn.order p ≥ 0 (non-pole), the function fn.regularValue is complex-differentiable
      in the manifold sense, i.e., holomorphic in local coordinates.

      Without this condition, the AMF is purely algebraic and has no connection
      to the smooth/holomorphic structure of the underlying Riemann surface. -/
  holomorphicAway : ∀ p, 0 ≤ fn.order p →
    @MDifferentiableAt ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) RS.carrier RS.topology RS.chartedSpace
      ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ℂ _ _ fn.regularValue p
  /-- The regularValue function is meromorphic in every chart.

      This is the full analytical condition: at EVERY point (including poles),
      the chart representation `fn.regularValue ∘ (extChartAt p).symm` is
      `MeromorphicAt` in the sense of Mathlib.

      At non-pole points, this follows from `holomorphicAway` (holomorphic → analytic
      → meromorphic). At poles, this captures the essential Laurent expansion behavior:
      multiplying by a suitable power of the local coordinate makes the function analytic.

      This field is critical for the argument principle and zero-counting arguments. -/
  chartMeromorphic : ∀ p,
    letI := RS.topology
    letI := RS.chartedSpace
    MeromorphicAt (fn.regularValue ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm) (extChartAt 𝓘(ℂ, ℂ) p p)
  /-- The chart-local meromorphic order matches the abstract AMF order.

      This is the soundness condition connecting the abstract `fn.order` field
      (an integer assigned per point by the AMF structure) to the analytic
      `meromorphicOrderAt` computed from the Laurent expansion in charts.

      At non-pole points (order ≥ 0), this follows from `holomorphicAway`:
      the function is analytic, so the analytic order matches the zero order.
      At poles (order < 0), this requires the Laurent expansion to have the
      correct leading term, which is part of the analytical content of the section.

      This field is critical for reducing `zero_counting_linear_combination`
      to the argument principle: it lets us bound the chart-order of a
      linear combination Σ cᵢ fᵢ using the AMF orders of the individual fᵢ. -/
  chartOrderAt_eq : ∀ p,
    letI := RS.topology
    letI := RS.chartedSpace
    chartOrderAt (RS := RS) fn.regularValue p = (fn.order p : WithTop ℤ)

/-- The linear system L(D) is empty when deg(D) < 0.

    **Proof idea:**
    If f ∈ L(D), then div(f) + D ≥ 0, so deg(div(f)) + deg(D) ≥ 0.
    By the argument principle, deg(div(f)) = 0 for meromorphic functions.
    Thus deg(D) ≥ 0, contradicting deg(D) < 0. -/
theorem linearSystem_empty_negative_degree (CRS : CompactRiemannSurface)
    (D : Divisor CRS.toRiemannSurface) (hdeg : D.degree < 0) :
    IsEmpty (LinearSystem CRS.toRiemannSurface D) := by
  constructor
  intro ls
  -- div(f) + D ≥ 0 means deg(div(f) + D) ≥ 0
  have hdeg_sum : (divisorOf ls.fn + D).degree ≥ 0 :=
    Divisor.degree_nonneg_of_effective ls.effective
  rw [Divisor.degree_add] at hdeg_sum
  -- deg(div(f)) = 0 from chart-order argument principle + order compatibility
  have hsum_zero : analyticOrderSum ls.fn = 0 :=
    analyticArgumentPrinciple_of_chartData CRS ls.fn
      (fun p => ls.chartMeromorphic p) (fun p => ls.chartOrderAt_eq p)
  have hdiv_zero : (divisorOf ls.fn).degree = 0 :=
    (principal_divisor_degree_zero CRS ls.fn).trans hsum_zero
  rw [hdiv_zero] at hdeg_sum
  simp at hdeg_sum
  omega

end RiemannSurfaces.Analytic
