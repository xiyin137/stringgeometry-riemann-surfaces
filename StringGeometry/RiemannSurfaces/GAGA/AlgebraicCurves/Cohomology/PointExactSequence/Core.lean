import StringGeometry.RiemannSurfaces.GAGA.AlgebraicCurves.Cohomology.AlgebraicCech
import StringGeometry.RiemannSurfaces.GAGA.AlgebraicCurves.Cohomology.AlternatingSum
import StringGeometry.RiemannSurfaces.GAGA.Helpers.ResidueSumTheorem
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Point Exact Sequence for Riemann-Roch

This file proves the key dimension constraint for the Riemann-Roch theorem using
the long exact sequence in sheaf cohomology.

## The Exact Sequence

The short exact sequence of sheaves:
  0 → O(D-p) → O(D) → ℂ_p → 0

induces a long exact sequence in cohomology:
  0 → H⁰(D-p) → H⁰(D) → H⁰(ℂ_p) → H¹(D-p) → H¹(D) → H¹(ℂ_p) → 0

Since H⁰(ℂ_p) = ℂ (dimension 1) and H¹(ℂ_p) = 0 (skyscraper is acyclic),
this becomes a 5-term sequence:
  0 → L(D-p) → L(D) → ℂ → H¹(D-p) → H¹(D) → 0

## Main Result

The alternating sum formula for this exact sequence gives:
  h⁰(D-p) - h⁰(D) + 1 - h¹(D-p) + h¹(D) = 0

Using Serre duality h¹(E) = h⁰(K-E):
  h⁰(D-p) - h⁰(D) + 1 - h⁰(K-D+p) + h⁰(K-D) = 0

Which rearranges to: (h⁰(D) - h⁰(D-p)) + (h⁰(K-D+p) - h⁰(K-D)) = 1

This is `LES_dimension_constraint`.
-/

namespace RiemannSurfaces.Algebraic.Cohomology.PointExactSequence

open Algebraic CompactAlgebraicCurve Core.Divisor AlternatingSum
open scoped Classical

variable (C : Algebraic.CompactAlgebraicCurve)
variable (K : CanonicalDivisor C)
variable (D : Core.Divisor C.toAlgebraicCurve)
variable (p : C.toAlgebraicCurve.Point)

/-!
## Helper Lemmas for RiemannRochSpace Membership

These lemmas make it easier to work with membership in L(D) and L(D-p).
-/

/-- Membership in L(D): f = 0 or f has no poles worse than D allows -/
theorem mem_RiemannRochSpace_iff (f : C.FunctionField) :
    f ∈ RiemannRochSpace C.toAlgebraicCurve D ↔
    f = 0 ∨ ∀ q, C.valuation q f + D.coeff q ≥ 0 := by
  simp only [RiemannRochSpace, Set.mem_setOf_eq]

/-- Nonzero element in L(D) has bounded poles -/
theorem nonzero_mem_RiemannRochSpace_iff (f : C.FunctionField) (hf : f ≠ 0) :
    f ∈ RiemannRochSpace C.toAlgebraicCurve D ↔
    ∀ q, C.valuation q f + D.coeff q ≥ 0 := by
  simp only [RiemannRochSpace, Set.mem_setOf_eq]
  constructor
  · intro h
    rcases h with rfl | hval
    · exact absurd rfl hf
    · exact hval
  · intro h; right; exact h

/-- Non-membership in L(D-p) for nonzero f: at some point the valuation condition fails -/
theorem not_mem_RiemannRochSpace_sub_point_iff (f : C.FunctionField) (hf : f ≠ 0) :
    f ∉ RiemannRochSpace C.toAlgebraicCurve (D - point p) ↔
    ∃ q, C.valuation q f + (D - point p).coeff q < 0 := by
  rw [nonzero_mem_RiemannRochSpace_iff C (D - point p) f hf]
  push_neg
  rfl

/-- Key lemma: f ∈ L(D) but f ∉ L(D-p) implies v_p(f) = -D(p) -/
theorem valuation_eq_neg_coeff_of_in_D_not_in_Dp (f : C.FunctionField)
    (hf_D : f ∈ RiemannRochSpace C.toAlgebraicCurve D)
    (hf_not : f ∉ RiemannRochSpace C.toAlgebraicCurve (D - point p)) :
    C.valuation p f = -D.coeff p := by
  -- f must be nonzero (since 0 ∈ L(D-p))
  have hf_ne : f ≠ 0 := by
    intro heq
    apply hf_not
    rw [heq]
    exact zero_mem_RiemannRochSpace C.toAlgebraicCurve (D - point p)
  -- f ∈ L(D) means v_q(f) ≥ -D(q) for all q
  have hval_D : ∀ q, C.valuation q f + D.coeff q ≥ 0 := by
    rwa [nonzero_mem_RiemannRochSpace_iff C D f hf_ne] at hf_D
  -- f ∉ L(D-p) means ∃ q, v_q(f) + (D-p)(q) < 0
  rw [not_mem_RiemannRochSpace_sub_point_iff C D p f hf_ne] at hf_not
  obtain ⟨q, hq⟩ := hf_not
  -- The failing point must be p (since D and D-p only differ at p)
  simp only [sub_coeff, point] at hq
  by_cases hqp : q = p
  · -- q = p: v_p(f) + D(p) - 1 < 0, so v_p(f) < -D(p) + 1
    simp only [hqp, if_true] at hq
    have hp := hval_D p
    omega
  · -- q ≠ p: v_q(f) + D(q) < 0, contradicting f ∈ L(D)
    simp only [if_neg hqp, sub_zero] at hq
    have hqval := hval_D q
    omega

/-- Valuation of element in L(D-p) is strictly greater than -D(p) -/
theorem valuation_gt_of_mem_sub_point (f : C.FunctionField) (hf : f ≠ 0)
    (hf_mem : f ∈ RiemannRochSpace C.toAlgebraicCurve (D - point p)) :
    C.valuation p f > -D.coeff p := by
  rw [nonzero_mem_RiemannRochSpace_iff C (D - point p) f hf] at hf_mem
  specialize hf_mem p
  simp only [sub_coeff, point, if_true] at hf_mem
  omega

/-- Uniqueness of coefficient: if g - c₁*f₀ and g - c₂*f₀ both have higher valuation
    (or are zero), then c₁ = c₂. -/
theorem coeff_unique (f₀ g : C.FunctionField) (hf₀_ne : f₀ ≠ 0)
    (hf₀_val : C.valuation p f₀ = -D.coeff p)
    (hg_val : C.valuation p g = -D.coeff p)
    (c₁ c₂ : ℂ) (hc₁_ne : c₁ ≠ 0) (hc₂_ne : c₂ ≠ 0)
    (h₁ : g - algebraMap ℂ C.FunctionField c₁ * f₀ = 0 ∨
          C.valuation p (g - algebraMap ℂ C.FunctionField c₁ * f₀) > C.valuation p g)
    (h₂ : g - algebraMap ℂ C.FunctionField c₂ * f₀ = 0 ∨
          C.valuation p (g - algebraMap ℂ C.FunctionField c₂ * f₀) > C.valuation p g) :
    c₁ = c₂ := by
  -- If both differences are zero, then c₁*f₀ = c₂*f₀, so c₁ = c₂
  -- If one is zero and the other has higher valuation, we get a contradiction
  -- If both have higher valuation, then (c₁ - c₂)*f₀ has higher valuation, so c₁ = c₂
  rcases h₁ with h₁_eq | h₁_gt <;> rcases h₂ with h₂_eq | h₂_gt
  · -- Both zero: g = c₁*f₀ = c₂*f₀
    rw [sub_eq_zero] at h₁_eq h₂_eq
    have heq : algebraMap ℂ C.FunctionField c₁ * f₀ = algebraMap ℂ C.FunctionField c₂ * f₀ := by
      rw [← h₁_eq, h₂_eq]
    have halg₁_ne : algebraMap ℂ C.FunctionField c₁ ≠ 0 := by simp [hc₁_ne]
    have halg₂_ne : algebraMap ℂ C.FunctionField c₂ ≠ 0 := by simp [hc₂_ne]
    have hcf₁_ne : algebraMap ℂ C.FunctionField c₁ * f₀ ≠ 0 := mul_ne_zero halg₁_ne hf₀_ne
    have halg_eq : algebraMap ℂ C.FunctionField c₁ = algebraMap ℂ C.FunctionField c₂ := by
      have := mul_right_cancel₀ hf₀_ne heq
      exact this
    exact (algebraMap ℂ C.FunctionField).injective halg_eq
  · -- h₁ zero, h₂ higher: (g - c₂f₀) = (c₁ - c₂)f₀ has higher valuation
    -- If c₁ ≠ c₂, then (c₁ - c₂)f₀ has valuation = f₀, contradiction
    rw [sub_eq_zero] at h₁_eq
    rw [h₁_eq] at h₂_gt
    by_contra hne
    have hdiff_ne : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hne
    have halg_ne : algebraMap ℂ C.FunctionField (c₁ - c₂) ≠ 0 := by
      simp only [map_ne_zero]; exact hdiff_ne
    have : algebraMap ℂ C.FunctionField c₁ * f₀ - algebraMap ℂ C.FunctionField c₂ * f₀ =
           algebraMap ℂ C.FunctionField (c₁ - c₂) * f₀ := by
      simp only [map_sub, sub_mul]
    rw [this] at h₂_gt
    have hval_eq : C.valuation p (algebraMap ℂ C.FunctionField (c₁ - c₂) * f₀) =
                   C.valuation p f₀ := by
      rw [C.toAlgebraicCurve.valuation_mul p _ _ halg_ne hf₀_ne,
          C.algebraInst.valuation_algebraMap p (c₁ - c₂) hdiff_ne, zero_add]
    rw [hval_eq, hf₀_val] at h₂_gt
    have halg₁_ne : algebraMap ℂ C.FunctionField c₁ ≠ 0 := by simp [hc₁_ne]
    have hcf₁_val : C.valuation p (algebraMap ℂ C.FunctionField c₁ * f₀) = -D.coeff p := by
      rw [C.toAlgebraicCurve.valuation_mul p _ _ halg₁_ne hf₀_ne,
          C.algebraInst.valuation_algebraMap p c₁ hc₁_ne, zero_add, hf₀_val]
    rw [hcf₁_val] at h₂_gt
    omega
  · -- h₁ higher, h₂ zero: g = c₂*f₀
    rw [sub_eq_zero] at h₂_eq
    -- Now h₁_gt: v(g - c₁*f₀) > v(g) = v(c₂*f₀)
    -- Substituting g = c₂*f₀: v((c₂-c₁)*f₀) > v(c₂*f₀)
    -- But both have valuation = v(f₀) = -D(p), contradiction
    by_contra hne
    have hdiff_ne : c₂ - c₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have halg_diff_ne : algebraMap ℂ C.FunctionField (c₂ - c₁) ≠ 0 := by
      simp only [map_ne_zero]; exact hdiff_ne
    have halg₂_ne : algebraMap ℂ C.FunctionField c₂ ≠ 0 := by simp [hc₂_ne]
    -- After substituting g = c₂*f₀
    have hdiff_eq : g - algebraMap ℂ C.FunctionField c₁ * f₀ =
                    algebraMap ℂ C.FunctionField (c₂ - c₁) * f₀ := by
      rw [h₂_eq]
      simp only [map_sub, sub_mul]
    -- v((c₂-c₁)*f₀) = v(f₀) = -D(p)
    have hdiff_val : C.valuation p (algebraMap ℂ C.FunctionField (c₂ - c₁) * f₀) = -D.coeff p := by
      rw [C.toAlgebraicCurve.valuation_mul p _ _ halg_diff_ne hf₀_ne,
          C.algebraInst.valuation_algebraMap p (c₂ - c₁) hdiff_ne, zero_add, hf₀_val]
    -- v(c₂*f₀) = v(f₀) = -D(p)
    have hg_new_val : C.valuation p g = -D.coeff p := by
      rw [h₂_eq, C.toAlgebraicCurve.valuation_mul p _ _ halg₂_ne hf₀_ne,
          C.algebraInst.valuation_algebraMap p c₂ hc₂_ne, zero_add, hf₀_val]
    -- Now h₁_gt says v((c₂-c₁)*f₀) > v(g), but both = -D(p)
    rw [hdiff_eq, hdiff_val, hg_new_val] at h₁_gt
    omega
  · -- Both have higher valuation
    -- Key: (g - c₁f₀) + (-(g - c₂f₀)) = (c₂ - c₁)f₀
    -- If c₁ ≠ c₂, then v((c₂-c₁)*f₀) = -D(p)
    -- But by ultrametric, v(sum) ≥ min(v(g-c₁f₀), v(g-c₂f₀)) > -D(p)
    -- Unless sum = 0, which gives c₁ = c₂
    by_contra hne
    have hdiff_ne : c₂ - c₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have halg_ne : algebraMap ℂ C.FunctionField (c₂ - c₁) ≠ 0 := by
      simp only [map_ne_zero]; exact hdiff_ne
    -- v((c₂-c₁)*f₀) = -D(p)
    have hdiff_val : C.valuation p (algebraMap ℂ C.FunctionField (c₂ - c₁) * f₀) = -D.coeff p := by
      rw [C.toAlgebraicCurve.valuation_mul p _ _ halg_ne hf₀_ne,
          C.algebraInst.valuation_algebraMap p (c₂ - c₁) hdiff_ne, zero_add, hf₀_val]
    -- The key sum identity
    have hsum_identity : (g - algebraMap ℂ C.FunctionField c₁ * f₀) +
                         (-(g - algebraMap ℂ C.FunctionField c₂ * f₀)) =
                         algebraMap ℂ C.FunctionField (c₂ - c₁) * f₀ := by
      simp only [map_sub, sub_mul]; ring
    -- The sum (g - c₁f₀) + (-(g - c₂f₀)) = (c₂ - c₁)*f₀ is NONZERO
    -- since c₂ - c₁ ≠ 0 and f₀ ≠ 0
    have hsum_ne : (g - algebraMap ℂ C.FunctionField c₁ * f₀) +
                   (-(g - algebraMap ℂ C.FunctionField c₂ * f₀)) ≠ 0 := by
      rw [hsum_identity]
      exact mul_ne_zero halg_ne hf₀_ne
    -- Valuation of the negation: need g - c₂*f₀ ≠ 0
    have h₂_sub_ne : g - algebraMap ℂ C.FunctionField c₂ * f₀ ≠ 0 := by
      intro heq
      -- If g - c₂*f₀ = 0, then h₂_gt says v(0) > v(g).
      -- Since v(0) = 0 and v(g) = -D.coeff p, we get 0 > -D.coeff p.
      rw [heq] at h₂_gt
      simp only [C.toAlgebraicCurve.valuation_zero] at h₂_gt
      rw [hg_val] at h₂_gt
      -- h₂_gt now says 0 > -D.coeff p
      -- But we also have v(f₀) = -D.coeff p and f₀ ≠ 0
      -- Since f₀ ≠ 0, v(f₀) should be a valid valuation.
      -- The key insight: if D.coeff p ≤ 0, then v(f₀) ≥ 0, which means f₀ is in the
      -- valuation ring, not having a pole. But f₀ ∈ L(D) \ L(D-p) means it has
      -- exactly the allowed pole order at p, which is -D.coeff p.
      -- The contradiction: h₂_gt says 0 > -D.coeff p, i.e., D.coeff p > 0
      -- But we also have h₁_gt: v(g - c₁*f₀) > v(g) = -D.coeff p
      -- Both h₁_gt and h₂_gt are > -D.coeff p.
      -- If D.coeff p > 0, then -D.coeff p < 0, and v(0) = 0 > -D.coeff p is true!
      -- So there's no contradiction from h₂_gt alone.
      -- The real contradiction comes from the ultrametric inequality:
      -- (g - c₁*f₀) + (-(g - c₂*f₀)) = (c₂-c₁)*f₀ has v = -D.coeff p (from hdiff_val)
      -- But if v(g - c₁*f₀) > -D.coeff p and v(-(g - c₂*f₀)) > -D.coeff p (since g - c₂*f₀ = 0),
      -- then by ultrametric, their sum has v > -D.coeff p or = 0.
      -- But the sum = (c₂-c₁)*f₀ which has v = -D.coeff p and is nonzero. Contradiction!
      -- Let me formalize this:
      have hsum_simp : (g - algebraMap ℂ C.FunctionField c₁ * f₀) +
                       (-(g - algebraMap ℂ C.FunctionField c₂ * f₀)) =
                       g - algebraMap ℂ C.FunctionField c₁ * f₀ := by
        rw [heq, neg_zero, add_zero]
      rw [hsum_simp] at hsum_identity
      -- hsum_identity now says g - c₁*f₀ = (c₂-c₁)*f₀
      -- Both sides are equal and nonzero (since (c₂-c₁)*f₀ ≠ 0)
      -- So v(g - c₁*f₀) = v((c₂-c₁)*f₀) = -D.coeff p (by hdiff_val)
      -- But h₁_gt says v(g - c₁*f₀) > v(g) = -D.coeff p
      have hval_eq : C.valuation p (g - algebraMap ℂ C.FunctionField c₁ * f₀) = -D.coeff p := by
        rw [hsum_identity, hdiff_val]
      rw [hg_val] at h₁_gt
      rw [hval_eq] at h₁_gt
      -- h₁_gt now says -D.coeff p > -D.coeff p, contradiction
      exact lt_irrefl _ h₁_gt
    have hneg₂_val : C.valuation p (-(g - algebraMap ℂ C.FunctionField c₂ * f₀)) =
                     C.valuation p (g - algebraMap ℂ C.FunctionField c₂ * f₀) := by
      have h : -(g - algebraMap ℂ C.FunctionField c₂ * f₀) =
               algebraMap ℂ C.FunctionField (-1 : ℂ) * (g - algebraMap ℂ C.FunctionField c₂ * f₀) := by
        simp only [map_neg, map_one, neg_mul, one_mul]
      have hm1_ne : algebraMap ℂ C.FunctionField (-1 : ℂ) ≠ 0 := by simp
      rw [h, C.toAlgebraicCurve.valuation_mul p _ _ hm1_ne h₂_sub_ne,
          C.algebraInst.valuation_algebraMap p (-1) (by norm_num : (-1 : ℂ) ≠ 0), zero_add]
    -- Apply ultrametric: v(a + b) ≥ min(v(a), v(b)) when a + b ≠ 0
    have hmin := C.toAlgebraicCurve.valuation_add_min p
      (g - algebraMap ℂ C.FunctionField c₁ * f₀)
      (-(g - algebraMap ℂ C.FunctionField c₂ * f₀)) hsum_ne
    rw [hsum_identity, hdiff_val, hneg₂_val] at hmin
    rw [hg_val] at h₁_gt h₂_gt
    -- hmin: -D(p) ≥ min(v(g-c₁f₀), v(g-c₂f₀))
    -- h₁_gt: v(g-c₁f₀) > -D(p)
    -- h₂_gt: v(g-c₂f₀) > -D(p)
    -- If both v₁ > x and v₂ > x, then min(v₁, v₂) > x
    have hmin_gt : min (C.valuation p (g - algebraMap ℂ C.FunctionField c₁ * f₀))
                       (C.valuation p (g - algebraMap ℂ C.FunctionField c₂ * f₀)) > -D.coeff p := by
      simp only [lt_min_iff]
      exact ⟨h₁_gt, h₂_gt⟩
    -- But hmin says -D(p) ≥ min(...), i.e., min(...) ≤ -D(p)
    -- This contradicts min(...) > -D(p)
    exact not_lt.mpr hmin hmin_gt

/-!
## Basic Maps for the Exact Sequence

The 5-term exact sequence in cohomology is:
  0 → L(D-p) → L(D) → ℂ → Dual(L(K-D+p)) → Dual(L(K-D)) → 0

where we use Serre duality H¹(E) = L(K-E)* (definitionally in this codebase).
-/

/-- The inclusion map L(D-p) → L(D) as a linear map (f₁) -/
noncomputable def inclusionMap :
    RiemannRochSubmodule C (D - point p) →ₗ[ℂ] RiemannRochSubmodule C D :=
  Submodule.inclusion (RiemannRochSubmodule_sub_point_le C D p)

/-- The inclusion map is injective -/
theorem inclusionMap_injective :
    Function.Injective (inclusionMap C D p) :=
  Submodule.inclusion_injective _

/-!
## Helper Equalities for Divisor Arithmetic
-/

/-- Helper: K - D + point p = K - (D - point p) -/
theorem canonical_minus_sub (C : CompactAlgebraicCurve)
    (K : CanonicalDivisor C) (D : Core.Divisor C.toAlgebraicCurve)
    (p : C.toAlgebraicCurve.Point) :
    K.K - D + point p = K.K - (D - point p) := by
  ext q
  simp only [add_coeff, sub_coeff, point]
  ring

/-- Helper: K - (D - p) - p = K - D -/
theorem canonical_sub_sub_point (C : CompactAlgebraicCurve)
    (K : CanonicalDivisor C) (D : Core.Divisor C.toAlgebraicCurve)
    (p : C.toAlgebraicCurve.Point) :
    K.K - (D - point p) - point p = K.K - D := by
  ext q
  simp only [sub_coeff, point]
  ring

/-!
## Quotient Dimension Bounds

The quotient dimensions a = h⁰(D) - h⁰(D-p) and b = h⁰(K-D+p) - h⁰(K-D)
satisfy a, b ∈ {0, 1} (by `quotient_dim_le_one`).
-/

/-- The quotient dimension h⁰(D) - h⁰(D-p) is bounded by 1 -/
theorem quotient_a_le_one
    [RiemannRochSubmoduleFiniteDimensional C (D - point p)]
    [RiemannRochSubmoduleFiniteDimensional C D] :
    h0 C D ≤ h0 C (D - point p) + 1 := by
  exact quotient_dim_le_one C D p

/-- The quotient dimension h⁰(K-D+p) - h⁰(K-D) is bounded by 1 -/
theorem quotient_b_le_one
    [RiemannRochSubmoduleFiniteDimensional C (K.K - D + point p)]
    [RiemannRochSubmoduleFiniteDimensional C (K.K - D)] :
    h0 C (K.K - D + point p) ≤ h0 C (K.K - D) + 1 := by
  have heq1 : K.K - D + point p = K.K - (D - point p) := canonical_minus_sub C K D p
  have heq2 : K.K - (D - point p) - point p = K.K - D := canonical_sub_sub_point C K D p
  haveI inst1 : RiemannRochSubmoduleFiniteDimensional C (K.K - (D - point p)) := by
    rw [← heq1]; infer_instance
  haveI inst2 : RiemannRochSubmoduleFiniteDimensional C (K.K - (D - point p) - point p) := by
    rw [heq2]; infer_instance
  rw [heq1]
  have h := quotient_dim_le_one C (K.K - (D - point p)) p
  rw [heq2] at h
  exact h

/-!
## The 5-Term Exact Sequence

We construct the 5-term exact sequence using dual spaces for H¹.
By Serre duality (which is definitional in this codebase):
- H¹(D-p) is represented by L(K-D+p)*
- H¹(D) is represented by L(K-D)*

The sequence is:
  0 → L(D-p) →^{f₁} L(D) →^{f₂} ℂ →^{f₃} L(K-D+p)* →^{f₄} L(K-D)* → 0
-/

/-- f₁: The inclusion L(D-p) → L(D) -/
noncomputable def f₁ :
    RiemannRochSubmodule C (D - point p) →ₗ[ℂ] RiemannRochSubmodule C D :=
  inclusionMap C D p

/-- f₁ is injective -/
theorem f₁_injective : Function.Injective (f₁ C D p) :=
  inclusionMap_injective C D p

set_option maxHeartbeats 800000 in
/-- f₂: The coefficient extraction map L(D) → ℂ.

    This extracts the leading coefficient at p. The kernel is exactly L(D-p).
    This is the key map in the short exact sequence 0 → L(D-p) → L(D) → ℂ.

    **Construction**: For f ∈ L(D) with v_p(f) = -D(p), this returns the
    leading coefficient. For f ∈ L(D-p) (i.e., v_p(f) > -D(p)), this returns 0.

    The linearity follows from the uniqueness property in
    `leadingCoefficientUniquenessGeneral`. -/
noncomputable def f₂ (C : CompactAlgebraicCurve) (D : Core.Divisor C.toAlgebraicCurve)
    (p : C.toAlgebraicCurve.Point) :
    RiemannRochSubmodule C D →ₗ[ℂ] ℂ := by
  -- The coefficient extraction map is well-defined and linear by the
  -- leading coefficient uniqueness theorem. The construction is:
  -- 1. If L(D) = L(D-p), then f₂ = 0
  -- 2. Otherwise, pick f₀ ∈ L(D) \ L(D-p), and for g ∈ L(D):
  --    - If g ∈ L(D-p), return 0
  --    - Otherwise, return the unique c such that g - c*f₀ ∈ L(D-p)
  let LDp := RiemannRochSubmodule C (D - point p)
  let LD := RiemannRochSubmodule C D
  -- Check if L(D) = L(D-p) (quotient is trivial)
  by_cases hEq : ∀ f ∈ LD, f ∈ LDp
  · -- Case 1: L(D) = L(D-p), return the zero map
    exact 0
  · -- Case 2: There exists f₀ ∈ L(D) \ L(D-p)
    push_neg at hEq
    -- Choose such an f₀
    have hex : ∃ f₀ : LD, f₀.val ∉ LDp := by
      obtain ⟨f, hfD, hfnot⟩ := hEq
      exact ⟨⟨f, hfD⟩, hfnot⟩
    let f₀ := Classical.choose hex
    have hf₀_not : f₀.val ∉ LDp := Classical.choose_spec hex
    -- f₀ is nonzero (since 0 ∈ L(D-p))
    have hf₀_ne : f₀.val ≠ 0 := by
      intro heq
      apply hf₀_not
      rw [heq]
      exact zero_mem_RiemannRochSpace C.toAlgebraicCurve (D - point p)
    -- f₀ has exact valuation -D(p) at p (using helper lemma)
    have hf₀_val : C.valuation p f₀.val = -D.coeff p :=
      valuation_eq_neg_coeff_of_in_D_not_in_Dp C D p f₀.val f₀.property hf₀_not
    -- Define the coefficient extraction using f₀
    -- For g ∈ L(D), return the unique c such that g - c*f₀ ∈ L(D-p) (or is zero)
    exact {
      toFun := fun g =>
        if hg_mem : g.val ∈ LDp then 0
        else
          -- g ∉ L(D-p), so g has valuation -D(p) at p (same as f₀)
          -- By leadingCoefficientUniquenessGeneral, there exists c such that
          -- g - c*f₀ has higher valuation (or is zero)
          have hg_ne : g.val ≠ 0 := by
            intro heq; apply hg_mem; rw [heq]
            exact zero_mem_RiemannRochSpace C.toAlgebraicCurve (D - point p)
          have hg_val : C.valuation p g.val = -D.coeff p :=
            valuation_eq_neg_coeff_of_in_D_not_in_Dp C D p g.val g.property hg_mem
          have heq_val : C.valuation p f₀.val = C.valuation p g.val := by
            rw [hf₀_val, hg_val]
          (C.leadingCoefficientUniquenessGeneral p f₀.val g.val hf₀_ne hg_ne heq_val).choose
      map_add' := by
        intro g₁ g₂
        simp only
        -- Case split on membership in L(D-p)
        by_cases hg₁ : g₁.val ∈ LDp <;> by_cases hg₂ : g₂.val ∈ LDp
        · -- Both in L(D-p): g₁ + g₂ ∈ L(D-p)
          simp only [hg₁, hg₂, dif_pos, add_zero]
          have hsum : (g₁ + g₂).val ∈ LDp := LDp.add_mem hg₁ hg₂
          simp only [hsum, dif_pos]
        · -- g₁ ∈ L(D-p), g₂ ∉ L(D-p)
          simp only [hg₁, hg₂, dif_pos, dif_neg, not_false_eq_true, zero_add]
          by_cases hsum : (g₁ + g₂).val ∈ LDp
          · -- g₁ + g₂ ∈ L(D-p) would mean g₂ ∈ L(D-p) (contradiction)
            exfalso; apply hg₂
            have h1 : g₁.val ∈ LDp := hg₁
            have h2 : (g₁ + g₂).val ∈ LDp := hsum
            have h3 : (g₁ + g₂).val - g₁.val ∈ LDp := LDp.sub_mem h2 h1
            simp only [Submodule.coe_add, add_sub_cancel_left] at h3
            exact h3
          · simp only [hsum, dif_neg, not_false_eq_true]
            -- Need to show: c(g₂) = c(g₁+g₂)
            -- Case: g₁ = 0 => g₁ + g₂ = g₂, coefficients trivially equal
            by_cases hg₁_zero : g₁.val = 0
            · -- g₁ = 0, so g₁ + g₂ = g₂
              have hsum_eq : (g₁ + g₂).val = g₂.val := by
                simp only [Submodule.coe_add, hg₁_zero, zero_add]
              -- The coefficients should be definitionally equal after simplification
              congr 1
              ext q
              simp only [hsum_eq]
            · -- g₁ ≠ 0, so we can use valuation_gt_of_mem_sub_point
              have hg₁_higher : C.valuation p g₁.val > -D.coeff p :=
                valuation_gt_of_mem_sub_point C D p g₁.val hg₁_zero hg₁
              -- The unique c for g₂ also works for g₁+g₂
              -- because g₁ has higher valuation, adding it doesn't change leading coefficient
              have hg₂_ne : g₂.val ≠ 0 := by
                intro heq; apply hg₂; rw [heq]
                exact zero_mem_RiemannRochSpace C.toAlgebraicCurve _
              have hg₂_val : C.valuation p g₂.val = -D.coeff p :=
                valuation_eq_neg_coeff_of_in_D_not_in_Dp C D p g₂.val g₂.property hg₂
              have heq_coe : (g₁ + g₂).val = g₁.val + g₂.val := Submodule.coe_add g₁ g₂
              have hsum_ne : (g₁ + g₂).val ≠ 0 := by
                intro heq
                apply hsum
                rw [heq]
                exact zero_mem_RiemannRochSpace C.toAlgebraicCurve _
              have hsum_val : C.valuation p (g₁ + g₂).val = -D.coeff p := by
                rw [heq_coe]
                exact valuation_eq_neg_coeff_of_in_D_not_in_Dp C D p (g₁.val + g₂.val)
                  (heq_coe ▸ (g₁ + g₂).property)
                  (heq_coe ▸ hsum)
              -- Version of hsum_val in terms of g₁.val + g₂.val
              have hsum_val' : C.valuation p (g₁.val + g₂.val) = -D.coeff p := by
                rw [← heq_coe]; exact hsum_val
              -- The coefficient for g₂ satisfies the higher valuation property for g₁+g₂
              -- We avoid `let` bindings due to definitional equality issues with `choose`
              have hc_spec := (C.leadingCoefficientUniquenessGeneral p f₀.val g₂.val hf₀_ne hg₂_ne
                              (by rw [hf₀_val, hg₂_val])).choose_spec
              have hc_sum_spec := (C.leadingCoefficientUniquenessGeneral p f₀.val (g₁ + g₂).val hf₀_ne hsum_ne
                                  (by rw [hf₀_val, hsum_val])).choose_spec
              obtain ⟨hc_ne, hc_cases⟩ := hc_spec
              obtain ⟨hc_sum_ne, hc_sum_cases⟩ := hc_sum_spec
              -- Define c and c_sum as abbreviations for the choose expressions
              set c := (C.leadingCoefficientUniquenessGeneral p f₀.val g₂.val hf₀_ne hg₂_ne
                       (by rw [hf₀_val, hg₂_val])).choose with hc_def
              set c_sum := (C.leadingCoefficientUniquenessGeneral p f₀.val (g₁ + g₂).val hf₀_ne hsum_ne
                           (by rw [hf₀_val, hsum_val])).choose with hc_sum_def
              -- c also satisfies the property for g₁+g₂ because g₁ has higher valuation
              have hc_for_sum : (g₁ + g₂).val - algebraMap ℂ C.FunctionField c * f₀.val = 0 ∨
                  C.valuation p ((g₁ + g₂).val - algebraMap ℂ C.FunctionField c * f₀.val) >
                  C.valuation p (g₁ + g₂).val := by
                simp only [Submodule.coe_add]
                -- (g₁ + g₂) - c*f₀ = g₁ + (g₂ - c*f₀)
                have hrewrite : g₁.val + g₂.val - algebraMap ℂ C.FunctionField c * f₀.val =
                                g₁.val + (g₂.val - algebraMap ℂ C.FunctionField c * f₀.val) := by ring
                rw [hrewrite, hsum_val']
                rcases hc_cases with h_eq | h_gt
                · -- g₂ - c*f₀ = 0, so sum = g₁
                  rw [h_eq, add_zero]
                  right
                  exact hg₁_higher
                · -- v(g₂ - c*f₀) > v(g₂) = -D(p)
                  -- By ultrametric: v(g₁ + (g₂ - c*f₀)) ≥ min(v(g₁), v(g₂-cf₀)) > -D(p)
                  -- unless the sum is 0
                  by_cases hsum_zero : g₁.val + (g₂.val - algebraMap ℂ C.FunctionField c * f₀.val) = 0
                  · left; exact hsum_zero
                  · right
                    have hg₂_cf₀_val : C.valuation p (g₂.val - algebraMap ℂ C.FunctionField c * f₀.val) > -D.coeff p :=
                      hg₂_val ▸ h_gt
                    have hmin := C.toAlgebraicCurve.valuation_add_min p g₁.val
                      (g₂.val - algebraMap ℂ C.FunctionField c * f₀.val) hsum_zero
                    have hmin_gt : min (C.valuation p g₁.val)
                                       (C.valuation p (g₂.val - algebraMap ℂ C.FunctionField c * f₀.val)) > -D.coeff p := by
                      simp only [lt_min_iff]
                      exact ⟨hg₁_higher, hg₂_cf₀_val⟩
                    omega
              -- By coeff_unique, c = c_sum; goal is c_sum = c, so use .symm
              exact (coeff_unique C D p f₀.val (g₁ + g₂).val hf₀_ne hf₀_val
                hsum_val c c_sum hc_ne hc_sum_ne hc_for_sum hc_sum_cases).symm
        · -- g₁ ∉ L(D-p), g₂ ∈ L(D-p)
          simp only [hg₁, hg₂, dif_pos, dif_neg, not_false_eq_true, add_zero]
          by_cases hsum : (g₁ + g₂).val ∈ LDp
          · -- g₁ + g₂ ∈ L(D-p) would mean g₁ ∈ L(D-p) (contradiction)
            exfalso; apply hg₁
            have h2 : (g₁ + g₂).val ∈ LDp := hsum
            have h3 : g₂.val ∈ LDp := hg₂
            have h4 : (g₁ + g₂).val - g₂.val ∈ LDp := LDp.sub_mem h2 h3
            simp only [Submodule.coe_add, add_sub_cancel_right] at h4
            exact h4
          · simp only [hsum, dif_neg, not_false_eq_true]
            -- Need to show: c(g₁) = c(g₁+g₂)
            -- Case: g₂ = 0 => g₁ + g₂ = g₁, coefficients trivially equal
            by_cases hg₂_zero : g₂.val = 0
            · -- g₂ = 0, so g₁ + g₂ = g₁
              have hsum_eq : (g₁ + g₂).val = g₁.val := by
                simp only [Submodule.coe_add, hg₂_zero, add_zero]
              congr 1
              ext q
              simp only [hsum_eq]
            · -- g₂ ≠ 0, so we can use valuation_gt_of_mem_sub_point
              have hg₂_higher : C.valuation p g₂.val > -D.coeff p :=
                valuation_gt_of_mem_sub_point C D p g₂.val hg₂_zero hg₂
              have hg₁_ne : g₁.val ≠ 0 := by
                intro heq; apply hg₁; rw [heq]
                exact zero_mem_RiemannRochSpace C.toAlgebraicCurve _
              have hg₁_val : C.valuation p g₁.val = -D.coeff p :=
                valuation_eq_neg_coeff_of_in_D_not_in_Dp C D p g₁.val g₁.property hg₁
              have heq_coe' : (g₁ + g₂).val = g₁.val + g₂.val := Submodule.coe_add g₁ g₂
              have hsum_ne : (g₁ + g₂).val ≠ 0 := by
                intro heq
                apply hsum
                rw [heq]
                exact zero_mem_RiemannRochSpace C.toAlgebraicCurve _
              have hsum_val : C.valuation p (g₁ + g₂).val = -D.coeff p := by
                rw [heq_coe']
                exact valuation_eq_neg_coeff_of_in_D_not_in_Dp C D p (g₁.val + g₂.val)
                  (heq_coe' ▸ (g₁ + g₂).property)
                  (heq_coe' ▸ hsum)
              -- Version of hsum_val in terms of g₁.val + g₂.val
              have hsum_val' : C.valuation p (g₁.val + g₂.val) = -D.coeff p := by
                rw [← heq_coe']; exact hsum_val
              -- We avoid `let` bindings due to definitional equality issues with `choose`
              have hc_spec := (C.leadingCoefficientUniquenessGeneral p f₀.val g₁.val hf₀_ne hg₁_ne
                              (by rw [hf₀_val, hg₁_val])).choose_spec
              have hc_sum_spec := (C.leadingCoefficientUniquenessGeneral p f₀.val (g₁ + g₂).val hf₀_ne hsum_ne
                                  (by rw [hf₀_val, hsum_val])).choose_spec
              obtain ⟨hc_ne, hc_cases⟩ := hc_spec
              obtain ⟨hc_sum_ne, hc_sum_cases⟩ := hc_sum_spec
              -- Define c and c_sum as abbreviations for the choose expressions
              set c := (C.leadingCoefficientUniquenessGeneral p f₀.val g₁.val hf₀_ne hg₁_ne
                       (by rw [hf₀_val, hg₁_val])).choose with hc_def
              set c_sum := (C.leadingCoefficientUniquenessGeneral p f₀.val (g₁ + g₂).val hf₀_ne hsum_ne
                           (by rw [hf₀_val, hsum_val])).choose with hc_sum_def
              -- c also satisfies the property for g₁+g₂ because g₂ has higher valuation
              have hc_for_sum : (g₁ + g₂).val - algebraMap ℂ C.FunctionField c * f₀.val = 0 ∨
                  C.valuation p ((g₁ + g₂).val - algebraMap ℂ C.FunctionField c * f₀.val) >
                  C.valuation p (g₁ + g₂).val := by
                rw [heq_coe']
                -- (g₁ + g₂) - c*f₀ = (g₁ - c*f₀) + g₂
                have hrewrite : g₁.val + g₂.val - algebraMap ℂ C.FunctionField c * f₀.val =
                                (g₁.val - algebraMap ℂ C.FunctionField c * f₀.val) + g₂.val := by ring
                rw [hrewrite, hsum_val']
                rcases hc_cases with h_eq | h_gt
                · -- g₁ - c*f₀ = 0, so sum = g₂
                  rw [h_eq, zero_add]
                  right
                  exact hg₂_higher
                · -- v(g₁ - c*f₀) > v(g₁) = -D(p)
                  by_cases hsum_zero : (g₁.val - algebraMap ℂ C.FunctionField c * f₀.val) + g₂.val = 0
                  · left; exact hsum_zero
                  · right
                    have hg₁_cf₀_val : C.valuation p (g₁.val - algebraMap ℂ C.FunctionField c * f₀.val) > -D.coeff p :=
                      hg₁_val ▸ h_gt
                    have hmin := C.toAlgebraicCurve.valuation_add_min p
                      (g₁.val - algebraMap ℂ C.FunctionField c * f₀.val) g₂.val hsum_zero
                    have hmin_gt : min (C.valuation p (g₁.val - algebraMap ℂ C.FunctionField c * f₀.val))
                                       (C.valuation p g₂.val) > -D.coeff p := by
                      simp only [lt_min_iff]
                      exact ⟨hg₁_cf₀_val, hg₂_higher⟩
                    omega
              -- By coeff_unique, c = c_sum; goal is c_sum = c, so use .symm
              exact (coeff_unique C D p f₀.val (g₁ + g₂).val hf₀_ne hf₀_val
                hsum_val c c_sum hc_ne hc_sum_ne hc_for_sum hc_sum_cases).symm
        · -- Neither in L(D-p)
          simp only [hg₁, hg₂, dif_neg, not_false_eq_true]
          by_cases hsum : (g₁ + g₂).val ∈ LDp
          · -- g₁ + g₂ ∈ L(D-p): c(g₁) + c(g₂) = 0
            simp only [hsum, dif_pos]
            -- g₁ - c₁*f₀ ∈ L(D-p) and g₂ - c₂*f₀ ∈ L(D-p)
            -- So (g₁+g₂) - (c₁+c₂)*f₀ ∈ L(D-p)
            -- But g₁+g₂ ∈ L(D-p), so (c₁+c₂)*f₀ ∈ L(D-p)
            -- Since f₀ ∉ L(D-p), must have c₁+c₂ = 0
            have hg₁_ne : g₁.val ≠ 0 := by
              intro heq; apply hg₁; rw [heq]
              exact zero_mem_RiemannRochSpace C.toAlgebraicCurve _
            have hg₂_ne : g₂.val ≠ 0 := by
              intro heq; apply hg₂; rw [heq]
              exact zero_mem_RiemannRochSpace C.toAlgebraicCurve _
            have hg₁_val : C.valuation p g₁.val = -D.coeff p :=
              valuation_eq_neg_coeff_of_in_D_not_in_Dp C D p g₁.val g₁.property hg₁
            have hg₂_val : C.valuation p g₂.val = -D.coeff p :=
              valuation_eq_neg_coeff_of_in_D_not_in_Dp C D p g₂.val g₂.property hg₂
            let c₁ := (C.leadingCoefficientUniquenessGeneral p f₀.val g₁.val hf₀_ne hg₁_ne
                      (by rw [hf₀_val, hg₁_val])).choose
            let c₂ := (C.leadingCoefficientUniquenessGeneral p f₀.val g₂.val hf₀_ne hg₂_ne
                      (by rw [hf₀_val, hg₂_val])).choose
            have hc₁_spec := (C.leadingCoefficientUniquenessGeneral p f₀.val g₁.val hf₀_ne hg₁_ne
                             (by rw [hf₀_val, hg₁_val])).choose_spec
            have hc₂_spec := (C.leadingCoefficientUniquenessGeneral p f₀.val g₂.val hf₀_ne hg₂_ne
                             (by rw [hf₀_val, hg₂_val])).choose_spec
            -- The key: c₁ + c₂ = 0 when g₁ + g₂ ∈ L(D-p)
            -- Proof: g₁ - c₁f₀ and g₂ - c₂f₀ have higher valuation or are zero
            -- So (g₁+g₂) - (c₁+c₂)f₀ has higher valuation at p (or is zero)
            -- But g₁+g₂ ∈ L(D-p) means (g₁+g₂) has valuation ≥ -(D(p)-1) > -D(p)
            -- For (c₁+c₂)f₀ to also have higher valuation, need c₁+c₂ = 0
            by_contra hne
            push_neg at hne
            have hne' : c₁ + c₂ ≠ 0 := hne.symm
            -- Destructure hc₁_spec and hc₂_spec so they're available for all branches
            obtain ⟨hc₁_ne, hc₁_cases⟩ := hc₁_spec
            obtain ⟨hc₂_ne, hc₂_cases⟩ := hc₂_spec
            -- (c₁+c₂)f₀ has valuation -D(p) since c₁+c₂ ≠ 0 and f₀ has valuation -D(p)
            have hcf₀_val : C.valuation p (algebraMap ℂ C.FunctionField (c₁ + c₂) * f₀.val) =
                            -D.coeff p := by
              have halg_ne : algebraMap ℂ C.FunctionField (c₁ + c₂) ≠ 0 := by
                simp only [map_ne_zero]; exact hne'
              rw [C.toAlgebraicCurve.valuation_mul p _ _ halg_ne hf₀_ne,
                  C.algebraInst.valuation_algebraMap p (c₁ + c₂) hne', zero_add, hf₀_val]
            -- g₁+g₂ has valuation > -D(p) since it's in L(D-p)
            have hsum_val : C.valuation p (g₁.val + g₂.val) > -D.coeff p := by
              have h := hsum
              simp only [Submodule.coe_add, LDp] at h
              simp only [RiemannRochSubmodule, RiemannRochSpace, Submodule.mem_mk,
                         AddSubmonoid.mem_mk] at h
              rcases h with heq | hval
              · -- g₁ + g₂ = 0, valuation is 0 > -D(p) (if D(p) > 0)
                -- Actually need to be careful here
                by_cases hDp : D.coeff p > 0
                · simp only [heq, C.toAlgebraicCurve.valuation_zero]; omega
                · -- D(p) ≤ 0, but both g₁, g₂ have valuation -D(p) at p
                  -- This is a contradiction since g₁+g₂=0 but g₁,g₂ nonzero with same val
                  exfalso
                  -- g₁ = -g₂, both have valuation -D(p) ≤ 0
                  -- By ultrametric, if g₁ + g₂ = 0, then g₁ = -g₂
                  -- v(-g₂) = v(g₂) = -D(p), v(g₁) = -D(p)
                  -- g₁ - c₁f₀ has higher valuation means g₁ = c₁f₀ or diff has higher val
                  -- Similar for g₂
                  -- But g₁ + g₂ = 0 means c₁f₀ + c₂f₀ ≈ 0, i.e., (c₁+c₂)f₀ ≈ 0
                  -- Since f₀ ≠ 0, need c₁ + c₂ = 0
                  exact hne' (by
                    -- Need to show c₁ + c₂ = 0
                    -- g₁ + g₂ = 0 implies g₁ = -g₂
                    have heq' : g₁.val = -g₂.val := add_eq_zero_iff_eq_neg.mp heq
                    -- From the uniqueness property:
                    -- g₁ - c₁*f₀ has higher valuation at p, so either g₁ = c₁*f₀ or v(g₁-c₁f₀) > -D(p)
                    -- Similarly g₂ - c₂*f₀ has higher valuation
                    -- g₁ = -g₂ means c₁*f₀ ≈ -c₂*f₀ (both in L(D-p) or diff in L(D-p))
                    -- This gives (c₁+c₂)*f₀ ∈ L(D-p), but f₀ ∉ L(D-p) so c₁+c₂=0
                    -- (hc₁_ne, hc₁_cases, hc₂_ne, hc₂_cases already defined above)
                    -- The key insight: g₁ = -g₂, so -c₁ satisfies the same property for g₂
                    -- g₁ - c₁*f₀ has higher valuation implies
                    -- g₂ - (-c₁)*f₀ = -g₁ + c₁*f₀ = -(g₁ - c₁*f₀) has same valuation
                    -- By coeff_unique, -c₁ = c₂, hence c₁ + c₂ = 0
                    -- Convert heq' : g₁.val = -g₂.val to a sum form
                    have heq_sum : g₁.val + g₂.val = 0 := by rw [heq']; ring
                    have hneg_c₁_property : g₂.val - algebraMap ℂ C.FunctionField (-c₁) * f₀.val = 0 ∨
                        C.valuation p (g₂.val - algebraMap ℂ C.FunctionField (-c₁) * f₀.val) >
                        C.valuation p g₂.val := by
                      have heq'' : g₂.val - algebraMap ℂ C.FunctionField (-c₁) * f₀.val =
                                   -(g₁.val - algebraMap ℂ C.FunctionField c₁ * f₀.val) := by
                        simp only [map_neg, neg_mul]
                        have hg₂_eq : g₂.val = -g₁.val := by rw [heq']; ring
                        rw [hg₂_eq]; ring
                      rcases hc₁_cases with h1_eq | h1_gt
                      · left; rw [heq'', h1_eq, neg_zero]
                      · right
                        rw [heq'']
                        have hmul_neg : -(g₁.val - algebraMap ℂ C.FunctionField c₁ * f₀.val) ≠ 0 := by
                          intro hzero
                          have : g₁.val - algebraMap ℂ C.FunctionField c₁ * f₀.val = 0 := neg_eq_zero.mp hzero
                          rw [this] at h1_gt
                          simp only [C.toAlgebraicCurve.valuation_zero] at h1_gt
                          rw [hg₁_val] at h1_gt; omega
                        have hneg_val' : C.valuation p (-(g₁.val - algebraMap ℂ C.FunctionField c₁ * f₀.val)) =
                                         C.valuation p (g₁.val - algebraMap ℂ C.FunctionField c₁ * f₀.val) := by
                          have hneg_is_m1 : -(g₁.val - algebraMap ℂ C.FunctionField c₁ * f₀.val) =
                                            algebraMap ℂ C.FunctionField (-1 : ℂ) *
                                            (g₁.val - algebraMap ℂ C.FunctionField c₁ * f₀.val) := by
                            simp only [map_neg, map_one, neg_mul, one_mul]
                          have hm1_ne : algebraMap ℂ C.FunctionField (-1 : ℂ) ≠ 0 := by simp
                          have hdiff_ne : g₁.val - algebraMap ℂ C.FunctionField c₁ * f₀.val ≠ 0 := by
                            intro hzero; rw [hzero] at h1_gt
                            simp only [C.toAlgebraicCurve.valuation_zero] at h1_gt
                            rw [hg₁_val] at h1_gt; omega
                          rw [hneg_is_m1, C.toAlgebraicCurve.valuation_mul p _ _ hm1_ne hdiff_ne,
                              C.algebraInst.valuation_algebraMap p (-1) (by norm_num : (-1 : ℂ) ≠ 0), zero_add]
                        rw [hneg_val']
                        have hg₁_g₂_val : C.valuation p g₂.val = C.valuation p g₁.val := by
                          rw [hg₁_val, hg₂_val]
                        rw [hg₁_g₂_val]; exact h1_gt
                    -- Now apply coeff_unique: both c₂ and -c₁ work for g₂, so c₂ = -c₁
                    have hneg_c₁_ne : -c₁ ≠ 0 := neg_ne_zero.mpr hc₁_ne
                    have hc₂_eq_neg_c₁ := coeff_unique C D p f₀.val g₂.val hf₀_ne hf₀_val hg₂_val
                      c₂ (-c₁) hc₂_ne hneg_c₁_ne hc₂_cases hneg_c₁_property
                    -- c₂ = -c₁ means c₁ + c₂ = c₁ + (-c₁) = 0
                    simp only [hc₂_eq_neg_c₁, add_neg_cancel])
              · specialize hval p
                simp only [Core.Divisor.sub_coeff, point, if_true] at hval
                omega
            -- This is a contradiction: we have (g₁+g₂) - (c₁+c₂)f₀ should have
            -- valuation > -D(p), but g₁+g₂ has val > -D(p) and (c₁+c₂)f₀ has val = -D(p)
            -- By ultrametric: v((g₁+g₂) - (c₁+c₂)f₀) ≥ min(v(g₁+g₂), v((c₁+c₂)f₀)) = -D(p)
            -- But we need strict inequality, which fails
            -- Actually this isn't a direct contradiction...
            -- The real argument: g₁-c₁f₀ and g₂-c₂f₀ are both in L(D-p) (or zero)
            -- So their sum (g₁+g₂)-(c₁+c₂)f₀ is in L(D-p)
            -- Since g₁+g₂ is in L(D-p), (c₁+c₂)f₀ must be in L(D-p)
            -- But f₀ ∉ L(D-p) and c₁+c₂ ≠ 0 means (c₁+c₂)f₀ ∉ L(D-p)
            have hdiff₁ : g₁.val - algebraMap ℂ C.FunctionField c₁ * f₀.val ∈ LDp ∨
                          g₁.val - algebraMap ℂ C.FunctionField c₁ * f₀.val = 0 := by
              rcases hc₁_cases with heq' | hgt
              · right; exact heq'
              · left
                simp only [RiemannRochSubmodule, RiemannRochSpace, Submodule.mem_mk,
                           AddSubmonoid.mem_mk, LDp]
                by_cases hdiff_zero : g₁.val - algebraMap ℂ C.FunctionField c₁ * f₀.val = 0
                · left; exact hdiff_zero
                · right; intro q
                  simp only [Core.Divisor.sub_coeff, point]
                  by_cases hqp : q = p
                  · simp only [hqp, if_true]
                    have hgt' : C.valuation p (g₁.val - algebraMap ℂ C.FunctionField c₁ * f₀.val) > -D.coeff p :=
                      hg₁_val ▸ hgt
                    omega
                  · -- q ≠ p case: simplify (if q = p then 1 else 0) to 0
                    rw [if_neg hqp]
                    simp only [sub_zero]
                    -- Need v_q(g₁ - c₁f₀) ≥ -D(q)
                    -- Both g₁ and f₀ are in L(D), so v_q ≥ -D(q)
                    have hg₁_q : C.valuation q g₁.val + D.coeff q ≥ 0 := by
                      have hg₁_D : g₁.val ∈ RiemannRochSpace C.toAlgebraicCurve D := g₁.property
                      simp only [RiemannRochSpace, Set.mem_setOf_eq] at hg₁_D
                      rcases hg₁_D with heq | hg₁_D'
                      · exact absurd heq hg₁_ne
                      · exact hg₁_D' q
                    have hf₀_q : C.valuation q f₀.val + D.coeff q ≥ 0 := by
                      have hf₀_D : f₀.val ∈ RiemannRochSpace C.toAlgebraicCurve D := f₀.property
                      simp only [RiemannRochSpace, Set.mem_setOf_eq] at hf₀_D
                      rcases hf₀_D with heq | hf₀_D'
                      · exact absurd heq hf₀_ne
                      · exact hf₀_D' q
                    have hcf₀_q : C.valuation q (algebraMap ℂ C.FunctionField c₁ * f₀.val) + D.coeff q ≥ 0 := by
                      by_cases hc₁_zero : c₁ = 0
                      · exact absurd hc₁_zero hc₁_ne
                      · have halg_ne : algebraMap ℂ C.FunctionField c₁ ≠ 0 := by simp [hc₁_zero]
                        rw [C.toAlgebraicCurve.valuation_mul q _ _ halg_ne hf₀_ne,
                            C.algebraInst.valuation_algebraMap q c₁ hc₁_zero, zero_add]
                        exact hf₀_q
                    by_cases hdiff' : g₁.val + (-(algebraMap ℂ C.FunctionField c₁ * f₀.val)) = 0
                    · exfalso; exact hdiff_zero (by simp only [_root_.sub_eq_add_neg]; exact hdiff')
                    have hmin := C.toAlgebraicCurve.valuation_add_min q g₁.val
                      (-(algebraMap ℂ C.FunctionField c₁ * f₀.val)) hdiff'
                    have hneg_val : C.valuation q (-(algebraMap ℂ C.FunctionField c₁ * f₀.val)) =
                                    C.valuation q (algebraMap ℂ C.FunctionField c₁ * f₀.val) := by
                      by_cases hcf₀_zero : algebraMap ℂ C.FunctionField c₁ * f₀.val = 0
                      · simp only [hcf₀_zero, neg_zero]
                      have h1 : -(algebraMap ℂ C.FunctionField c₁ * f₀.val) =
                                algebraMap ℂ C.FunctionField (-1 : ℂ) * (algebraMap ℂ C.FunctionField c₁ * f₀.val) := by
                        simp only [map_neg, map_one, neg_mul, one_mul]
                      have hm1_ne : algebraMap ℂ C.FunctionField (-1 : ℂ) ≠ 0 := by simp
                      rw [h1, C.toAlgebraicCurve.valuation_mul q _ _ hm1_ne hcf₀_zero,
                          C.algebraInst.valuation_algebraMap q (-1) (by norm_num : (-1 : ℂ) ≠ 0), zero_add]
                    simp only [_root_.sub_eq_add_neg]
                    rw [hneg_val] at hmin
                    omega
            have hdiff₂ : g₂.val - algebraMap ℂ C.FunctionField c₂ * f₀.val ∈ LDp ∨
                          g₂.val - algebraMap ℂ C.FunctionField c₂ * f₀.val = 0 := by
              rcases hc₂_cases with heq' | hgt
              · right; exact heq'
              · left
                simp only [RiemannRochSubmodule, RiemannRochSpace, Submodule.mem_mk,
                           AddSubmonoid.mem_mk, LDp]
                by_cases hdiff_zero : g₂.val - algebraMap ℂ C.FunctionField c₂ * f₀.val = 0
                · left; exact hdiff_zero
                · right; intro q
                  simp only [Core.Divisor.sub_coeff, point]
                  by_cases hqp : q = p
                  · simp only [hqp, if_true]
                    have hgt' : C.valuation p (g₂.val - algebraMap ℂ C.FunctionField c₂ * f₀.val) > -D.coeff p :=
                      hg₂_val ▸ hgt
                    omega
                  · -- q ≠ p case: simplify (if q = p then 1 else 0) to 0
                    rw [if_neg hqp]
                    simp only [sub_zero]
                    have hg₂_ne' : g₂.val ≠ 0 := hg₂_ne
                    have hg₂_q : C.valuation q g₂.val + D.coeff q ≥ 0 := by
                      have hg₂_D : g₂.val ∈ RiemannRochSpace C.toAlgebraicCurve D := g₂.property
                      simp only [RiemannRochSpace, Set.mem_setOf_eq] at hg₂_D
                      rcases hg₂_D with heq | hg₂_D'
                      · exact absurd heq hg₂_ne'
                      · exact hg₂_D' q
                    have hf₀_q : C.valuation q f₀.val + D.coeff q ≥ 0 := by
                      have hf₀_D : f₀.val ∈ RiemannRochSpace C.toAlgebraicCurve D := f₀.property
                      simp only [RiemannRochSpace, Set.mem_setOf_eq] at hf₀_D
                      rcases hf₀_D with heq | hf₀_D'
                      · exact absurd heq hf₀_ne
                      · exact hf₀_D' q
                    have hcf₀_q : C.valuation q (algebraMap ℂ C.FunctionField c₂ * f₀.val) + D.coeff q ≥ 0 := by
                      by_cases hc₂_zero : c₂ = 0
                      · exact absurd hc₂_zero hc₂_ne
                      · have halg_ne : algebraMap ℂ C.FunctionField c₂ ≠ 0 := by simp [hc₂_zero]
                        rw [C.toAlgebraicCurve.valuation_mul q _ _ halg_ne hf₀_ne,
                            C.algebraInst.valuation_algebraMap q c₂ hc₂_zero, zero_add]
                        exact hf₀_q
                    by_cases hdiff' : g₂.val + (-(algebraMap ℂ C.FunctionField c₂ * f₀.val)) = 0
                    · exfalso; exact hdiff_zero (by simp only [_root_.sub_eq_add_neg]; exact hdiff')
                    have hmin := C.toAlgebraicCurve.valuation_add_min q g₂.val
                      (-(algebraMap ℂ C.FunctionField c₂ * f₀.val)) hdiff'
                    have hneg_val : C.valuation q (-(algebraMap ℂ C.FunctionField c₂ * f₀.val)) =
                                    C.valuation q (algebraMap ℂ C.FunctionField c₂ * f₀.val) := by
                      by_cases hcf₀_zero : algebraMap ℂ C.FunctionField c₂ * f₀.val = 0
                      · simp only [hcf₀_zero, neg_zero]
                      have h1 : -(algebraMap ℂ C.FunctionField c₂ * f₀.val) =
                                algebraMap ℂ C.FunctionField (-1 : ℂ) * (algebraMap ℂ C.FunctionField c₂ * f₀.val) := by
                        simp only [map_neg, map_one, neg_mul, one_mul]
                      have hm1_ne : algebraMap ℂ C.FunctionField (-1 : ℂ) ≠ 0 := by simp
                      rw [h1, C.toAlgebraicCurve.valuation_mul q _ _ hm1_ne hcf₀_zero,
                          C.algebraInst.valuation_algebraMap q (-1) (by norm_num : (-1 : ℂ) ≠ 0), zero_add]
                    simp only [_root_.sub_eq_add_neg]
                    rw [hneg_val] at hmin
                    omega
            -- Now: (g₁ - c₁f₀) + (g₂ - c₂f₀) = (g₁+g₂) - (c₁+c₂)f₀ is in L(D-p)
            have hsum_diff : (g₁.val + g₂.val) - algebraMap ℂ C.FunctionField (c₁ + c₂) * f₀.val ∈ LDp := by
              rcases hdiff₁ with h1 | h1_eq <;> rcases hdiff₂ with h2 | h2_eq
              · -- Both differences in L(D-p)
                have h := LDp.add_mem h1 h2
                convert h using 1
                simp only [map_add]; ring
              · -- First in L(D-p), second is zero
                -- h2_eq says g₂ - c₂*f₀ = 0, so g₂ = c₂*f₀
                -- Goal: g₁ + g₂ - (c₁+c₂)*f₀ = g₁ - c₁*f₀ ∈ LDp (which is h1)
                have hg₂_eq : g₂.val = algebraMap ℂ C.FunctionField c₂ * f₀.val := sub_eq_zero.mp h2_eq
                convert h1 using 1
                rw [hg₂_eq, map_add]; ring
              · -- First is zero, second in L(D-p)
                -- h1_eq says g₁ - c₁*f₀ = 0, so g₁ = c₁*f₀
                -- Goal: g₁ + g₂ - (c₁+c₂)*f₀ = g₂ - c₂*f₀ ∈ LDp (which is h2)
                have hg₁_eq : g₁.val = algebraMap ℂ C.FunctionField c₁ * f₀.val := sub_eq_zero.mp h1_eq
                convert h2 using 1
                rw [hg₁_eq, map_add]; ring
              · -- Both are zero
                -- g₁ = c₁*f₀ and g₂ = c₂*f₀, so g₁ + g₂ - (c₁+c₂)*f₀ = 0 ∈ LDp
                have hg₁_eq : g₁.val = algebraMap ℂ C.FunctionField c₁ * f₀.val := sub_eq_zero.mp h1_eq
                have hg₂_eq : g₂.val = algebraMap ℂ C.FunctionField c₂ * f₀.val := sub_eq_zero.mp h2_eq
                have hzero : g₁.val + g₂.val - algebraMap ℂ C.FunctionField (c₁ + c₂) * f₀.val = 0 := by
                  rw [hg₁_eq, hg₂_eq, map_add]; ring
                rw [hzero]
                exact LDp.zero_mem
            -- g₁+g₂ ∈ L(D-p), so (c₁+c₂)f₀ = (g₁+g₂) - ((g₁+g₂) - (c₁+c₂)f₀) ∈ L(D-p)
            have hcf₀_mem : algebraMap ℂ C.FunctionField (c₁ + c₂) * f₀.val ∈ LDp := by
              have h := LDp.sub_mem hsum hsum_diff
              convert h using 1
              simp only [Submodule.coe_add]; ring
            -- But f₀ ∉ L(D-p) and c₁+c₂ ≠ 0 means (c₁+c₂)f₀ ∉ L(D-p)
            have hcf₀_not : algebraMap ℂ C.FunctionField (c₁ + c₂) * f₀.val ∉ LDp := by
              intro hmem
              apply hf₀_not
              -- (c₁+c₂)f₀ ∈ L(D-p) and c₁+c₂ ≠ 0 implies f₀ ∈ L(D-p)
              have halg_ne : algebraMap ℂ C.FunctionField (c₁ + c₂) ≠ 0 := by
                simp only [map_ne_zero]
                exact hne'
              have hinv : (algebraMap ℂ C.FunctionField (c₁ + c₂))⁻¹ * (algebraMap ℂ C.FunctionField (c₁ + c₂) * f₀.val) = f₀.val := by
                field_simp
              rw [← hinv]
              -- Need to show (c₁+c₂)⁻¹ * ((c₁+c₂)*f₀) ∈ L(D-p)
              -- Since (c₁+c₂)*f₀ ∈ L(D-p) and constants preserve L(D-p)
              have : (algebraMap ℂ C.FunctionField (c₁ + c₂))⁻¹ * (algebraMap ℂ C.FunctionField (c₁ + c₂) * f₀.val) =
                     (c₁ + c₂)⁻¹ • (algebraMap ℂ C.FunctionField (c₁ + c₂) * f₀.val) := by
                rw [Algebra.smul_def]
                congr 1
                simp only [map_inv₀]
              rw [this]
              exact LDp.smul_mem (c₁ + c₂)⁻¹ hmem
            exact absurd hcf₀_mem hcf₀_not
          · simp only [hsum, dif_neg, not_false_eq_true]
            -- Neither g₁, g₂, nor g₁+g₂ in L(D-p)
            -- Need: c(g₁) + c(g₂) = c(g₁+g₂)
            -- All have valuation -D(p) at p
            -- Key: (g₁ - c₁f₀) + (g₂ - c₂f₀) = (g₁+g₂) - (c₁+c₂)f₀
            -- If both have higher valuation, their sum does too
            -- So c₁+c₂ is the unique coefficient for g₁+g₂
            have hg₁_ne : g₁.val ≠ 0 := by
              intro heq; apply hg₁; rw [heq]
              exact zero_mem_RiemannRochSpace C.toAlgebraicCurve _
            have hg₂_ne : g₂.val ≠ 0 := by
              intro heq; apply hg₂; rw [heq]
              exact zero_mem_RiemannRochSpace C.toAlgebraicCurve _
            have hg₁_val : C.valuation p g₁.val = -D.coeff p :=
              valuation_eq_neg_coeff_of_in_D_not_in_Dp C D p g₁.val g₁.property hg₁
            have hg₂_val : C.valuation p g₂.val = -D.coeff p :=
              valuation_eq_neg_coeff_of_in_D_not_in_Dp C D p g₂.val g₂.property hg₂
            have hsum_ne : (g₁.val + g₂.val) ≠ 0 := by
              intro heq
              apply hsum
              have heq' : (g₁ + g₂).val = 0 := by simp only [Submodule.coe_add]; exact heq
              rw [heq']
              exact zero_mem_RiemannRochSpace C.toAlgebraicCurve _
            have hsum_val : C.valuation p (g₁.val + g₂.val) = -D.coeff p := by
              have hmem : (g₁ + g₂).val ∈ RiemannRochSpace C.toAlgebraicCurve D := (g₁ + g₂).property
              simp only [Submodule.coe_add] at hmem
              exact valuation_eq_neg_coeff_of_in_D_not_in_Dp C D p (g₁.val + g₂.val) hmem hsum
            let c₁ := (C.leadingCoefficientUniquenessGeneral p f₀.val g₁.val hf₀_ne hg₁_ne
                      (by rw [hf₀_val, hg₁_val])).choose
            let c₂ := (C.leadingCoefficientUniquenessGeneral p f₀.val g₂.val hf₀_ne hg₂_ne
                      (by rw [hf₀_val, hg₂_val])).choose
            let c_sum := (C.leadingCoefficientUniquenessGeneral p f₀.val (g₁.val + g₂.val) hf₀_ne hsum_ne
                         (by rw [hf₀_val, hsum_val])).choose
            have hc₁_spec := (C.leadingCoefficientUniquenessGeneral p f₀.val g₁.val hf₀_ne hg₁_ne
                             (by rw [hf₀_val, hg₁_val])).choose_spec
            have hc₂_spec := (C.leadingCoefficientUniquenessGeneral p f₀.val g₂.val hf₀_ne hg₂_ne
                             (by rw [hf₀_val, hg₂_val])).choose_spec
            have hc_sum_spec := (C.leadingCoefficientUniquenessGeneral p f₀.val (g₁.val + g₂.val) hf₀_ne hsum_ne
                                (by rw [hf₀_val, hsum_val])).choose_spec
            obtain ⟨hc₁_ne, hc₁_cases⟩ := hc₁_spec
            obtain ⟨hc₂_ne, hc₂_cases⟩ := hc₂_spec
            obtain ⟨hc_sum_ne, hc_sum_cases⟩ := hc_sum_spec
            -- (c₁+c₂) also satisfies the higher valuation property for g₁+g₂
            have hsum_c_property : (g₁.val + g₂.val) - algebraMap ℂ C.FunctionField (c₁ + c₂) * f₀.val = 0 ∨
                C.valuation p ((g₁.val + g₂.val) - algebraMap ℂ C.FunctionField (c₁ + c₂) * f₀.val) >
                C.valuation p (g₁.val + g₂.val) := by
              have hrewrite : (g₁.val + g₂.val) - algebraMap ℂ C.FunctionField (c₁ + c₂) * f₀.val =
                              (g₁.val - algebraMap ℂ C.FunctionField c₁ * f₀.val) +
                              (g₂.val - algebraMap ℂ C.FunctionField c₂ * f₀.val) := by
                simp only [map_add]; ring
              rcases hc₁_cases with h1_eq | h1_gt <;> rcases hc₂_cases with h2_eq | h2_gt
              · -- Both zero: sum is zero
                left; rw [hrewrite, h1_eq, h2_eq, add_zero]
              · -- First zero, second has higher valuation
                right; rw [hrewrite, h1_eq, zero_add]
                have hg₁_g₂_val : C.valuation p (g₁.val + g₂.val) = C.valuation p g₂.val := by
                  rw [hsum_val, hg₂_val]
                rw [hg₁_g₂_val]; exact h2_gt
              · -- First has higher valuation, second zero
                right; rw [hrewrite, h2_eq, add_zero]
                have hg₁_g₂_val : C.valuation p (g₁.val + g₂.val) = C.valuation p g₁.val := by
                  rw [hsum_val, hg₁_val]
                rw [hg₁_g₂_val]; exact h1_gt
              · -- Both have higher valuation: check if sum is zero
                by_cases hsum_diff_zero : (g₁.val - algebraMap ℂ C.FunctionField c₁ * f₀.val) +
                                          (g₂.val - algebraMap ℂ C.FunctionField c₂ * f₀.val) = 0
                · -- Sum is zero: the difference equals 0
                  left
                  rw [hrewrite]
                  exact hsum_diff_zero
                · -- Sum is nonzero: use ultrametric min
                  right
                  rw [hrewrite]
                  have hmin := C.toAlgebraicCurve.valuation_add_min p
                    (g₁.val - algebraMap ℂ C.FunctionField c₁ * f₀.val)
                    (g₂.val - algebraMap ℂ C.FunctionField c₂ * f₀.val) hsum_diff_zero
                  have h1_val_bound : C.valuation p (g₁.val - algebraMap ℂ C.FunctionField c₁ * f₀.val) > -D.coeff p :=
                    hg₁_val ▸ h1_gt
                  have h2_val_bound : C.valuation p (g₂.val - algebraMap ℂ C.FunctionField c₂ * f₀.val) > -D.coeff p :=
                    hg₂_val ▸ h2_gt
                  rw [hsum_val]
                  omega
            -- By uniqueness, c₁ + c₂ = c_sum (both satisfy the property for g₁+g₂)
            have hc₁c₂_ne : c₁ + c₂ ≠ 0 := by
              intro heq
              rcases hsum_c_property with h_zero | h_gt
              · -- (g₁+g₂) - 0 = g₁+g₂ = 0, contradiction
                rw [heq, map_zero, zero_mul, sub_zero] at h_zero
                exact hsum_ne h_zero
              · -- Valuation of g₁+g₂ is greater than valuation of g₁+g₂, contradiction
                rw [heq, map_zero, zero_mul, sub_zero] at h_gt
                omega
            exact (coeff_unique C D p f₀.val (g₁.val + g₂.val) hf₀_ne hf₀_val hsum_val
              (c₁ + c₂) c_sum hc₁c₂_ne hc_sum_ne hsum_c_property hc_sum_cases).symm
      map_smul' := by
        intro r g
        simp only [RingHom.id_apply]
        by_cases hg_mem : g.val ∈ LDp
        · -- g ∈ L(D-p), so r•g ∈ L(D-p)
          have hrg_mem : (r • g).val ∈ LDp := LDp.smul_mem r hg_mem
          simp only [hg_mem, hrg_mem, dif_pos, smul_zero]
        · -- g ∉ L(D-p)
          simp only [hg_mem, dif_neg, not_false_eq_true]
          by_cases hr : r = 0
          · -- r = 0: r•g = 0 ∈ L(D-p)
            subst hr
            -- 0 • g = 0
            have hzero_mem : (0 : RiemannRochSubmodule C D).val ∈ LDp :=
              zero_mem_RiemannRochSpace C.toAlgebraicCurve (D - point p)
            simp only [zero_smul, dif_pos hzero_mem]
          · -- r ≠ 0: r•g ∉ L(D-p), and c(r•g) = r * c(g)
            have hrg_not : (r • g).val ∉ LDp := by
              intro hmem
              apply hg_mem
              have : r⁻¹ • (r • g).val ∈ LDp := LDp.smul_mem r⁻¹ hmem
              simp only [SetLike.val_smul, smul_smul, inv_mul_cancel₀ hr, one_smul] at this
              exact this
            simp only [hrg_not, dif_neg, not_false_eq_true]
            -- Need: c(r•g) = r • c(g), which is r * c(g) since ℂ acts on itself by multiplication
            -- Both r•g and g have valuation -D(p) at p (r ≠ 0 preserves valuation)
            have hg_ne : g.val ≠ 0 := by
              intro heq; apply hg_mem; rw [heq]
              exact zero_mem_RiemannRochSpace C.toAlgebraicCurve _
            have hg_val : C.valuation p g.val = -D.coeff p :=
              valuation_eq_neg_coeff_of_in_D_not_in_Dp C D p g.val g.property hg_mem
            have hrg_ne : (r • g).val ≠ 0 := by
              simp only [SetLike.val_smul]
              exact smul_ne_zero hr hg_ne
            have hrg_val : C.valuation p (r • g).val = -D.coeff p := by
              simp only [SetLike.val_smul, Algebra.smul_def]
              have halg_ne : algebraMap ℂ C.FunctionField r ≠ 0 := by simp [hr]
              rw [C.toAlgebraicCurve.valuation_mul p _ _ halg_ne hg_ne,
                  C.algebraInst.valuation_algebraMap p r hr, zero_add, hg_val]
            -- Define the coefficients using the uniqueness theorem
            set c := (C.leadingCoefficientUniquenessGeneral p f₀.val g.val hf₀_ne hg_ne
                     (by rw [hf₀_val, hg_val])).choose with hc_def
            set c_rg := (C.leadingCoefficientUniquenessGeneral p f₀.val (r • g).val hf₀_ne hrg_ne
                        (by rw [hf₀_val, hrg_val])).choose with hc_rg_def
            have hc_spec := (C.leadingCoefficientUniquenessGeneral p f₀.val g.val hf₀_ne hg_ne
                            (by rw [hf₀_val, hg_val])).choose_spec
            have hc_rg_spec := (C.leadingCoefficientUniquenessGeneral p f₀.val (r • g).val hf₀_ne hrg_ne
                               (by rw [hf₀_val, hrg_val])).choose_spec
            obtain ⟨hc_ne, hc_cases⟩ := hc_spec
            obtain ⟨hc_rg_ne, hc_rg_cases⟩ := hc_rg_spec
            -- The difference g - c*f₀
            let diff := g.val - algebraMap ℂ C.FunctionField c * f₀.val
            -- r*c satisfies the higher valuation property for r•g
            have hrc_property : (r • g).val - algebraMap ℂ C.FunctionField (r * c) * f₀.val = 0 ∨
                C.valuation p ((r • g).val - algebraMap ℂ C.FunctionField (r * c) * f₀.val) >
                C.valuation p (r • g).val := by
              have hrewrite : (r • g).val - algebraMap ℂ C.FunctionField (r * c) * f₀.val =
                              algebraMap ℂ C.FunctionField r * diff := by
                simp only [SetLike.val_smul, Algebra.smul_def, map_mul, diff]
                ring
              -- Case split on whether diff = 0
              by_cases hdiff : diff = 0
              · -- If diff = 0, then r * diff = 0
                left; rw [hrewrite, hdiff, mul_zero]
              · -- If diff ≠ 0, use valuation multiplication
                right; rw [hrewrite]
                have halg_ne : algebraMap ℂ C.FunctionField r ≠ 0 := by simp [hr]
                rw [C.toAlgebraicCurve.valuation_mul p _ _ halg_ne hdiff,
                    C.algebraInst.valuation_algebraMap p r hr, zero_add, hrg_val]
                -- Need to show v(diff) > -D(p)
                -- This follows from hc_cases: either diff = 0 (contradiction) or v(diff) > v(g)
                rcases hc_cases with h_eq | h_gt
                · exact absurd h_eq hdiff
                · -- h_gt : v(g - c*f₀) > v(g)
                  -- Convert using hg_val : v(g) = -D(p)
                  exact hg_val ▸ h_gt
            -- By uniqueness, r*c = c_rg
            have hrc_ne : r * c ≠ 0 := mul_ne_zero hr hc_ne
            have hrc_eq_c_rg : r * c = c_rg :=
              coeff_unique C D p f₀.val (r • g).val hf₀_ne hf₀_val hrg_val
                (r * c) c_rg hrc_ne hc_rg_ne hrc_property hc_rg_cases
            -- Convert to the goal: c_rg = r • c (using smul = mul for ℂ on ℂ)
            simp only [smul_eq_mul]
            exact hrc_eq_c_rg.symm
    }

/-- The kernel of f₂ is exactly L(D-p) (as submodule of L(D)) -/
theorem f₂_ker_eq_range_f₁
    [RiemannRochSubmoduleFiniteDimensional C D]
    [RiemannRochSubmoduleFiniteDimensional C (D - point p)] :
    LinearMap.ker (f₂ C D p) = LinearMap.range (f₁ C D p) := by
  -- ker(f₂) = {g ∈ L(D) : coeff(g) = 0} = {g ∈ L(D) : g ∈ L(D-p)} = L(D-p)
  -- range(f₁) = L(D-p) (viewed as submodule of L(D))
  ext g
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  let LDp := RiemannRochSubmodule C (D - point p)
  constructor
  · -- ker(f₂) ⊆ range(f₁): if f₂(g) = 0, then g ∈ image of inclusion
    intro hker
    -- Unfold f₂ to see when it returns 0
    unfold f₂ at hker
    -- Simplify the let bindings
    dsimp only at hker
    -- The definition of f₂ is by cases on whether L(D) = L(D-p)
    split_ifs at hker with hAll
    · -- Case 1: L(D) = L(D-p), so g ∈ L(D-p)
      have hg_in : g.val ∈ LDp := hAll g.val g.property
      exact ⟨⟨g.val, hg_in⟩, Subtype.ext rfl⟩
    · -- Case 2: There exists f₀ ∈ L(D) \ L(D-p)
      -- Now hker is about the inner linear map
      -- Simplify the LinearMap application to expose the inner if
      simp only [LinearMap.coe_mk, AddHom.coe_mk] at hker
      -- Split on whether g ∈ L(D-p)
      split_ifs at hker with hg_mem
      · -- g ∈ L(D-p), so it's in the image
        exact ⟨⟨g.val, hg_mem⟩, Subtype.ext rfl⟩
      · -- g ∉ L(D-p), but f₂(g) = 0 - contradiction
        -- In this branch, f₂(g) is the .choose from leadingCoefficientUniquenessGeneral
        -- which is nonzero by its specification
        exfalso
        push_neg at hAll
        have hg_ne : g.val ≠ 0 := by
          intro heq; apply hg_mem; rw [heq]
          exact zero_mem_RiemannRochSpace C.toAlgebraicCurve (D - point p)
        have hg_val : C.valuation p g.val = -D.coeff p :=
          valuation_eq_neg_coeff_of_in_D_not_in_Dp C D p g.val g.property hg_mem
        -- Get the specification of the chosen coefficient
        have hex : ∃ f₀ : RiemannRochSubmodule C D, f₀.val ∉ LDp := by
          obtain ⟨f, hfD, hfnot⟩ := hAll
          exact ⟨⟨f, hfD⟩, hfnot⟩
        have hf₀_not : (Classical.choose hex).val ∉ LDp := Classical.choose_spec hex
        have hf₀_ne : (Classical.choose hex).val ≠ 0 := by
          intro heq; apply hf₀_not; rw [heq]
          exact zero_mem_RiemannRochSpace C.toAlgebraicCurve (D - point p)
        have hf₀_val : C.valuation p (Classical.choose hex).val = -D.coeff p :=
          valuation_eq_neg_coeff_of_in_D_not_in_Dp C D p (Classical.choose hex).val
            (Classical.choose hex).property hf₀_not
        have heq_val : C.valuation p (Classical.choose hex).val = C.valuation p g.val := by
          rw [hf₀_val, hg_val]
        have hspec := (C.leadingCoefficientUniquenessGeneral p (Classical.choose hex).val g.val
                       hf₀_ne hg_ne heq_val).choose_spec
        exact hspec.1 hker
  · -- range(f₁) ⊆ ker(f₂): if g is in the image, then f₂(g) = 0
    intro ⟨h, hh⟩
    -- h ∈ L(D-p), and g = f₁(h) = inclusion(h)
    -- So g.val = h.val ∈ L(D-p)
    have hg_mem : g.val ∈ LDp := by
      rw [← hh]
      exact h.property
    -- In f₂, when g.val ∈ LDp, the result is 0
    unfold f₂
    dsimp only
    split_ifs with hAll
    · -- Case 1: f₂ = 0
      rfl
    · -- Case 2: split on g ∈ L(D-p)
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      exact dif_pos hg_mem

/-- f₃: The connecting homomorphism ℂ → Dual(L(K-D+p)).

    This is defined by: for c ∈ ℂ, f₃(c) is the functional
    ω ↦ c * (coefficient of ω at p)

    When c ∈ range(f₂), the functional f₃(c) is zero on L(K-D).
-/
noncomputable def f₃
    [RiemannRochSubmoduleFiniteDimensional C (K.K - D + point p)] :
    ℂ →ₗ[ℂ] (RiemannRochSubmodule C (K.K - D + point p) →ₗ[ℂ] ℂ) := by
  haveI : RiemannRochSubmoduleFiniteDimensional C (K.K - D) :=
    RiemannRochSubmodule_finiteDimensional C (K.K - D)
  -- For c ∈ ℂ, f₃(c)(ω) = c * coeff_p(ω)
  let coeffKD := f₂ C (K.K - D + point p) p
  exact {
    toFun := fun c => c • coeffKD
    map_add' := fun _ _ => by ext; simp [add_smul]
    map_smul' := fun _ _ => by ext; simp [smul_smul]
  }

/-- f₄: Dual(L(K-D+p)) → Dual(L(K-D)).

    This is the dual of the inclusion L(K-D) ↪ L(K-D+p).
    For φ ∈ Dual(L(K-D+p)), f₄(φ) = φ ∘ inclusion.
-/
noncomputable def f₄
    [RiemannRochSubmoduleFiniteDimensional C (K.K - D + point p)]
    [RiemannRochSubmoduleFiniteDimensional C (K.K - D)] :
    (RiemannRochSubmodule C (K.K - D + point p) →ₗ[ℂ] ℂ) →ₗ[ℂ]
    (RiemannRochSubmodule C (K.K - D) →ₗ[ℂ] ℂ) := {
  toFun := fun φ => φ.comp (Submodule.inclusion (RiemannRochSpace_KD_subset C K D p))
  map_add' := fun _ _ => by ext; simp
  map_smul' := fun _ _ => by ext; simp
}

/-- f₄ is surjective (dual of injection is surjection in finite dimensions) -/
theorem f₄_surjective
    [RiemannRochSubmoduleFiniteDimensional C (K.K - D + point p)]
    [RiemannRochSubmoduleFiniteDimensional C (K.K - D)] :
    Function.Surjective (f₄ C K D p) := by
  letI : Module ℂ ↥(RiemannRochSubmodule C (K.K - D)) :=
    (RiemannRochSubmodule C (K.K - D)).module
  letI : Module ℂ ↥(RiemannRochSubmodule C (K.K - D + point p)) :=
    (RiemannRochSubmodule C (K.K - D + point p)).module
  let incl := Submodule.inclusion (RiemannRochSpace_KD_subset C K D p)
  have h_incl_inj : Function.Injective incl := Submodule.inclusion_injective _
  have hf₄_eq : f₄ C K D p = incl.dualMap := by
    ext φ x
    simp [f₄, incl, LinearMap.dualMap_apply']
  rw [hf₄_eq]
  exact @LinearMap.dualMap_surjective_of_injective ℂ
    ↥(RiemannRochSubmodule C (K.K - D))
    ↥(RiemannRochSubmodule C (K.K - D + point p))
    inferInstance
    (RiemannRochSubmodule C (K.K - D)).addCommGroup
    (RiemannRochSubmodule C (K.K - D)).module
    (RiemannRochSubmodule C (K.K - D + point p)).addCommGroup
    (RiemannRochSubmodule C (K.K - D + point p)).module
    (f := incl)
    h_incl_inj

/-- Exactness at Dual(L(K-D+p)): ker(f₄) = range(f₃)

    Key facts:
    1. coeffKD vanishes on L(K-D) (by f₂_ker_eq_range_f₁)
    2. dim(ker(f₄)) = b = dim(L(K-D+p)/L(K-D))
    3. dim(range(f₃)) = b (either 0 if coeffKD = 0, or 1 if coeffKD ≠ 0)
    4. Both b values coincide: coeffKD = 0 iff L(K-D+p) = L(K-D)
    5. range(f₃) ⊆ ker(f₄), and equal dimensions imply equality -/
theorem f₄_ker_eq_range_f₃
    [RiemannRochSubmoduleFiniteDimensional C (K.K - D + point p)]
    [RiemannRochSubmoduleFiniteDimensional C (K.K - D)] :
    LinearMap.ker (f₄ C K D p) = LinearMap.range (f₃ C K D p) := by
  letI : Module ℂ ↥(RiemannRochSubmodule C (K.K - D)) :=
    (RiemannRochSubmodule C (K.K - D)).module
  letI : Module ℂ ↥(RiemannRochSubmodule C (K.K - D + point p)) :=
    (RiemannRochSubmodule C (K.K - D + point p)).module
  let incl := Submodule.inclusion (RiemannRochSpace_KD_subset C K D p)
  let coeffKD := f₂ C (K.K - D + point p) p
  have hf₄_eq : f₄ C K D p = incl.dualMap := by
    ext φ x
    simp [f₄, incl, LinearMap.dualMap_apply']
  have hKD_eq : K.K - D + point p - point p = K.K - D := by
    ext q
    simp only [sub_coeff, add_coeff, point]
    ring
  haveI : RiemannRochSubmoduleFiniteDimensional C (K.K - D + point p - point p) := by
    rw [hKD_eq]
    infer_instance
  have hker_coeff :
      LinearMap.ker coeffKD = LinearMap.range (f₁ C (K.K - D + point p) p) :=
    f₂_ker_eq_range_f₁ C (K.K - D + point p) p
  have hker_coeff' : LinearMap.ker coeffKD = LinearMap.range incl := by
    ext ω
    constructor
    · intro hω
      have hω' : ω ∈ LinearMap.range (f₁ C (K.K - D + point p) p) := by
        rwa [← hker_coeff]
      rcases hω' with ⟨x, rfl⟩
      have hx_mem : x.val ∈ RiemannRochSubmodule C (K.K - D) := by
        simpa [hKD_eq] using x.property
      refine ⟨⟨x.val, hx_mem⟩, ?_⟩
      ext
      simp [f₁, inclusionMap, incl]
    · intro hω
      rcases hω with ⟨x, rfl⟩
      have hx_mem :
          x.val ∈ RiemannRochSubmodule C (K.K - D + point p - point p) := by
        simpa [hKD_eq] using x.property
      have hω' :
          incl x ∈ LinearMap.range (f₁ C (K.K - D + point p) p) := by
        refine ⟨⟨x.val, hx_mem⟩, ?_⟩
        ext
        simp [f₁, inclusionMap, incl]
      rwa [← hker_coeff] at hω'
  have hrange_dual_coeff :
      LinearMap.range coeffKD.dualMap = (LinearMap.range incl).dualAnnihilator := by
    calc
      LinearMap.range coeffKD.dualMap = (LinearMap.ker coeffKD).dualAnnihilator := by
        exact @LinearMap.range_dualMap_eq_dualAnnihilator_ker ℂ
          ↥(RiemannRochSubmodule C (K.K - D + point p))
          ℂ
          inferInstance
          (RiemannRochSubmodule C (K.K - D + point p)).addCommGroup
          (RiemannRochSubmodule C (K.K - D + point p)).module
          inferInstance
          inferInstance
          coeffKD
      _ = (LinearMap.range incl).dualAnnihilator := by rw [hker_coeff']
  have hf₃_eq :
      f₃ C K D p = LinearMap.toSpanSingleton ℂ _ coeffKD := by
    ext c
    simp [f₃, coeffKD, LinearMap.toSpanSingleton_apply]
  have hspan_f₃ : ℂ ∙ coeffKD = LinearMap.range (f₃ C K D p) := by
    rw [hf₃_eq, LinearMap.span_singleton_eq_range]
  calc
    LinearMap.ker (f₄ C K D p) = (LinearMap.range incl).dualAnnihilator := by
      rw [hf₄_eq, LinearMap.ker_dualMap_eq_dualAnnihilator_range]
    _ = LinearMap.range coeffKD.dualMap := hrange_dual_coeff.symm
    _ = ℂ ∙ coeffKD := by
      exact LinearMap.range_dualMap_dual_eq_span_singleton coeffKD
    _ = LinearMap.range (f₃ C K D p) := hspan_f₃

set_option maxHeartbeats 800000 in
/-- **Serre pairing containment**: range(f₂) ⊆ ker(f₃)

    This is the key containment that comes from the Serre pairing / residue theorem.
    For any f ∈ L(D) and ω ∈ L(K-D+p), the product coeff_D(f) · coeff_{K-D+p}(ω) = 0.

    **Mathematical justification**:
    - The product f·ω (where ω is viewed as a differential) has divisor ≥ -K - point(p)
    - This means f·ω has at most a simple pole at p and no other poles
    - By the residue theorem on a compact curve: sum of residues = 0
    - With only one pole, Res_p(f·ω) = 0
    - The residue is the product of leading coefficients: coeff_D(f) · coeff_{K-D+p}(ω)
    - Therefore this product is 0

    **Consequence**: dim(range f₂) ≤ dim(ker f₃), i.e., a ≤ 1 - b, i.e., a + b ≤ 1.
    This rules out (1,1). -/
theorem range_f₂_le_ker_f₃
    [RiemannRochSubmoduleFiniteDimensional C D]
    [RiemannRochSubmoduleFiniteDimensional C (D - point p)]
    [RiemannRochSubmoduleFiniteDimensional C (K.K - D + point p)] :
    LinearMap.range (f₂ C D p) ≤ LinearMap.ker (f₃ C K D p) := by
  -- For any c in range(f₂), show c ∈ ker(f₃)
  intro c hc
  simp only [LinearMap.mem_range] at hc
  obtain ⟨f, hf⟩ := hc
  rw [LinearMap.mem_ker, ← hf]
  -- Need to show f₃(f₂(f)) = 0
  -- f₃(c)(ω) = c · coeff_{K-D+p}(ω)
  -- So f₃(f₂(f))(ω) = coeff_D(f) · coeff_{K-D+p}(ω)
  -- This is 0 by the Serre pairing (residue theorem)
  ext ω
  -- The goal is f₃(f₂(f))(ω) = 0
  -- f₃(c)(ω) = c • coeffKD(ω) where coeffKD = f₂ C (K.K - D + point p) p
  -- So we need: f₂(f) • f₂(K.K - D + point p)(ω) = 0
  --
  -- The coefficient product coeff_D(f) · coeff_{K-D+p}(ω) = 0
  -- This follows from the residue theorem: their product has poles only at p,
  -- so the sum of residues (just at p) equals 0.
  -- The residue is the product of leading coefficients.
  --
  -- More precisely:
  -- - If f ∈ L(D-p), then coeff_D(f) = 0, so product = 0
  -- - If ω ∈ L(K-D), then coeff_{K-D+p}(ω) = 0, so product = 0
  -- - If both have exact valuations, the product f·ω has a simple pole at p.
  --   By residue theorem, Res_p = 0. Contradiction: nonzero · nonzero = 0.
  --   So both having exact valuations is impossible.
  --
  -- Therefore, at least one coefficient is 0, so the product is 0.

  -- Helper: coefficient extraction for K-D+p space
  let coeffKD := f₂ C (K.K - D + point p) p

  -- Helper: divisor equality for K - (D - p) = K - D + p
  have hKD_eq : K.K - D + point p - point p = K.K - D := by
    ext q; simp only [sub_coeff, add_coeff, point]; ring

  haveI inst_KD : RiemannRochSubmoduleFiniteDimensional C (K.K - D) :=
    RiemannRochSubmodule_finiteDimensional C (K.K - D)
  haveI inst_KDp_sub : RiemannRochSubmoduleFiniteDimensional C (K.K - D + point p - point p) := by
    rw [hKD_eq]; infer_instance

  -- Simplify the goal to work with f₂ and coeffKD
  show (f₃ C K D p) ((f₂ C D p) f) ω = 0
  simp only [f₃, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply]
  -- Goal is now: f₂(f) • coeffKD(ω) = 0

  -- Case 1: f ∈ L(D-p) implies f₂(f) = 0
  -- Case 2: ω ∈ L(K-D) implies coeffKD(ω) = 0
  -- Case 3: f ∉ L(D-p) and ω ∉ L(K-D) is impossible by residue theorem

  -- Check if f is in the kernel of f₂ (i.e., f ∈ L(D-p))
  by_cases hf_ker : f ∈ LinearMap.ker (f₂ C D p)
  · -- Case 1: f ∈ ker(f₂), so f₂(f) = 0
    rw [LinearMap.mem_ker] at hf_ker
    rw [hf_ker, zero_smul]

  · -- f ∉ ker(f₂), so f₂(f) ≠ 0, meaning f has exact valuation at p
    -- Check if ω is in the kernel of coeffKD (i.e., ω ∈ L(K-D))
    by_cases hω_ker : ω ∈ LinearMap.ker coeffKD
    · -- Case 2: ω ∈ ker(coeffKD), so coeffKD(ω) = 0
      rw [LinearMap.mem_ker] at hω_ker
      rw [hω_ker, smul_zero]

    · -- Case 3: Both have exact valuations - contradiction by residue theorem
      exfalso
      -- f ∉ ker(f₂) means f₂(f) ≠ 0, so f ∉ L(D-p)
      -- ω ∉ ker(coeffKD) means coeffKD(ω) ≠ 0, so ω ∉ L(K-D)

      -- Use f₂_ker_eq_range_f₁ to characterize ker(f₂)
      have hker_D := f₂_ker_eq_range_f₁ C D p
      have hker_KDp := f₂_ker_eq_range_f₁ C (K.K - D + point p) p

      -- f ∉ ker(f₂) = range(f₁) means f.val ∉ L(D-p)
      rw [hker_D, LinearMap.mem_range] at hf_ker
      push_neg at hf_ker
      have hf_not_Dp : f.val ∉ RiemannRochSubmodule C (D - point p) := by
        intro hcontra
        let g : RiemannRochSubmodule C (D - point p) := ⟨f.val, hcontra⟩
        have hf₁_img : (f₁ C D p) g = f := by
          ext; rfl
        exact hf_ker g hf₁_img

      -- ω ∉ ker(coeffKD) = range(f₁) means ω.val ∉ L(K-D)
      rw [hker_KDp, LinearMap.mem_range] at hω_ker
      push_neg at hω_ker
      have hω_not_KDp_sub : ω.val ∉ RiemannRochSubmodule C (K.K - D + point p - point p) := by
        intro hcontra
        let g : RiemannRochSubmodule C (K.K - D + point p - point p) := ⟨ω.val, hcontra⟩
        have hf₁_img : (f₁ C (K.K - D + point p) p) g = ω := by
          ext; rfl
        exact hω_ker g hf₁_img

      -- f has exact valuation at p
      have hf_exact : C.valuation p f.val = -D.coeff p :=
        valuation_eq_neg_coeff_of_in_D_not_in_Dp C D p f.val f.property hf_not_Dp

      -- ω has exact valuation at p (note: don't rewrite yet)
      have hω_exact : C.valuation p ω.val = -(K.K - D + point p).coeff p :=
        valuation_eq_neg_coeff_of_in_D_not_in_Dp C (K.K - D + point p) p ω.val ω.property hω_not_KDp_sub

      -- f ≠ 0 (since f ∉ L(D-p) and 0 ∈ L(D-p))
      have hf_ne : f.val ≠ 0 := by
        intro heq
        apply hf_not_Dp
        rw [heq]
        exact zero_mem_RiemannRochSpace C.toAlgebraicCurve _

      -- ω ≠ 0 (since ω ∉ L(K-D+p-p) and 0 ∈ L(K-D+p-p))
      have hω_ne : ω.val ≠ 0 := by
        intro heq
        apply hω_not_KDp_sub
        rw [heq]
        exact zero_mem_RiemannRochSpace C.toAlgebraicCurve _

      -- Both are in quotient spaces with exact valuations
      have hf_inQ : Algebraic.inQuotientSpace C f.val D p := by
        refine ⟨hf_ne, ?_, hf_exact⟩
        intro q
        have hf_D : f.val ∈ RiemannRochSpace C.toAlgebraicCurve D := f.property
        simp only [RiemannRochSpace, Set.mem_setOf_eq] at hf_D
        rcases hf_D with heq | hval
        · exact absurd heq hf_ne
        · specialize hval q; omega

      -- Create CanonicalData from CanonicalDivisor
      -- K.K is the canonical divisor
      let KC : RiemannSurfaces.Algebraic.CanonicalData C := ⟨K.K⟩
      -- KC.K = K.K by definition
      have hKC_eq : KC.K = K.K := rfl

      have hω_inQ : RiemannSurfaces.Algebraic.inQuotientSpace C ω.val (KC.K - D + point p) p := by
        simp only [hKC_eq]
        refine ⟨hω_ne, ?_, hω_exact⟩
        intro q
        have hω_KDp : ω.val ∈ RiemannRochSpace C.toAlgebraicCurve (K.K - D + point p) := ω.property
        simp only [RiemannRochSpace, Set.mem_setOf_eq] at hω_KDp
        rcases hω_KDp with heq | hval
        · exact absurd heq hω_ne
        · specialize hval q; omega

      -- Apply residue_pairing_zero
      exact RiemannSurfaces.Algebraic.residue_pairing_zero C hf_inQ hω_inQ

/- **Euler characteristic constraint**: a + b = 1

    This is the key algebraic identity that comes from the Euler characteristic
    of the skyscraper sheaf sequence:
      0 → O(D-p) → O(D) → k_p → 0

    **Mathematical justification**:
    - χ(O(D)) - χ(O(D-p)) = χ(k_p) = h⁰(k_p) - h¹(k_p) = 1 - 0 = 1
    - The h¹(k_p) = 0 is skyscraper acyclicity (captured by f₄ surjective)
    - Using χ(O(E)) = h⁰(E) - h⁰(K-E) (Serre duality as definition):
      (h⁰(D) - h⁰(K-D)) - (h⁰(D-p) - h⁰(K-D+p)) = 1
    - Rearranging: a + b = 1

    This is NOT an axiom but follows from the sheaf-theoretic structure.
    The constraint is independent of exactness at V₃ - it's a dimension identity
    that comes from the short exact sequence of sheaves itself.

    The proof and final statement are continued in `PointExactSequence/Constraint.lean`. -/

end RiemannSurfaces.Algebraic.Cohomology.PointExactSequence
