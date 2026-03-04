/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringGeometry.RiemannSurfaces.SchemeTheoretic.Sheaves.LineBundles
import StringGeometry.RiemannSurfaces.SchemeTheoretic.Sheaves.Skyscraper
import StringGeometry.RiemannSurfaces.SchemeTheoretic.LocalRings

/-!
# Morphisms for the Point Exact Sequence

This file provides infrastructure for constructing the morphisms in the fundamental
point exact sequence:

  0 → O(D - [p]) → O(D) → k_p → 0

## Main Definitions

* `uniformizerAt` - A uniformizer (local parameter) at point p with v_p(t) = 1
* `inclusionMorphism` - The inclusion O(D-[p]) ↪ O(D) (multiplication by uniformizer)
* `evaluationMorphism` - The evaluation O(D) → k_p (restriction to residue field)

## Mathematical Construction

**Uniformizers:**
  - From `LocalRings.exists_localParameter`: ∃ t, v_p(t) = 1
  - We use `Classical.choose` to pick one such element

**Inclusion morphism O(D - [p]) → O(D):**
  - Defined by f ↦ t_p · f where t_p is a uniformizer at p
  - If f ∈ O(D-[p])(U), then v_q(f) ≥ -(D-[p])(q) for all q ∈ U
  - v_p(f) ≥ -(D-[p])(p) = -D(p) + 1
  - v_p(t_p · f) = 1 + v_p(f) ≥ 1 + (-D(p) + 1) = -D(p) + 2 ≥ -D(p) ✓

**Evaluation morphism O(D) → k_p:**
  - Defined by restricting a section to its value at p
  - For f ∈ O(D)(U) with p ∈ U, we have v_p(f) ≥ -D(p)
  - The residue class in κ(p) is well-defined

**Exactness:**
  - ker(eval) = { f ∈ O(D)(U) : f(p) = 0 } = { f : v_p(f) ≥ 1 - D(p) } = O(D-[p])(U)
  - This shows exactness at the middle term

## References

* Hartshorne, "Algebraic Geometry", Chapter IV.1 (Riemann-Roch)
-/

open AlgebraicGeometry CategoryTheory

namespace RiemannSurfaces.SchemeTheoretic

variable (C : SmoothProjectiveCurve)

/-!
## Uniformizers

A uniformizer at a point p is a local parameter: an element t_p ∈ K(C) with v_p(t_p) = 1.
On a smooth curve, such elements exist because the stalks are DVRs.

We use `Classical.choose` on `exists_localParameter` to obtain a canonical choice.
-/

/-- A uniformizer at a point p is an element t ∈ K(C) with v_p(t) = 1.

    **Existence:** Uses `SmoothProjectiveCurve.exists_localParameter` from LocalRings.lean,
    which derives uniformizer existence from the DVR structure of stalks.

    **Construction:** `Classical.choose` picks a witness from the existence theorem. -/
noncomputable def uniformizerAt (p : C.PointType) : C.FunctionFieldType :=
  Classical.choose (C.exists_localParameter p)

/-- The uniformizer has valuation 1 at p.

    **Proof:** Follows directly from `Classical.choose_spec` on `exists_localParameter`. -/
theorem uniformizer_valuation (p : C.PointType) :
    C.valuationAt p (uniformizerAt C p) = 1 :=
  Classical.choose_spec (C.exists_localParameter p)

/-- The uniformizer is nonzero.

    **Proof:** If t_p = 0, then v_p(0) = 0 ≠ 1 by `valuationAt_zero`. -/
theorem uniformizer_ne_zero (p : C.PointType) : uniformizerAt C p ≠ 0 := by
  intro h
  have hval := uniformizer_valuation C p
  rw [h, C.valuationAt_zero] at hval
  exact one_ne_zero hval.symm

/-- The uniformizer has finite support (only finitely many points with nonzero valuation).

    **Proof:** Follows from `valuationAt_finiteSupport` in LocalRings.lean. -/
theorem uniformizer_finiteSupport (p : C.PointType) :
    Set.Finite { q : C.PointType | C.valuationAt q (uniformizerAt C p) ≠ 0 } :=
  C.valuationAt_finiteSupport (uniformizerAt C p) (uniformizer_ne_zero C p)

/-- The principal divisor of a uniformizer has degree 0.

    **Note:** v_p(t_p) = 1, so by the argument principle, the sum of valuations
    at other points is -1. This means there must be some pole(s) elsewhere. -/
theorem uniformizer_degree_zero (p : C.PointType) :
    (principalDivisor C (uniformizerAt C p) (uniformizer_ne_zero C p)).degree = 0 :=
  principalDivisor_degree_zero C (uniformizerAt C p) (uniformizer_ne_zero C p)

/-!
## The Inclusion Morphism

The inclusion O(D-[p]) → O(D) is the natural inclusion of subsheaves.

**Key insight:**
O(D-[p]) and O(D) are both subsheaves of the constant sheaf K(C).
For a section f, we have:
- f ∈ O(D-[p])(U) ⟺ v_q(f) ≥ -(D-[p])(q) for all q ∈ U
- f ∈ O(D)(U) ⟺ v_q(f) ≥ -D(q) for all q ∈ U

Since (D-[p])(q) = D(q) - [p](q):
- For q ≠ p: (D-[p])(q) = D(q), so conditions are the same
- For q = p: (D-[p])(p) = D(p) - 1, so v_p(f) ≥ -D(p)+1 > -D(p)

Therefore O(D-[p])(U) ⊆ O(D)(U), and the inclusion is just the natural embedding.
-/

/-- The inclusion morphism O(D - [p]) → O(D).

    **Mathematical definition:**
    The natural inclusion of subsheaves of K(C). For each open U:
      O(D-[p])(U) → O(D)(U)
      f ↦ f

    **Why this is well-defined:**
    If f ∈ O(D-[p])(U), then v_q(f) ≥ -(D-[p])(q) for all q ∈ U.
    - For q ≠ p: -(D-[p])(q) = -D(q), so v_q(f) ≥ -D(q) ✓
    - For q = p: -(D-[p])(p) = -D(p)+1 > -D(p), so v_p(f) ≥ -D(p) ✓
    Therefore f ∈ O(D)(U). -/
theorem exists_inclusionMorphism (D : Divisor C.toAlgebraicCurve) (p : C.PointType) :
    Nonempty ((divisorSheaf C (D - Divisor.point p)).toModule ⟶ (divisorSheaf C D).toModule) := by
  -- TODO: Implement as the subsheaf inclusion induced by divisor inequalities.
  sorry

/-!
## The Evaluation Morphism

The evaluation O(D) → k_p is given by restricting a section to its value at p.
-/

/-- The evaluation morphism O(D) → k_p.

    **Mathematical definition:**
    For f ∈ O(D)(U) with p ∈ U, map f to its "value" at p.

    More precisely:
    - The stalk O_{C,p} has maximal ideal m_p
    - κ(p) = O_{C,p} / m_p is the residue field
    - For f with v_p(f) ≥ -D(p), the element t_p^{D(p)} · f is regular at p
    - Its image in κ(p) gives the evaluation

    **Type-theoretic definition:**
    A morphism in X.Modules = SheafOfModules X.ringCatSheaf from
    divisorModule C D to skyscraperModule C.toAlgebraicCurve p. -/
theorem exists_evaluationMorphism (D : Divisor C.toAlgebraicCurve) (p : C.PointType) :
    Nonempty ((divisorSheaf C D).toModule ⟶ skyscraperModule C.toAlgebraicCurve p) := by
  -- TODO: Implement from stalk-to-residue evaluation at p.
  sorry

/-!
## Point Morphism Package

To avoid definition-level `Classical.choice` from unproved existence theorems,
we keep the two morphisms and exactness witnesses as explicit data.
-/

/-- Data package for the point exact sequence
`0 → O(D-[p]) → O(D) → k_p → 0`. -/
structure PointMorphismData (C : SmoothProjectiveCurve)
    (D : Divisor C.toAlgebraicCurve) (p : C.PointType) where
  /-- Inclusion map `O(D-[p]) ⟶ O(D)`. -/
  inclusion :
    (divisorSheaf C (D - Divisor.point p)).toModule ⟶ (divisorSheaf C D).toModule
  /-- Evaluation map `O(D) ⟶ k_p`. -/
  evaluation :
    (divisorSheaf C D).toModule ⟶ skyscraperModule C.toAlgebraicCurve p
  /-- Inclusion is mono. -/
  mono_inclusion : Mono inclusion
  /-- Evaluation is epi. -/
  epi_evaluation : Epi evaluation
  /-- Composition vanishes. -/
  comp_zero : inclusion ≫ evaluation = 0
  /-- Exactness at the middle term. -/
  exact :
    (CategoryTheory.ShortComplex.mk inclusion evaluation comp_zero).Exact

/-- Existence of full point-exact-sequence morphism data. -/
theorem exists_pointMorphismData (D : Divisor C.toAlgebraicCurve) (p : C.PointType) :
    Nonempty (PointMorphismData C D p) := by
  sorry

/-!
## Exactness of the Point Sequence
-/

/-- The composition `i ≫ p` is zero for packaged point morphism data. -/
theorem PointMorphismData.composition_zero
    (D : Divisor C.toAlgebraicCurve) (p : C.PointType)
    (data : PointMorphismData C D p) :
    data.inclusion ≫ data.evaluation = 0 :=
  data.comp_zero

/-- Exactness at the middle term for packaged point morphism data. -/
theorem PointMorphismData.pointSequence_exact
    (D : Divisor C.toAlgebraicCurve) (p : C.PointType)
    (data : PointMorphismData C D p) :
    (CategoryTheory.ShortComplex.mk
      data.inclusion
      data.evaluation
      data.comp_zero).Exact :=
  data.exact

end RiemannSurfaces.SchemeTheoretic
