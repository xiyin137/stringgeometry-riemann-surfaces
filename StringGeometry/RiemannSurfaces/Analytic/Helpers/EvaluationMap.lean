import StringGeometry.RiemannSurfaces.Analytic.LineBundles
import StringGeometry.RiemannSurfaces.Analytic.Helpers.RRHelpers

/-!
# Evaluation Map for Linear Systems

This file develops the evaluation map `ev_p : L(D + [p]) → ℂ` that extracts
the "pole coefficient" at a point p. This is the key tool for understanding
how h⁰ changes when adding a point to a divisor.

## Main Results

* `h0_add_point_le` — h⁰(D) ≤ h⁰(D + [p]) ≤ h⁰(D) + 1
* `linearSystem_restriction_to_D` — The kernel of ev_p maps to L(D)

## Mathematical Background

Given a divisor D and a point p, there is a short exact sequence of sheaves:
  0 → O(D) → O(D + [p]) →^{ev_p} k_p → 0

where k_p is the skyscraper sheaf at p. Taking global sections:
  0 → H⁰(O(D)) → H⁰(O(D+[p])) →^{ev_p} ℂ

The map ev_p extracts the "principal part" at p: for f ∈ L(D+[p]),
ev_p(f) = coefficient of (z - z_p)^{-D(p)-1} in the Laurent expansion.

When D(p) = 0, ev_p(f) = (z - z_p)^{-1}-coefficient, i.e., the residue-like part.
When D(p) ≥ 0, ev_p(f) is the leading pole coefficient beyond what D allows.

## References

* Griffiths, Harris "Principles of Algebraic Geometry" Ch 2.3
* Miranda "Algebraic Curves and Riemann Surfaces" Ch VII
-/

namespace RiemannSurfaces.Analytic

open Divisor
open scoped Manifold

/-!
## Restriction from L(D + [p]) to L(D)

An element of L(D + [p]) is in L(D) if and only if its order at p
is at least -D(p) (i.e., the extra pole allowed by [p] is not used).
-/

variable {RS : RiemannSurface}

/-- An element of L(D + [p]) whose order at p is high enough
    can be viewed as an element of L(D). This is the kernel of
    the evaluation map ev_p : L(D+[p]) → ℂ. -/
theorem linearSystem_add_point_to_D {D : Divisor RS} {p : RS.carrier}
    (ls : LinearSystem RS (D + Divisor.point p))
    (hord : 0 ≤ ls.fn.order p + D.coeff p) :
    ∃ ls' : LinearSystem RS D, ls'.fn = ls.fn :=
  ⟨linearSystem_tighten ls hord, linearSystem_tighten_fn ls hord⟩

/-- If an element of L(D + [p]) has a zero at p (when D(p) = 0), it's in L(D). -/
theorem linearSystem_zero_at_point_in_D {D : Divisor RS}
    (ls : LinearSystem RS (D + Divisor.point p))
    (hp : D.coeff p = 0)
    (hord : 0 ≤ ls.fn.order p) :
    ∃ ls' : LinearSystem RS D, ls'.fn = ls.fn := by
  have : 0 ≤ ls.fn.order p + D.coeff p := by rw [hp]; omega
  exact linearSystem_add_point_to_D ls this

/-!
## Dimension Bounds

The key inequality: h⁰(D) ≤ h⁰(D + [p]) ≤ h⁰(D) + 1.

The left inequality is h0_mono (proven in RRHelpers).
The right inequality follows from rank-nullity for the evaluation map:
  dim L(D+[p]) = dim ker(ev_p) + dim im(ev_p) ≤ dim L(D) + 1
-/

/-- h⁰(D + [p]) ≤ h⁰(D) + 1 from five-term exact-sequence data. -/
theorem h0_add_point_upper_of_fiveTermData (CRS : CompactRiemannSurface)
    (K : CanonicalDivisor CRS)
    (D : Divisor CRS.toRiemannSurface) (p : CRS.toRiemannSurface.carrier)
    (hdata : EvalResidueFiveTermData CRS K D p) :
    h0 CRS (D + Divisor.point p) ≤ h0 CRS D + 1 := by
  have hcomp :
      (h0 CRS (D + Divisor.point p) : ℤ) - (h0 CRS D : ℤ) +
      ((h0 CRS (K.representative + (-D)) : ℤ) -
       (h0 CRS (K.representative + (-(D + Divisor.point p))) : ℤ)) = 1 :=
    eval_residue_complementarity_of_fiveTermData CRS K D p hdata
  have hdual_le :
      h0 CRS (K.representative + (-(D + Divisor.point p))) ≤
        h0 CRS (K.representative + (-D)) := by
    have hle :
        K.representative + (-(D + Divisor.point p)) ≤
          K.representative + (-D) := by
      simpa [add_assoc, add_left_comm, add_comm, neg_add] using
        (sub_point_le (D := K.representative + (-D)) p)
    exact h0_mono CRS hle
  have hdual_nonneg :
      0 ≤ (h0 CRS (K.representative + (-D)) : ℤ) -
            (h0 CRS (K.representative + (-(D + Divisor.point p))) : ℤ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hdual_le)
  have hstep : (h0 CRS (D + Divisor.point p) : ℤ) - (h0 CRS D : ℤ) ≤ 1 := by
    linarith
  have hstep' : (h0 CRS (D + Divisor.point p) : ℤ) ≤ (h0 CRS D : ℤ) + 1 := by
    linarith
  exact_mod_cast hstep'

/-- h⁰(D + [p]) ≤ h⁰(D) + 1 from map-level five-term data plus finrank identifications. -/
theorem h0_add_point_upper_of_fiveTermMaps (CRS : CompactRiemannSurface)
    (K : CanonicalDivisor CRS)
    (D : Divisor CRS.toRiemannSurface) (p : CRS.toRiemannSurface.carrier)
    (hmap : EvalResidueFiveTermMaps CRS D p)
    (hids : EvalResidueFinrankIdentifications CRS K D p hmap) :
    h0 CRS (D + Divisor.point p) ≤ h0 CRS D + 1 := by
  have hdata : EvalResidueFiveTermData CRS K D p :=
    EvalResidueFiveTermMaps.toData CRS K D p hmap
      hids.hdim_V₁ hids.hdim_V₂ hids.hdim_V₄ hids.hdim_V₅
  exact h0_add_point_upper_of_fiveTermData CRS K D p hdata

/-- h⁰(D + [p]) ≤ h⁰(D) + 1 from split map-level existence assumptions. -/
theorem h0_add_point_upper_of_exists_fiveTermMaps_and_ids (CRS : CompactRiemannSurface)
    (K : CanonicalDivisor CRS)
    (D : Divisor CRS.toRiemannSurface) (p : CRS.toRiemannSurface.carrier)
    (hexMaps : Nonempty (EvalResidueFiveTermMaps CRS D p))
    (hexIds : ∀ hmap : EvalResidueFiveTermMaps CRS D p,
      Nonempty (EvalResidueFinrankIdentifications CRS K D p hmap)) :
    h0 CRS (D + Divisor.point p) ≤ h0 CRS D + 1 := by
  rcases hexMaps with ⟨hmap⟩
  rcases hexIds hmap with ⟨hids⟩
  exact h0_add_point_upper_of_fiveTermMaps CRS K D p hmap hids

/-- h⁰(D + [p]) ≤ h⁰(D) + 1.

    Any h⁰(D)+2 elements of L(D+[p]) include h⁰(D)+2 evaluation vectors
    in ℂ (one-dimensional), so at most one direction is "new" beyond L(D).

    **Proof sketch:**
    Given h⁰(D)+2 elements of L(D+[p]), the evaluation at p gives
    h⁰(D)+2 complex numbers. Some linear combination of these evaluations
    is zero (pigeonhole in 1D), giving an element of L(D). By maximality
    of h⁰(D), we can't have more than h⁰(D)+1 independent elements. -/
theorem h0_add_point_upper (CRS : CompactRiemannSurface)
    (D : Divisor CRS.toRiemannSurface) (p : CRS.toRiemannSurface.carrier) :
    h0 CRS (D + Divisor.point p) ≤ h0 CRS D + 1 := by
  obtain ⟨K⟩ := canonical_divisor_exists CRS
  rcases exists_evalResidueFiveTermMaps_and_ids CRS K D p with ⟨hmap, hids⟩
  exact h0_add_point_upper_of_fiveTermMaps CRS K D p hmap hids

/-- The full bound: h⁰(D) ≤ h⁰(D + [p]) ≤ h⁰(D) + 1. -/
theorem h0_add_point_bounds (CRS : CompactRiemannSurface)
    (D : Divisor CRS.toRiemannSurface) (p : CRS.toRiemannSurface.carrier) :
    (h0 CRS D : ℤ) ≤ (h0 CRS (D + Divisor.point p) : ℤ) ∧
    (h0 CRS (D + Divisor.point p) : ℤ) ≤ (h0 CRS D : ℤ) + 1 := by
  constructor
  · exact_mod_cast h0_mono CRS (le_add_point D p)
  · exact_mod_cast h0_add_point_upper CRS D p

/-!
## The Evaluation-Residue Complementarity

The deep result: the "evaluation jump" and "residue jump" sum to 1.

  [h⁰(D+[p]) - h⁰(D)] + [h⁰(K-D) - h⁰(K-D-[p])] = 1

This is equivalent to χ(D+[p]) = χ(D) + 1, which comes from the
long exact cohomology sequence. The proof requires Serre duality
or the residue pairing.

### Why the naive approach fails:

We can prove:
  - h⁰(D+[p]) - h⁰(D) ∈ {0, 1}  (evaluation map)
  - h⁰(K-D) - h⁰(K-D-[p]) ∈ {0, 1}  (same argument)

But showing the SUM is exactly 1 requires the deep connection
between L(D+[p])/L(D) and L(K-D)/L(K-D-[p]) via the residue
pairing. This is essentially Serre duality.
-/

end RiemannSurfaces.Analytic
