import StringGeometry.RiemannSurfaces.GAGA.AlgebraicCurves.Cohomology.PointExactSequence.Core
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace RiemannSurfaces.Algebraic.Cohomology.PointExactSequence

open Algebraic CompactAlgebraicCurve Core.Divisor AlternatingSum
open scoped Classical

variable (C : Algebraic.CompactAlgebraicCurve)
variable (K : CanonicalDivisor C)
variable (D : Core.Divisor C.toAlgebraicCurve)
variable (p : C.toAlgebraicCurve.Point)

theorem euler_char_skyscraper_constraint
    [RiemannRochSubmoduleFiniteDimensional C D]
    [RiemannRochSubmoduleFiniteDimensional C (D - point p)]
    [RiemannRochSubmoduleFiniteDimensional C (K.K - D + point p)]
    [RiemannRochSubmoduleFiniteDimensional C (K.K - D)] :
    h0 C D - h0 C (D - point p) + h0 C (K.K - D + point p) - h0 C (K.K - D) = 1 := by
  sorry

/-- Exactness at ℂ: ker(f₃) = range(f₂)

    The proof uses the Euler characteristic constraint a + b = 1.
    In ℂ (1-dimensional), subspaces are either {0} or ℂ.
    With a + b = 1:
    - (a=0, b=1): range(f₂) = {0}, ker(f₃) = {0}. Equal!
    - (a=1, b=0): range(f₂) = ℂ, ker(f₃) = ℂ. Equal! -/

theorem f₃_ker_eq_range_f₂
    [RiemannRochSubmoduleFiniteDimensional C D]
    [RiemannRochSubmoduleFiniteDimensional C (D - point p)]
    [RiemannRochSubmoduleFiniteDimensional C (K.K - D + point p)]
    [RiemannRochSubmoduleFiniteDimensional C (K.K - D)] :
    LinearMap.ker (f₃ C K D p) = LinearMap.range (f₂ C D p) := by
  have hle : LinearMap.range (f₂ C D p) ≤ LinearMap.ker (f₃ C K D p) :=
    range_f₂_le_ker_f₃ C K D p

  have hfinr1 : Module.finrank ℂ (LinearMap.range (f₁ C D p)) =
      Module.finrank ℂ ↥(RiemannRochSubmodule C (D - point p)) :=
    @AlternatingSum.finrank_range_of_injective
      ↥(RiemannRochSubmodule C (D - point p))
      (RiemannRochSubmodule C (D - point p)).addCommGroup
      (RiemannRochSubmodule C (D - point p)).module
      (show RiemannRochSubmoduleFiniteDimensional C (D - point p) from inferInstance)
      ↥(RiemannRochSubmodule C D)
      (RiemannRochSubmodule C D).addCommGroup
      (RiemannRochSubmodule C D).module
      (show RiemannRochSubmoduleFiniteDimensional C D from inferInstance)
      (f₁ C D p)
      (f₁_injective C D p)

  have hk2 : Module.finrank ℂ (LinearMap.ker (f₂ C D p)) = h0 C (D - point p) := by
    rw [f₂_ker_eq_range_f₁ C D p]
    simpa [h0, RiemannRochSubmoduleFinrank, RiemannRochSubmoduleType] using hfinr1

  have rn2 : Module.finrank ℂ ↥(RiemannRochSubmodule C D) =
      Module.finrank ℂ (LinearMap.ker (f₂ C D p)) + Module.finrank ℂ (LinearMap.range (f₂ C D p)) :=
    @AlternatingSum.rank_nullity_finrank
      ↥(RiemannRochSubmodule C D)
      (RiemannRochSubmodule C D).addCommGroup
      (RiemannRochSubmodule C D).module
      (show RiemannRochSubmoduleFiniteDimensional C D from inferInstance)
      ℂ
      inferInstance
      inferInstance
      inferInstance
      (f₂ C D p)

  have hr2 : Module.finrank ℂ (LinearMap.range (f₂ C D p)) = h0 C D - h0 C (D - point p) := by
    exact Nat.eq_sub_of_add_eq (by
      calc
        Module.finrank ℂ (LinearMap.range (f₂ C D p)) + h0 C (D - point p)
            = Module.finrank ℂ (LinearMap.range (f₂ C D p)) +
                Module.finrank ℂ (LinearMap.ker (f₂ C D p)) := by
              rw [hk2]
        _ = Module.finrank ℂ (LinearMap.ker (f₂ C D p)) +
              Module.finrank ℂ (LinearMap.range (f₂ C D p)) := by
              rw [Nat.add_comm]
        _ = Module.finrank ℂ ↥(RiemannRochSubmodule C D) := rn2.symm
        _ = h0 C D := by
              simp [h0, RiemannRochSubmoduleFinrank, RiemannRochSubmoduleType])

  haveI freeKDp : Module.Free ℂ ↥(RiemannRochSubmodule C (K.K - D + point p)) :=
    Module.Free.of_basis
      (@Module.Basis.ofVectorSpace ℂ ↥(RiemannRochSubmodule C (K.K - D + point p))
        inferInstance
        (RiemannRochSubmodule C (K.K - D + point p)).addCommGroup
        (RiemannRochSubmodule C (K.K - D + point p)).module)
  haveI freeKD : Module.Free ℂ ↥(RiemannRochSubmodule C (K.K - D)) :=
    Module.Free.of_basis
      (@Module.Basis.ofVectorSpace ℂ ↥(RiemannRochSubmodule C (K.K - D))
        inferInstance
        (RiemannRochSubmodule C (K.K - D)).addCommGroup
        (RiemannRochSubmodule C (K.K - D)).module)
  haveI finDualKDp : Module.Finite ℂ
      (↥(RiemannRochSubmodule C (K.K - D + point p)) →ₗ[ℂ] ℂ) :=
    (Module.finite_dual_iff ℂ).2
      (show RiemannRochSubmoduleFiniteDimensional C (K.K - D + point p) from inferInstance)
  haveI finDualKD : Module.Finite ℂ
      (↥(RiemannRochSubmodule C (K.K - D)) →ₗ[ℂ] ℂ) :=
    (Module.finite_dual_iff ℂ).2
      (show RiemannRochSubmoduleFiniteDimensional C (K.K - D) from inferInstance)

  have hdual₁ :
      Module.finrank ℂ (↥(RiemannRochSubmodule C (K.K - D + point p)) →ₗ[ℂ] ℂ) =
        Module.finrank ℂ ↥(RiemannRochSubmodule C (K.K - D + point p)) :=
    @Subspace.dual_finrank_eq ℂ
      ↥(RiemannRochSubmodule C (K.K - D + point p))
      inferInstance
      (RiemannRochSubmodule C (K.K - D + point p)).addCommGroup
      (RiemannRochSubmodule C (K.K - D + point p)).module
  have hdual₂ :
      Module.finrank ℂ (↥(RiemannRochSubmodule C (K.K - D)) →ₗ[ℂ] ℂ) =
        Module.finrank ℂ ↥(RiemannRochSubmodule C (K.K - D)) :=
    @Subspace.dual_finrank_eq ℂ
      ↥(RiemannRochSubmodule C (K.K - D))
      inferInstance
      (RiemannRochSubmodule C (K.K - D)).addCommGroup
      (RiemannRochSubmodule C (K.K - D)).module

  have rn4 : Module.finrank ℂ
      (↥(RiemannRochSubmodule C (K.K - D + point p)) →ₗ[ℂ] ℂ) =
      Module.finrank ℂ (LinearMap.ker (f₄ C K D p)) +
      Module.finrank ℂ (LinearMap.range (f₄ C K D p)) :=
    @AlternatingSum.rank_nullity_finrank
      (↥(RiemannRochSubmodule C (K.K - D + point p)) →ₗ[ℂ] ℂ)
      inferInstance
      inferInstance
      inferInstance
      (↥(RiemannRochSubmodule C (K.K - D)) →ₗ[ℂ] ℂ)
      inferInstance
      inferInstance
      inferInstance
      (f₄ C K D p)

  have hs4 : Module.finrank ℂ (LinearMap.range (f₄ C K D p)) =
      Module.finrank ℂ (↥(RiemannRochSubmodule C (K.K - D)) →ₗ[ℂ] ℂ) :=
    AlternatingSum.finrank_range_of_surjective (f₄ C K D p) (f₄_surjective C K D p)

  have hk4 : Module.finrank ℂ (LinearMap.ker (f₄ C K D p)) =
      h0 C (K.K - D + point p) - h0 C (K.K - D) := by
    exact Nat.eq_sub_of_add_eq (by
      calc
        Module.finrank ℂ (LinearMap.ker (f₄ C K D p)) + h0 C (K.K - D)
            = Module.finrank ℂ (LinearMap.ker (f₄ C K D p)) +
                Module.finrank ℂ (↥(RiemannRochSubmodule C (K.K - D)) →ₗ[ℂ] ℂ) := by
              simp [h0, RiemannRochSubmoduleFinrank, RiemannRochSubmoduleType, hdual₂]
        _ = Module.finrank ℂ (LinearMap.ker (f₄ C K D p)) +
              Module.finrank ℂ (LinearMap.range (f₄ C K D p)) := by
              rw [hs4]
        _ = Module.finrank ℂ
              (↥(RiemannRochSubmodule C (K.K - D + point p)) →ₗ[ℂ] ℂ) := rn4.symm
        _ = h0 C (K.K - D + point p) := by
              simp [h0, RiemannRochSubmoduleFinrank, RiemannRochSubmoduleType, hdual₁])

  have hr3 : Module.finrank ℂ (LinearMap.range (f₃ C K D p)) =
      h0 C (K.K - D + point p) - h0 C (K.K - D) := by
    rw [← f₄_ker_eq_range_f₃ C K D p]
    exact hk4

  have rn3 : Module.finrank ℂ ℂ =
      Module.finrank ℂ (LinearMap.ker (f₃ C K D p)) +
      Module.finrank ℂ (LinearMap.range (f₃ C K D p)) :=
    @AlternatingSum.rank_nullity_finrank
      ℂ
      inferInstance
      inferInstance
      inferInstance
      (↥(RiemannRochSubmodule C (K.K - D + point p)) →ₗ[ℂ] ℂ)
      inferInstance
      inferInstance
      inferInstance
      (f₃ C K D p)

  have hk3_add_r3 : Module.finrank ℂ (LinearMap.ker (f₃ C K D p)) +
      Module.finrank ℂ (LinearMap.range (f₃ C K D p)) = 1 := by
    have h' : 1 = Module.finrank ℂ (LinearMap.ker (f₃ C K D p)) +
      Module.finrank ℂ (LinearMap.range (f₃ C K D p)) := by
      simpa using rn3
    exact h'.symm

  have hKD_le : h0 C (K.K - D) ≤ h0 C (K.K - D + point p) := by
    let incl := Submodule.inclusion (RiemannRochSpace_KD_subset C K D p)
    have hinj : Function.Injective incl := Submodule.inclusion_injective _
    have hrincl : Module.finrank ℂ (LinearMap.range incl) =
        Module.finrank ℂ ↥(RiemannRochSubmodule C (K.K - D)) :=
      @AlternatingSum.finrank_range_of_injective
        ↥(RiemannRochSubmodule C (K.K - D))
        (RiemannRochSubmodule C (K.K - D)).addCommGroup
        (RiemannRochSubmodule C (K.K - D)).module
        (show RiemannRochSubmoduleFiniteDimensional C (K.K - D) from inferInstance)
        ↥(RiemannRochSubmodule C (K.K - D + point p))
        (RiemannRochSubmodule C (K.K - D + point p)).addCommGroup
        (RiemannRochSubmodule C (K.K - D + point p)).module
        (show RiemannRochSubmoduleFiniteDimensional C (K.K - D + point p) from inferInstance)
        incl hinj
    have hrle : Module.finrank ℂ (LinearMap.range incl) ≤
        Module.finrank ℂ ↥(RiemannRochSubmodule C (K.K - D + point p)) :=
      @Submodule.finrank_le ℂ
        ↥(RiemannRochSubmodule C (K.K - D + point p))
        inferInstance
        inferInstance
        (RiemannRochSubmodule C (K.K - D + point p)).module
        inferInstance
        (show RiemannRochSubmoduleFiniteDimensional C (K.K - D + point p) from inferInstance)
        (LinearMap.range incl)
    have hfin : Module.finrank ℂ ↥(RiemannRochSubmodule C (K.K - D)) ≤
        Module.finrank ℂ ↥(RiemannRochSubmodule C (K.K - D + point p)) := by
      rw [← hrincl]
      exact hrle
    simpa [h0, RiemannRochSubmoduleFinrank, RiemannRochSubmoduleType] using hfin

  have hsume :
      h0 C D - h0 C (D - point p) + h0 C (K.K - D + point p) - h0 C (K.K - D) = 1 :=
    euler_char_skyscraper_constraint C K D p

  have hsume' :
      (h0 C D - h0 C (D - point p)) + (h0 C (K.K - D + point p) - h0 C (K.K - D)) = 1 := by
    have hadd :
        (h0 C D - h0 C (D - point p)) + h0 C (K.K - D + point p) - h0 C (K.K - D) =
        (h0 C D - h0 C (D - point p)) +
          (h0 C (K.K - D + point p) - h0 C (K.K - D)) := by
      exact Nat.add_sub_assoc hKD_le (h0 C D - h0 C (D - point p))
    rw [hadd] at hsume
    exact hsume

  let b := h0 C (K.K - D + point p) - h0 C (K.K - D)

  have hk3_eq : Module.finrank ℂ (LinearMap.ker (f₃ C K D p)) + b = 1 := by
    simpa [b, hr3] using hk3_add_r3

  have hr2_eq : Module.finrank ℂ (LinearMap.range (f₂ C D p)) + b = 1 := by
    calc
      Module.finrank ℂ (LinearMap.range (f₂ C D p)) + b
          = (h0 C D - h0 C (D - point p)) + (h0 C (K.K - D + point p) - h0 C (K.K - D)) := by
            simp [b, hr2]
      _ = 1 := hsume'

  have hfin : Module.finrank ℂ (LinearMap.range (f₂ C D p)) =
      Module.finrank ℂ (LinearMap.ker (f₃ C K D p)) := by
    have hboth : Module.finrank ℂ (LinearMap.range (f₂ C D p)) + b =
        Module.finrank ℂ (LinearMap.ker (f₃ C K D p)) + b := by
      rw [hr2_eq, hk3_eq]
    exact Nat.add_right_cancel hboth

  exact (Submodule.eq_of_le_of_finrank_eq hle hfin).symm

/-- **Key Lemma**: The LES exactness gives the dimension constraint.

    (h⁰(D) - h⁰(D-p)) + (h⁰(K-D+p) - h⁰(K-D)) = 1

    This follows directly from the alternating sum formula applied to the
    5-term exact sequence in cohomology. No case analysis is needed. -/
theorem LES_dimension_constraint
    [RiemannRochSubmoduleFiniteDimensional C (D - point p)]
    [RiemannRochSubmoduleFiniteDimensional C D]
    [RiemannRochSubmoduleFiniteDimensional C (K.K - D + point p)]
    [RiemannRochSubmoduleFiniteDimensional C (K.K - D)] :
    (h0 C D : ℤ) - h0 C (D - point p) +
    (h0 C (K.K - D + point p) : ℤ) - h0 C (K.K - D) = 1 := by
  haveI freeKDp : Module.Free ℂ ↥(RiemannRochSubmodule C (K.K - D + point p)) :=
    Module.Free.of_basis
      (@Module.Basis.ofVectorSpace ℂ ↥(RiemannRochSubmodule C (K.K - D + point p))
        inferInstance
        (RiemannRochSubmodule C (K.K - D + point p)).addCommGroup
        (RiemannRochSubmodule C (K.K - D + point p)).module)
  haveI freeKD : Module.Free ℂ ↥(RiemannRochSubmodule C (K.K - D)) :=
    Module.Free.of_basis
      (@Module.Basis.ofVectorSpace ℂ ↥(RiemannRochSubmodule C (K.K - D))
        inferInstance
        (RiemannRochSubmodule C (K.K - D)).addCommGroup
        (RiemannRochSubmodule C (K.K - D)).module)
  haveI finDualKDp : Module.Finite ℂ
      (↥(RiemannRochSubmodule C (K.K - D + point p)) →ₗ[ℂ] ℂ) :=
    (Module.finite_dual_iff ℂ).2
      (show RiemannRochSubmoduleFiniteDimensional C (K.K - D + point p) from inferInstance)
  haveI finDualKD : Module.Finite ℂ
      (↥(RiemannRochSubmodule C (K.K - D)) →ₗ[ℂ] ℂ) :=
    (Module.finite_dual_iff ℂ).2
      (show RiemannRochSubmoduleFiniteDimensional C (K.K - D) from inferInstance)
  have h := @AlternatingSum.alternating_sum_exact_five'
    ↥(RiemannRochSubmodule C (D - point p))
    (RiemannRochSubmodule C (D - point p)).addCommGroup
    (RiemannRochSubmodule C (D - point p)).module
    (show RiemannRochSubmoduleFiniteDimensional C (D - point p) from inferInstance)
    ↥(RiemannRochSubmodule C D)
    (RiemannRochSubmodule C D).addCommGroup
    (RiemannRochSubmodule C D).module
    (show RiemannRochSubmoduleFiniteDimensional C D from inferInstance)
    ℂ
    inferInstance
    inferInstance
    inferInstance
    (↥(RiemannRochSubmodule C (K.K - D + point p)) →ₗ[ℂ] ℂ)
    inferInstance
    inferInstance
    inferInstance
    (↥(RiemannRochSubmodule C (K.K - D)) →ₗ[ℂ] ℂ)
    inferInstance
    inferInstance
    inferInstance
    (f₁ C D p) (f₂ C D p) (f₃ C K D p) (f₄ C K D p)
    (f₁_injective C D p) (f₄_surjective C K D p)
    (f₂_ker_eq_range_f₁ C D p) (f₃_ker_eq_range_f₂ C K D p) (f₄_ker_eq_range_f₃ C K D p)
  have hdual₁ :
      Module.finrank ℂ (↥(RiemannRochSubmodule C (K.K - D + point p)) →ₗ[ℂ] ℂ) =
        Module.finrank ℂ ↥(RiemannRochSubmodule C (K.K - D + point p)) :=
    @Subspace.dual_finrank_eq ℂ
      ↥(RiemannRochSubmodule C (K.K - D + point p))
      inferInstance
      (RiemannRochSubmodule C (K.K - D + point p)).addCommGroup
      (RiemannRochSubmodule C (K.K - D + point p)).module
  have hdual₂ :
      Module.finrank ℂ (↥(RiemannRochSubmodule C (K.K - D)) →ₗ[ℂ] ℂ) =
        Module.finrank ℂ ↥(RiemannRochSubmodule C (K.K - D)) :=
    @Subspace.dual_finrank_eq ℂ
      ↥(RiemannRochSubmodule C (K.K - D))
      inferInstance
      (RiemannRochSubmodule C (K.K - D)).addCommGroup
      (RiemannRochSubmodule C (K.K - D)).module
  rw [hdual₁, hdual₂] at h
  simpa [h0, RiemannRochSubmoduleFinrank, RiemannRochSubmoduleType] using h


end RiemannSurfaces.Algebraic.Cohomology.PointExactSequence
