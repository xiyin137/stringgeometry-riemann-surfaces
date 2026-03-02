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
  sorry

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
