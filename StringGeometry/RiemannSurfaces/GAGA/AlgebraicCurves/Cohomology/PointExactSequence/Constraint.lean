import StringGeometry.RiemannSurfaces.GAGA.AlgebraicCurves.Cohomology.PointExactSequence.Core

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
  sorry


end RiemannSurfaces.Algebraic.Cohomology.PointExactSequence
