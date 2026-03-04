import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Dimension Identities for Exact Sequences (Analytic Helpers)

Reusable finite-dimensional linear algebra lemmas for five-term exact sequences:
`0 → V₁ → V₂ → V₃ → V₄ → V₅ → 0`.

These are used in the analytic Riemann-Roch point-step, where `V₃ = ℂ`.
-/

namespace RiemannSurfaces.Analytic

open Module FiniteDimensional

variable {k : Type*} [DivisionRing k]
variable {V₁ V₂ V₃ V₄ V₅ : Type*}
variable [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄] [AddCommGroup V₅]
variable [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄] [Module k V₅]

/-- Alternating-sum dimension identity for a five-term exact sequence. -/
theorem alternating_sum_exact_five
    (f₁ : V₁ →ₗ[k] V₂) (f₂ : V₂ →ₗ[k] V₃) (f₃ : V₃ →ₗ[k] V₄) (f₄ : V₄ →ₗ[k] V₅)
    [FiniteDimensional k V₁] [FiniteDimensional k V₂] [FiniteDimensional k V₃]
    [FiniteDimensional k V₄] [FiniteDimensional k V₅]
    (inj_f₁ : Function.Injective f₁)
    (exact_V₂ : LinearMap.ker f₂ = LinearMap.range f₁)
    (exact_V₃ : LinearMap.ker f₃ = LinearMap.range f₂)
    (exact_V₄ : LinearMap.ker f₄ = LinearMap.range f₃)
    (surj_f₄ : Function.Surjective f₄) :
    (finrank k V₁ : ℤ) - finrank k V₂ + finrank k V₃ - finrank k V₄ + finrank k V₅ = 0 := by
  have h1 : finrank k (LinearMap.range f₁) = finrank k V₁ :=
    LinearMap.finrank_range_of_inj inj_f₁
  have h2 : finrank k (LinearMap.ker f₂) = finrank k V₁ := by
    rw [exact_V₂, h1]
  have rn2 : finrank k V₂ = finrank k (LinearMap.ker f₂) + finrank k (LinearMap.range f₂) := by
    have h := LinearMap.finrank_range_add_finrank_ker f₂
    omega
  have h3 : finrank k (LinearMap.range f₂) = finrank k V₂ - finrank k V₁ := by
    rw [h2] at rn2; omega
  have h4 : finrank k (LinearMap.ker f₃) = finrank k V₂ - finrank k V₁ := by
    rw [exact_V₃, h3]
  have rn3 : finrank k V₃ = finrank k (LinearMap.ker f₃) + finrank k (LinearMap.range f₃) := by
    have h := LinearMap.finrank_range_add_finrank_ker f₃
    omega
  have h5 : finrank k (LinearMap.range f₃) = finrank k V₃ - (finrank k V₂ - finrank k V₁) := by
    rw [h4] at rn3; omega
  have h6 : finrank k (LinearMap.ker f₄) = finrank k V₃ - (finrank k V₂ - finrank k V₁) := by
    rw [exact_V₄, h5]
  have h7 : finrank k (LinearMap.range f₄) = finrank k V₅ := by
    rw [LinearMap.range_eq_top.mpr surj_f₄]
    exact finrank_top k V₅
  have rn4 : finrank k V₄ = finrank k (LinearMap.ker f₄) + finrank k (LinearMap.range f₄) := by
    have h := LinearMap.finrank_range_add_finrank_ker f₄
    omega
  have h8 : finrank k V₄ = finrank k V₃ - (finrank k V₂ - finrank k V₁) + finrank k V₅ := by
    rw [h6, h7] at rn4
    exact rn4
  omega

/-- Rearranged exact-sequence identity in integer form. -/
theorem complementarity_exact_five_int
    (f₁ : V₁ →ₗ[k] V₂) (f₂ : V₂ →ₗ[k] V₃) (f₃ : V₃ →ₗ[k] V₄) (f₄ : V₄ →ₗ[k] V₅)
    [FiniteDimensional k V₁] [FiniteDimensional k V₂] [FiniteDimensional k V₃]
    [FiniteDimensional k V₄] [FiniteDimensional k V₅]
    (inj_f₁ : Function.Injective f₁)
    (exact_V₂ : LinearMap.ker f₂ = LinearMap.range f₁)
    (exact_V₃ : LinearMap.ker f₃ = LinearMap.range f₂)
    (exact_V₄ : LinearMap.ker f₄ = LinearMap.range f₃)
    (surj_f₄ : Function.Surjective f₄) :
    (finrank k V₂ : ℤ) - finrank k V₁ + ((finrank k V₄ : ℤ) - finrank k V₅) =
      finrank k V₃ := by
  have h := alternating_sum_exact_five f₁ f₂ f₃ f₄ inj_f₁ exact_V₂ exact_V₃ exact_V₄ surj_f₄
  omega

/-- If the middle term has dimension `1`, the two jumps add to `1`. -/
theorem complementarity_exact_five_dim_one
    (f₁ : V₁ →ₗ[k] V₂) (f₂ : V₂ →ₗ[k] V₃) (f₃ : V₃ →ₗ[k] V₄) (f₄ : V₄ →ₗ[k] V₅)
    [FiniteDimensional k V₁] [FiniteDimensional k V₂] [FiniteDimensional k V₃]
    [FiniteDimensional k V₄] [FiniteDimensional k V₅]
    (inj_f₁ : Function.Injective f₁)
    (exact_V₂ : LinearMap.ker f₂ = LinearMap.range f₁)
    (exact_V₃ : LinearMap.ker f₃ = LinearMap.range f₂)
    (exact_V₄ : LinearMap.ker f₄ = LinearMap.range f₃)
    (surj_f₄ : Function.Surjective f₄)
    (hV₃ : finrank k V₃ = 1) :
    (finrank k V₂ : ℤ) - finrank k V₁ + ((finrank k V₄ : ℤ) - finrank k V₅) = 1 := by
  have h := complementarity_exact_five_int f₁ f₂ f₃ f₄ inj_f₁ exact_V₂ exact_V₃ exact_V₄ surj_f₄
  rw [h]
  exact_mod_cast hV₃

end RiemannSurfaces.Analytic
