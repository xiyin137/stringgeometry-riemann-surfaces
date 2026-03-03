import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.LinearAlgebra.Complex.Module
import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.Infrastructure.RealSmoothness

/-!
# Wirtinger Derivatives

This file develops the theory of Wirtinger derivatives, providing the key connection
between ℝ-differentiability and ℂ-differentiability needed for the ∂̄-operator.

## Mathematical Background

For a function f : ℂ → ℂ that is ℝ-differentiable at z, we define the Wirtinger derivatives:
  ∂f/∂z = (1/2)(∂f/∂x - i ∂f/∂y)
  ∂f/∂z̄ = (1/2)(∂f/∂x + i ∂f/∂y)

Equivalently, using the Fréchet derivative L = fderiv ℝ f z : ℂ →L[ℝ] ℂ:
  ∂f/∂z  = (1/2)(L(1) - i·L(i))
  ∂f/∂z̄ = (1/2)(L(1) + i·L(i))

**Key theorem**: f is ℂ-differentiable at z iff ∂f/∂z̄ = 0 (Cauchy-Riemann equations).

When f is ℂ-differentiable, ∂f/∂z equals the complex derivative deriv f z.

## Main Definitions

* `wirtingerDeriv` - The holomorphic derivative ∂/∂z
* `wirtingerDerivBar` - The antiholomorphic derivative ∂/∂z̄

## Main Results

* `holomorphic_iff_wirtingerDerivBar_zero` - f is ℂ-differentiable iff ∂f/∂z̄ = 0
* `wirtingerDeriv_eq_deriv` - When ℂ-differentiable, ∂f/∂z = deriv f z
* `wirtinger_add`, `wirtinger_mul`, etc. - Algebraic properties

## References

* Ahlfors, "Complex Analysis", Chapter 1
* Griffiths-Harris, "Principles of Algebraic Geometry", §0.5
-/

namespace RiemannSurfaces.Analytic.Infrastructure

open Complex

-- The `module` keyword in Mathlib's FDeriv files can block instance synthesis for
-- SMulCommClass ℝ ℂ ℂ (which should come from Algebra.to_smulCommClass).
-- We provide it explicitly here, constructing from commutativity of ℂ.
instance instSMulCommClassRealComplexComplex : SMulCommClass ℝ ℂ ℂ :=
  ⟨fun r c x => by
    simp only [smul_eq_mul]
    exact mul_left_comm (↑r) c x⟩

-- Similarly, IsScalarTower ℝ ℂ ℂ and CompatibleSMul ℂ ℂ ℝ ℂ are blocked by the same
-- module keyword issue. Provide them explicitly.
instance instIsScalarTowerRealComplexComplex : IsScalarTower ℝ ℂ ℂ where
  smul_assoc r c x := by
    simp only [Algebra.smul_def, Algebra.algebraMap_self_apply, mul_assoc]

/-- Left multiplication by c as an ℝ-continuous linear map.
    Used to bypass `fderiv_const_smul` which needs the unsynthesizable
    `Module ℂ (ℂ →L[ℝ] ℂ)` instance in this Lean/Mathlib version. -/
private def mulLeftCLM (c : ℂ) : ℂ →L[ℝ] ℂ where
  toFun := (c * ·)
  map_add' := mul_add c
  map_smul' := fun r w => by
    simp only [RingHom.id_apply]
    exact Algebra.mul_smul_comm r c w

/-!
## Wirtinger Derivatives via Fréchet Derivative

For an ℝ-differentiable function f : ℂ → ℂ, the ℝ-linear Fréchet derivative
L = fderiv ℝ f z can be uniquely decomposed as:
  L(w) = A·w + B·conj(w)
where A, B ∈ ℂ. We have:
  A = ∂f/∂z = (1/2)(L(1) - i·L(i))
  B = ∂f/∂z̄ = (1/2)(L(1) + i·L(i))

The function f is ℂ-differentiable iff B = 0.
-/

/-- The Wirtinger derivative ∂f/∂z = (1/2)(L(1) - i·L(i)) where L = fderiv ℝ f z.
    This is the holomorphic part of the derivative. When f is ℂ-differentiable,
    this equals deriv f z. -/
noncomputable def wirtingerDeriv (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1/2 : ℂ) * (fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I)

/-- The Wirtinger derivative ∂f/∂z̄ = (1/2)(L(1) + i·L(i)) where L = fderiv ℝ f z.
    This is the antiholomorphic part of the derivative.
    A function is holomorphic iff this vanishes. -/
noncomputable def wirtingerDerivBar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1/2 : ℂ) * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I)

/-- `wirtingerDerivBar` is invariant under eventual equality in a neighborhood. -/
theorem wirtingerDerivBar_congr_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ}
    (hfg : f =ᶠ[nhds z] g) :
    wirtingerDerivBar f z = wirtingerDerivBar g z := by
  unfold wirtingerDerivBar
  rw [hfg.fderiv_eq]

/-- `wirtingerDeriv` is invariant under eventual equality in a neighborhood. -/
theorem wirtingerDeriv_congr_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ}
    (hfg : f =ᶠ[nhds z] g) :
    wirtingerDeriv f z = wirtingerDeriv g z := by
  unfold wirtingerDeriv
  rw [hfg.fderiv_eq]

/-!
## The Fundamental Characterization Theorem

The key result: f is ℂ-differentiable iff ∂f/∂z̄ = 0.
-/

/-- Helper: The Cauchy-Riemann condition L(I) = I·L(1) is equivalent to ∂f/∂z̄ = 0. -/
theorem wirtingerDerivBar_eq_zero_iff_cauchyRiemann {f : ℂ → ℂ} {z : ℂ}
    (_hf : DifferentiableAt ℝ f z) :
    wirtingerDerivBar f z = 0 ↔ fderiv ℝ f z Complex.I = Complex.I • fderiv ℝ f z 1 := by
  unfold wirtingerDerivBar
  constructor
  · intro h
    -- From (1/2)(L(1) + I·L(I)) = 0, we get L(1) + I·L(I) = 0
    have h' : fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I = 0 := by
      have := h
      simp only [one_div, mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or] at this
      exact this
    -- From L(1) + I·L(I) = 0, get I·L(I) = -L(1)
    have h'' : Complex.I * fderiv ℝ f z Complex.I = -fderiv ℝ f z 1 := by
      calc Complex.I * fderiv ℝ f z Complex.I
        _ = (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) - fderiv ℝ f z 1 := by ring
        _ = 0 - fderiv ℝ f z 1 := by rw [h']
        _ = -fderiv ℝ f z 1 := by ring
    -- L(I) = (I * L(I)) / I = -L(1) / I
    have hIinv : Complex.I⁻¹ = -Complex.I := by
      have hIsq : Complex.I * Complex.I = -1 := Complex.I_mul_I
      field_simp
      calc 1 = -(-1) := by ring
        _ = -(Complex.I * Complex.I) := by rw [hIsq]
        _ = -Complex.I ^ 2 := by ring
    have hne : Complex.I ≠ 0 := Complex.I_ne_zero
    calc fderiv ℝ f z Complex.I
      _ = Complex.I⁻¹ * (Complex.I * fderiv ℝ f z Complex.I) := by field_simp
      _ = Complex.I⁻¹ * (-fderiv ℝ f z 1) := by rw [h'']
      _ = (-Complex.I) * (-fderiv ℝ f z 1) := by rw [hIinv]
      _ = Complex.I * fderiv ℝ f z 1 := by ring
      _ = Complex.I • fderiv ℝ f z 1 := by rw [smul_eq_mul]
  · intro hCR
    -- From L(I) = I·L(1), compute I·L(I) = I·I·L(1) = -L(1)
    have hIsq : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have h' : Complex.I * fderiv ℝ f z Complex.I = -fderiv ℝ f z 1 := by
      rw [hCR, smul_eq_mul]
      calc Complex.I * (Complex.I * fderiv ℝ f z 1)
        _ = (Complex.I * Complex.I) * fderiv ℝ f z 1 := by ring
        _ = (-1) * fderiv ℝ f z 1 := by rw [hIsq]
        _ = -fderiv ℝ f z 1 := by ring
    simp only [one_div, mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
    calc fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I
      _ = fderiv ℝ f z 1 + (-fderiv ℝ f z 1) := by rw [h']
      _ = 0 := by ring

/-- **The fundamental theorem**: A function is ℂ-differentiable iff it is ℝ-differentiable
    and its Wirtinger derivative ∂f/∂z̄ vanishes. -/
theorem holomorphic_iff_wirtingerDerivBar_zero {f : ℂ → ℂ} {z : ℂ} :
    DifferentiableAt ℂ f z ↔ DifferentiableAt ℝ f z ∧ wirtingerDerivBar f z = 0 := by
  rw [differentiableAt_complex_iff_differentiableAt_real]
  constructor
  · intro ⟨hR, hCR⟩
    exact ⟨hR, (wirtingerDerivBar_eq_zero_iff_cauchyRiemann hR).mpr hCR⟩
  · intro ⟨hR, hBar⟩
    exact ⟨hR, (wirtingerDerivBar_eq_zero_iff_cauchyRiemann hR).mp hBar⟩

/-- When f is ℂ-differentiable, ∂f/∂z equals the complex derivative. -/
theorem wirtingerDeriv_eq_deriv {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    wirtingerDeriv f z = deriv f z := by
  -- Expand the definition without introducing let-binding
  show (1/2 : ℂ) * (fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I) = deriv f z
  -- The key is that ℂ-differentiability implies the Cauchy-Riemann equation
  -- L(I) = I * L(1) where L = fderiv ℝ f z
  have hCR : fderiv ℝ f z Complex.I = Complex.I • fderiv ℝ f z 1 := by
    rw [differentiableAt_complex_iff_differentiableAt_real] at hf
    exact hf.2
  -- From Cauchy-Riemann: L(1) - I * L(I) = L(1) - I * (I * L(1)) = 2 * L(1)
  have hIsq : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [hCR, smul_eq_mul]
  -- wirtingerDeriv = (1/2)(L(1) - I * I * L(1)) = (1/2)(2 * L(1)) = L(1)
  calc (1/2 : ℂ) * (fderiv ℝ f z 1 - Complex.I * (Complex.I * fderiv ℝ f z 1))
    _ = (1/2 : ℂ) * (fderiv ℝ f z 1 - (Complex.I * Complex.I) * fderiv ℝ f z 1) := by ring
    _ = (1/2 : ℂ) * (fderiv ℝ f z 1 - (-1) * fderiv ℝ f z 1) := by rw [hIsq]
    _ = fderiv ℝ f z 1 := by ring
    _ = deriv f z := by
        -- fderiv ℝ f z 1 = deriv f z when f is ℂ-differentiable
        -- Use that fderiv ℝ f z = (fderiv ℂ f z).restrictScalars ℝ
        -- and (fderiv ℂ f z) 1 = deriv f z
        rw [@DifferentiableAt.fderiv_restrictScalars ℝ _ ℂ _ _ ℂ _ _ _
            IsScalarTower.right ℂ _ _ _ IsScalarTower.right _ _ hf]
        exact fderiv_apply_one_eq_deriv

/-!
## Algebraic Properties of Wirtinger Derivatives
-/

section Algebraic

variable {f g : ℂ → ℂ} {z : ℂ}

/-- Wirtinger derivative of sum. -/
theorem wirtingerDeriv_add (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtingerDeriv (f + g) z = wirtingerDeriv f z + wirtingerDeriv g z := by
  unfold wirtingerDeriv
  rw [fderiv_add hf hg]
  simp only [ContinuousLinearMap.add_apply]
  ring

/-- Wirtinger bar derivative of sum. -/
theorem wirtingerDerivBar_add (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtingerDerivBar (f + g) z = wirtingerDerivBar f z + wirtingerDerivBar g z := by
  unfold wirtingerDerivBar
  rw [fderiv_add hf hg]
  simp only [ContinuousLinearMap.add_apply]
  ring

/-- Helper: For a constant c and ℝ-differentiable f, fderiv of c * f applied to v.
    Uses `mulLeftCLM` composition to avoid `fderiv_const_smul` which needs
    the unsynthesizable `Module ℂ (ℂ →L[ℝ] ℂ)`. -/
private theorem fderiv_const_mul_apply' {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (c : ℂ) (v : ℂ) :
    fderiv ℝ (fun w => c * f w) z v = c * fderiv ℝ f z v := by
  -- Express c * f w as composition: mulLeftCLM(c) ∘ f
  have key : fderiv ℝ (fun w => c * f w) z = (mulLeftCLM c).comp (fderiv ℝ f z) := by
    have h := ((mulLeftCLM c).hasFDerivAt.comp z hf.hasFDerivAt).fderiv
    rwa [show (↑(mulLeftCLM c) ∘ f) = (fun w => c * f w) from rfl] at h
  rw [key]; rfl

/-- Wirtinger derivative of constant multiple. -/
theorem wirtingerDeriv_const_smul (c : ℂ) (hf : DifferentiableAt ℝ f z) :
    wirtingerDeriv (c • f) z = c * wirtingerDeriv f z := by
  -- c • f = fun w => c * f w
  show wirtingerDeriv (fun w => c * f w) z = c * wirtingerDeriv f z
  show (1/2 : ℂ) * (fderiv ℝ (fun w => c * f w) z 1 -
    Complex.I * fderiv ℝ (fun w => c * f w) z Complex.I) =
    c * ((1/2 : ℂ) * (fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I))
  rw [fderiv_const_mul_apply' hf, fderiv_const_mul_apply' hf]; ring

/-- Wirtinger bar derivative of constant multiple. -/
theorem wirtingerDerivBar_const_smul (c : ℂ) (hf : DifferentiableAt ℝ f z) :
    wirtingerDerivBar (c • f) z = c * wirtingerDerivBar f z := by
  show wirtingerDerivBar (fun w => c * f w) z = c * wirtingerDerivBar f z
  show (1/2 : ℂ) * (fderiv ℝ (fun w => c * f w) z 1 +
    Complex.I * fderiv ℝ (fun w => c * f w) z Complex.I) =
    c * ((1/2 : ℂ) * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I))
  rw [fderiv_const_mul_apply' hf, fderiv_const_mul_apply' hf]; ring

/-- Wirtinger derivative of negation. -/
theorem wirtingerDeriv_neg :
    wirtingerDeriv (-f) z = -wirtingerDeriv f z := by
  unfold wirtingerDeriv
  simp only [fderiv_neg, ContinuousLinearMap.neg_apply]
  ring

/-- Wirtinger bar derivative of negation. -/
theorem wirtingerDerivBar_neg :
    wirtingerDerivBar (-f) z = -wirtingerDerivBar f z := by
  unfold wirtingerDerivBar
  simp only [fderiv_neg, ContinuousLinearMap.neg_apply]
  ring

/-- Wirtinger derivative of constant function. -/
theorem wirtingerDeriv_const (c : ℂ) : wirtingerDeriv (fun _ => c) z = 0 := by
  unfold wirtingerDeriv
  have heq : (fun _ : ℂ => c) = Function.const ℂ c := rfl
  rw [heq, fderiv_const]
  simp

/-- Wirtinger bar derivative of constant function. -/
theorem wirtingerDerivBar_const (c : ℂ) : wirtingerDerivBar (fun _ => c) z = 0 := by
  unfold wirtingerDerivBar
  have heq : (fun _ : ℂ => c) = Function.const ℂ c := rfl
  rw [heq, fderiv_const]
  simp

/-- Wirtinger derivative of identity. -/
theorem wirtingerDeriv_id : wirtingerDeriv id z = 1 := by
  unfold wirtingerDeriv
  rw [fderiv_id]
  simp only [ContinuousLinearMap.id_apply]
  have hIsq : Complex.I * Complex.I = -1 := Complex.I_mul_I
  calc (1 : ℂ) / 2 * (1 - Complex.I * Complex.I)
    _ = 1 / 2 * (1 - (-1)) := by rw [hIsq]
    _ = 1 / 2 * 2 := by ring
    _ = 1 := by ring

/-- Wirtinger bar derivative of identity vanishes (identity is holomorphic). -/
theorem wirtingerDerivBar_id : wirtingerDerivBar id z = 0 := by
  unfold wirtingerDerivBar
  rw [fderiv_id]
  simp only [ContinuousLinearMap.id_apply]
  have hIsq : Complex.I * Complex.I = -1 := Complex.I_mul_I
  calc (1 : ℂ) / 2 * (1 + Complex.I * Complex.I)
    _ = 1 / 2 * (1 + (-1)) := by rw [hIsq]
    _ = 0 := by ring

/-- Value-level product rule for fderiv, bypassing `fderiv_mul`'s `<•` (RightActions) notation
    which requires the unsynthesizable `Module ℂ (ℂ →L[ℝ] ℂ)`.
    Uses `IsBoundedBilinearMap` for multiplication composed via chain rule. -/
private theorem fderiv_mul_apply (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z)
    (v : ℂ) :
    fderiv ℝ (fun w => f w * g w) z v = f z * fderiv ℝ g z v + fderiv ℝ f z v * g z := by
  have B := isBoundedBilinearMap_mul (𝕜 := ℝ) (A := ℂ)
  -- Compute fderiv at the CLM level first, then evaluate at v
  have key : fderiv ℝ (fun w => f w * g w) z =
      (B.deriv (f z, g z)).comp ((fderiv ℝ f z).prod (fderiv ℝ g z)) := by
    have hfg := DifferentiableAt.prodMk hf hg
    rw [show (fun w => f w * g w) = (fun p : ℂ × ℂ => p.1 * p.2) ∘ (fun w => (f w, g w)) from rfl,
        fderiv_comp z (B.differentiableAt _) hfg,
        B.fderiv, DifferentiableAt.fderiv_prodMk hf hg]
  rw [key, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
  simp [IsBoundedBilinearMap.deriv_apply]

/-- Product rule for Wirtinger derivatives (Leibniz rule).
    This is the standard product rule: ∂(fg)/∂z = (∂f/∂z)g + f(∂g/∂z). -/
theorem wirtingerDeriv_mul (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtingerDeriv (f * g) z = wirtingerDeriv f z * g z + f z * wirtingerDeriv g z := by
  show wirtingerDeriv (fun w => f w * g w) z = _
  unfold wirtingerDeriv
  simp only [fderiv_mul_apply hf hg]
  ring

/-- Product rule for Wirtinger bar derivatives (Leibniz rule).
    This is the standard product rule: ∂(fg)/∂z̄ = (∂f/∂z̄)g + f(∂g/∂z̄). -/
theorem wirtingerDerivBar_mul (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtingerDerivBar (f * g) z = wirtingerDerivBar f z * g z + f z * wirtingerDerivBar g z := by
  show wirtingerDerivBar (fun w => f w * g w) z = _
  unfold wirtingerDerivBar
  simp only [fderiv_mul_apply hf hg]
  ring

/-- Simplified product rule when both functions are holomorphic. -/
theorem wirtingerDeriv_mul_holomorphic
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z) :
    wirtingerDeriv (f * g) z = wirtingerDeriv f z * g z + f z * wirtingerDeriv g z := by
  rw [wirtingerDeriv_eq_deriv hf, wirtingerDeriv_eq_deriv hg,
      wirtingerDeriv_eq_deriv (hf.mul hg)]
  exact deriv_mul hf hg

end Algebraic

/-!
## Wirtinger Derivatives of Special Functions
-/

/-- Wirtinger derivative of conjugation: ∂(conj)/∂z = 0.
    Conjugation is antiholomorphic, not holomorphic. -/
theorem wirtingerDeriv_conj : wirtingerDeriv (starRingEnd ℂ) z = 0 := by
  unfold wirtingerDeriv
  have h : fderiv ℝ (starRingEnd ℂ : ℂ → ℂ) z = RiemannSurfaces.Analytic.conjCLM := by
    apply HasFDerivAt.fderiv
    exact RiemannSurfaces.Analytic.conjCLM.hasFDerivAt
  rw [h]
  -- conjCLM = conjCLE.toContinuousLinearMap; use erw to handle coercion
  have h1 : (RiemannSurfaces.Analytic.conjCLM : ℂ →L[ℝ] ℂ) 1 = 1 := by
    show Complex.conjCLE.toContinuousLinearMap 1 = 1
    erw [conjCLE_apply]; simp
  have hI : (RiemannSurfaces.Analytic.conjCLM : ℂ →L[ℝ] ℂ) Complex.I = -Complex.I := by
    show Complex.conjCLE.toContinuousLinearMap Complex.I = -Complex.I
    erw [conjCLE_apply]; exact Complex.conj_I
  rw [h1, hI]
  have : Complex.I * -Complex.I = 1 := by rw [mul_neg, Complex.I_mul_I, neg_neg]
  rw [this]; ring

/-- Wirtinger bar derivative of conjugation: ∂(conj)/∂z̄ = 1.
    This shows conjugation is a "purely antiholomorphic" function. -/
theorem wirtingerDerivBar_conj : wirtingerDerivBar (starRingEnd ℂ) z = 1 := by
  unfold wirtingerDerivBar
  have h : fderiv ℝ (starRingEnd ℂ : ℂ → ℂ) z = RiemannSurfaces.Analytic.conjCLM := by
    apply HasFDerivAt.fderiv
    exact RiemannSurfaces.Analytic.conjCLM.hasFDerivAt
  rw [h]
  have h1 : (RiemannSurfaces.Analytic.conjCLM : ℂ →L[ℝ] ℂ) 1 = 1 := by
    show Complex.conjCLE.toContinuousLinearMap 1 = 1
    erw [conjCLE_apply]; simp
  have hI : (RiemannSurfaces.Analytic.conjCLM : ℂ →L[ℝ] ℂ) Complex.I = -Complex.I := by
    show Complex.conjCLE.toContinuousLinearMap Complex.I = -Complex.I
    erw [conjCLE_apply]; exact Complex.conj_I
  rw [h1, hI]
  have : Complex.I * -Complex.I = 1 := by rw [mul_neg, Complex.I_mul_I, neg_neg]
  rw [this]; ring

/-- For a ℂ-differentiable function, construct HasFDerivAt over ℝ directly,
    bypassing restrictScalars (which has an instance diamond with the `module` keyword). -/
private theorem hasFDerivAt_real_of_complex {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z) :
    HasFDerivAt (𝕜 := ℝ) g (mulLeftCLM (deriv g z)) z := by
  -- Key: mulLeftCLM (deriv g z) and fderiv ℂ g z agree pointwise
  have heq : ∀ h : ℂ, mulLeftCLM (deriv g z) h = (fderiv ℂ g z) h := by
    intro h
    show (deriv g z) * h = (fderiv ℂ g z) h
    have : (fderiv ℂ g z) h = h * deriv g z := by
      have hsm := (fderiv ℂ g z).map_smul h (1 : ℂ)
      simp only [smul_eq_mul, mul_one] at hsm
      rw [hsm, fderiv_apply_one_eq_deriv]
    rw [this, mul_comm]
  -- Transfer the isLittleO condition (HasFDerivAt uses pairs p.1, p.2 in this Mathlib version)
  show HasFDerivAtFilter g (mulLeftCLM (deriv g z)) (nhds z ×ˢ pure z)
  refine HasFDerivAtFilter.of_isLittleO ?_
  have key : ∀ p : ℂ × ℂ,
      g p.1 - g p.2 - mulLeftCLM (deriv g z) (p.1 - p.2) =
      g p.1 - g p.2 - (fderiv ℂ g z) (p.1 - p.2) := fun p => by rw [heq]
  simp_rw [key]
  exact HasFDerivAtFilter.isLittleO hg.hasFDerivAt

/-- ℂ-differentiable implies ℝ-differentiable (bypasses restrictScalars diamond). -/
private theorem differentiableAt_real_of_complex {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z) : DifferentiableAt ℝ g z :=
  (hasFDerivAt_real_of_complex hg).differentiableAt

/-- For ℂ-differentiable g, fderiv ℝ g z = mulLeftCLM (deriv g z). -/
private theorem fderiv_real_eq_mulLeftCLM {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z) :
    fderiv ℝ g z = mulLeftCLM (deriv g z) :=
  (hasFDerivAt_real_of_complex hg).fderiv

/-- Algebraic identity for evaluating an ℝ-linear map on a complex number and its
`I`-multiple. This is the core linear-algebra step behind the chain rule for
`wirtingerDerivBar` under holomorphic reparametrization. -/
private theorem clm_eval_add_I_eval_I_mul_conj
    (L : ℂ →L[ℝ] ℂ) (a : ℂ) :
    L a + Complex.I * L (Complex.I * a) =
      (L 1 + Complex.I * L Complex.I) * (starRingEnd ℂ a) := by
  have ha :
      a = (a.re : ℝ) • (1 : ℂ) + (a.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  have hIa :
      Complex.I * a =
        (-a.im : ℝ) • (1 : ℂ) + (a.re : ℝ) • Complex.I := by
    rw [ha]
    apply Complex.ext <;> simp
  have hLa :
      L a = (a.re : ℝ) • L 1 + (a.im : ℝ) • L Complex.I := by
    calc
      L a = L ((a.re : ℝ) • (1 : ℂ) + (a.im : ℝ) • Complex.I) := by
        exact congrArg L ha
      _ = L ((a.re : ℝ) • (1 : ℂ)) + L ((a.im : ℝ) • Complex.I) := by rw [map_add]
      _ = (a.re : ℝ) • L 1 + (a.im : ℝ) • L Complex.I := by rw [map_smul, map_smul]
  have hLIa :
      L (Complex.I * a) =
        (-a.im : ℝ) • L 1 + (a.re : ℝ) • L Complex.I := by
    calc
      L (Complex.I * a) = L ((-a.im : ℝ) • (1 : ℂ) + (a.re : ℝ) • Complex.I) := by
        exact congrArg L hIa
      _ = L ((-a.im : ℝ) • (1 : ℂ)) + L ((a.re : ℝ) • Complex.I) := by rw [map_add]
      _ = (-a.im : ℝ) • L 1 + (a.re : ℝ) • L Complex.I := by rw [map_smul, map_smul]
  have hconj :
      (starRingEnd ℂ a) = (a.re : ℝ) • (1 : ℂ) + (-a.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  rw [hLa, hLIa, hconj]
  apply Complex.ext <;> simp [mul_add, add_mul, Complex.mul_re, Complex.mul_im] <;> ring

/-- Algebraic identity for evaluating an ℝ-linear map on a complex number and its
`I`-multiple, isolating the holomorphic (`∂`) part. -/
private theorem clm_eval_sub_I_eval_I_mul
    (L : ℂ →L[ℝ] ℂ) (a : ℂ) :
    L a - Complex.I * L (Complex.I * a) =
      (L 1 - Complex.I * L Complex.I) * a := by
  have ha :
      a = (a.re : ℝ) • (1 : ℂ) + (a.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  have hIa :
      Complex.I * a =
        (-a.im : ℝ) • (1 : ℂ) + (a.re : ℝ) • Complex.I := by
    rw [ha]
    apply Complex.ext <;> simp
  have hLa :
      L a = (a.re : ℝ) • L 1 + (a.im : ℝ) • L Complex.I := by
    calc
      L a = L ((a.re : ℝ) • (1 : ℂ) + (a.im : ℝ) • Complex.I) := by
        exact congrArg L ha
      _ = L ((a.re : ℝ) • (1 : ℂ)) + L ((a.im : ℝ) • Complex.I) := by rw [map_add]
      _ = (a.re : ℝ) • L 1 + (a.im : ℝ) • L Complex.I := by rw [map_smul, map_smul]
  have hLIa :
      L (Complex.I * a) =
        (-a.im : ℝ) • L 1 + (a.re : ℝ) • L Complex.I := by
    calc
      L (Complex.I * a) = L ((-a.im : ℝ) • (1 : ℂ) + (a.re : ℝ) • Complex.I) := by
        exact congrArg L hIa
      _ = L ((-a.im : ℝ) • (1 : ℂ)) + L ((a.re : ℝ) • Complex.I) := by rw [map_add]
      _ = (-a.im : ℝ) • L 1 + (a.re : ℝ) • L Complex.I := by rw [map_smul, map_smul]
  rw [hLa, hLIa]
  apply Complex.ext <;> simp [mul_add, add_mul, Complex.mul_re, Complex.mul_im] <;> ring

/-- Chain rule for `wirtingerDerivBar` under composition with a holomorphic map.

If `g` is holomorphic at `z`, then
`∂̄(f ∘ g)(z) = (∂̄f)(g(z)) * conj(g'(z))`. -/
theorem wirtingerDerivBar_comp_holomorphic {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f (g z)) (hg : DifferentiableAt ℂ g z) :
    wirtingerDerivBar (f ∘ g) z =
      wirtingerDerivBar f (g z) * starRingEnd ℂ (deriv g z) := by
  unfold wirtingerDerivBar
  have hgR : DifferentiableAt ℝ g z := differentiableAt_real_of_complex hg
  have hchain : fderiv ℝ (f ∘ g) z =
      (fderiv ℝ f (g z)).comp (fderiv ℝ g z) := by
    exact (hf.hasFDerivAt.comp z hgR.hasFDerivAt).fderiv
  have hgfd : fderiv ℝ g z = mulLeftCLM (deriv g z) := fderiv_real_eq_mulLeftCLM hg
  rw [hchain, hgfd]
  set L : ℂ →L[ℝ] ℂ := fderiv ℝ f (g z)
  have hEval :
      L (deriv g z) + Complex.I * L (Complex.I * deriv g z) =
        (L 1 + Complex.I * L Complex.I) * (starRingEnd ℂ (deriv g z)) :=
    clm_eval_add_I_eval_I_mul_conj L (deriv g z)
  have hEval' :
      L (deriv g z) + Complex.I * L (deriv g z * Complex.I) =
        (L 1 + Complex.I * L Complex.I) * (starRingEnd ℂ (deriv g z)) := by
    simpa [mul_comm] using hEval
  have hLhs :
      (L.comp (mulLeftCLM (deriv g z))) 1 +
        Complex.I * (L.comp (mulLeftCLM (deriv g z))) Complex.I =
        (L 1 + Complex.I * L Complex.I) * (starRingEnd ℂ (deriv g z)) := by
    simpa [mulLeftCLM, ContinuousLinearMap.comp_apply] using hEval'
  calc
    (1 / 2 : ℂ) *
        ((L.comp (mulLeftCLM (deriv g z))) 1 +
          Complex.I * (L.comp (mulLeftCLM (deriv g z))) Complex.I)
      = (1 / 2 : ℂ) *
          ((L 1 + Complex.I * L Complex.I) * (starRingEnd ℂ (deriv g z))) := by
            rw [hLhs]
    _ = ((1 / 2 : ℂ) * (L 1 + Complex.I * L Complex.I)) *
          (starRingEnd ℂ (deriv g z)) := by ring
    _ = wirtingerDerivBar f (g z) * starRingEnd ℂ (deriv g z) := by rfl

/-- `AnalyticAt` specialization of `wirtingerDerivBar_comp_holomorphic`. -/
theorem wirtingerDerivBar_comp_analyticAt {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f (g z)) (hg : AnalyticAt ℂ g z) :
    wirtingerDerivBar (f ∘ g) z =
      wirtingerDerivBar f (g z) * starRingEnd ℂ (deriv g z) := by
  exact wirtingerDerivBar_comp_holomorphic hf hg.differentiableAt

/-- Chain rule for `wirtingerDeriv` under composition with a holomorphic map.

If `g` is holomorphic at `z`, then
`∂(f ∘ g)(z) = (∂f)(g(z)) * g'(z)`. -/
theorem wirtingerDeriv_comp_holomorphic {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f (g z)) (hg : DifferentiableAt ℂ g z) :
    wirtingerDeriv (f ∘ g) z =
      wirtingerDeriv f (g z) * deriv g z := by
  unfold wirtingerDeriv
  have hgR : DifferentiableAt ℝ g z := differentiableAt_real_of_complex hg
  have hchain : fderiv ℝ (f ∘ g) z =
      (fderiv ℝ f (g z)).comp (fderiv ℝ g z) := by
    exact (hf.hasFDerivAt.comp z hgR.hasFDerivAt).fderiv
  have hgfd : fderiv ℝ g z = mulLeftCLM (deriv g z) := fderiv_real_eq_mulLeftCLM hg
  rw [hchain, hgfd]
  set L : ℂ →L[ℝ] ℂ := fderiv ℝ f (g z)
  have hEval :
      L (deriv g z) - Complex.I * L (Complex.I * deriv g z) =
        (L 1 - Complex.I * L Complex.I) * deriv g z :=
    clm_eval_sub_I_eval_I_mul L (deriv g z)
  have hEval' :
      L (deriv g z) - Complex.I * L (deriv g z * Complex.I) =
        (L 1 - Complex.I * L Complex.I) * deriv g z := by
    simpa [mul_comm] using hEval
  have hLhs :
      (L.comp (mulLeftCLM (deriv g z))) 1 -
        Complex.I * (L.comp (mulLeftCLM (deriv g z))) Complex.I =
        (L 1 - Complex.I * L Complex.I) * deriv g z := by
    simpa [mulLeftCLM, ContinuousLinearMap.comp_apply] using hEval'
  calc
    (1 / 2 : ℂ) *
        ((L.comp (mulLeftCLM (deriv g z))) 1 -
          Complex.I * (L.comp (mulLeftCLM (deriv g z))) Complex.I)
      = (1 / 2 : ℂ) * ((L 1 - Complex.I * L Complex.I) * deriv g z) := by
          rw [hLhs]
    _ = ((1 / 2 : ℂ) * (L 1 - Complex.I * L Complex.I)) * deriv g z := by ring
    _ = wirtingerDeriv f (g z) * deriv g z := by rfl

/-- `AnalyticAt` specialization of `wirtingerDeriv_comp_holomorphic`. -/
theorem wirtingerDeriv_comp_analyticAt {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f (g z)) (hg : AnalyticAt ℂ g z) :
    wirtingerDeriv (f ∘ g) z =
      wirtingerDeriv f (g z) * deriv g z := by
  exact wirtingerDeriv_comp_holomorphic hf hg.differentiableAt

/-- Conjugation swaps `∂` and `∂̄` for any real-differentiable map:
`∂̄(conj ∘ g) = conj(∂g)`. -/
theorem wirtingerDerivBar_comp_conj_real {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℝ g z) :
    wirtingerDerivBar (starRingEnd ℂ ∘ g) z = starRingEnd ℂ (wirtingerDeriv g z) := by
  unfold wirtingerDerivBar wirtingerDeriv
  have hfderiv_chain : fderiv ℝ (starRingEnd ℂ ∘ g) z =
      (RiemannSurfaces.Analytic.conjCLM).comp (fderiv ℝ g z) := by
    exact (RiemannSurfaces.Analytic.conjCLM.hasFDerivAt.comp z hg.hasFDerivAt).fderiv
  have hconj_apply : ∀ w : ℂ,
      (RiemannSurfaces.Analytic.conjCLM : ℂ →L[ℝ] ℂ) w = starRingEnd ℂ w := by
    intro w
    show Complex.conjCLE.toContinuousLinearMap w = starRingEnd ℂ w
    erw [conjCLE_apply]
  have hconj_two : (starRingEnd ℂ) (2 : ℂ) = (2 : ℂ) := by
    simpa using (map_natCast (starRingEnd ℂ) 2)
  rw [hfderiv_chain]
  calc
    (1 / 2 : ℂ) *
        (((RiemannSurfaces.Analytic.conjCLM).comp (fderiv ℝ g z)) 1 +
          Complex.I * ((RiemannSurfaces.Analytic.conjCLM).comp (fderiv ℝ g z)) Complex.I)
      = (1 / 2 : ℂ) *
          (starRingEnd ℂ ((fderiv ℝ g z) 1) +
            Complex.I * starRingEnd ℂ ((fderiv ℝ g z) Complex.I)) := by
            simp [ContinuousLinearMap.comp_apply, hconj_apply]
    _ = starRingEnd ℂ ((1 / 2 : ℂ) *
          ((fderiv ℝ g z) 1 - Complex.I * (fderiv ℝ g z) Complex.I)) := by
            simp [map_mul, map_sub, Complex.conj_I, hconj_two]

/-- `ℂ`-differentiable specialization of `wirtingerDerivBar_comp_conj_real`. -/
theorem wirtingerDerivBar_comp_conj {g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℂ g z) :
    wirtingerDerivBar (starRingEnd ℂ ∘ g) z = starRingEnd ℂ (wirtingerDeriv g z) := by
  exact wirtingerDerivBar_comp_conj_real (differentiableAt_real_of_complex hg)

/-- Conjugation swaps `∂` and `∂̄` for any real-differentiable map:
`∂(conj ∘ g) = conj(∂̄g)`. -/
theorem wirtingerDeriv_comp_conj_real {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℝ g z) :
    wirtingerDeriv (starRingEnd ℂ ∘ g) z = starRingEnd ℂ (wirtingerDerivBar g z) := by
  unfold wirtingerDeriv wirtingerDerivBar
  have hfderiv_chain : fderiv ℝ (starRingEnd ℂ ∘ g) z =
      (RiemannSurfaces.Analytic.conjCLM).comp (fderiv ℝ g z) := by
    exact (RiemannSurfaces.Analytic.conjCLM.hasFDerivAt.comp z hg.hasFDerivAt).fderiv
  have hconj_apply : ∀ w : ℂ,
      (RiemannSurfaces.Analytic.conjCLM : ℂ →L[ℝ] ℂ) w = starRingEnd ℂ w := by
    intro w
    show Complex.conjCLE.toContinuousLinearMap w = starRingEnd ℂ w
    erw [conjCLE_apply]
  have hconj_two : (starRingEnd ℂ) (2 : ℂ) = (2 : ℂ) := by
    simpa using (map_natCast (starRingEnd ℂ) 2)
  rw [hfderiv_chain]
  calc
    (1 / 2 : ℂ) *
        (((RiemannSurfaces.Analytic.conjCLM).comp (fderiv ℝ g z)) 1 -
          Complex.I * ((RiemannSurfaces.Analytic.conjCLM).comp (fderiv ℝ g z)) Complex.I)
      = (1 / 2 : ℂ) *
          (starRingEnd ℂ ((fderiv ℝ g z) 1) -
            Complex.I * starRingEnd ℂ ((fderiv ℝ g z) Complex.I)) := by
            simp [ContinuousLinearMap.comp_apply, hconj_apply]
    _ = starRingEnd ℂ ((1 / 2 : ℂ) *
          ((fderiv ℝ g z) 1 + Complex.I * (fderiv ℝ g z) Complex.I)) := by
            simp [map_mul, map_add, Complex.conj_I, hconj_two, sub_eq_add_neg]

/-- Chain rule for `wirtingerDeriv` with conjugation: `∂(conj ∘ g)=0` when `g` is holomorphic. -/
theorem wirtingerDeriv_comp_conj {g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℂ g z) :
    wirtingerDeriv (starRingEnd ℂ ∘ g) z = 0 := by
  have hgR : DifferentiableAt ℝ g z := differentiableAt_real_of_complex hg
  have hbar0 : wirtingerDerivBar g z = 0 :=
    (holomorphic_iff_wirtingerDerivBar_zero.mp hg).2
  calc
    wirtingerDeriv (starRingEnd ℂ ∘ g) z
        = starRingEnd ℂ (wirtingerDerivBar g z) := wirtingerDeriv_comp_conj_real hgR
    _ = 0 := by simpa [hbar0]

/-!
## Differentiability in Manifold Charts

For functions on manifolds, ContMDiff implies differentiability in chart coordinates.
This section provides the bridge needed for Wirtinger derivative computations on Riemann surfaces.
-/

open scoped Manifold
open Topology

/-- For a ContMDiff function on a manifold modeled on ℂ (with ℝ-smoothness),
    composition with chart symm gives DifferentiableAt ℝ, provided the smoothness
    order is nonzero.

    This is the key link: manifold smoothness → chart differentiability → Wirtinger derivatives. -/
theorem differentiableAt_chart_comp_of_ne_zero {M : Type*}
    [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) ⊤ M]
    {n : WithTop ℕ∞} {f : M → ℂ} (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n f)
    (hn : n ≠ 0) (p : M) :
    DifferentiableAt ℝ (f ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) := by
  -- Get ContMDiffAt from ContMDiff
  have hCM : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n f p := hf.contMDiffAt
  -- Use contMDiffAt_iff_of_mem_source to extract ContDiffWithinAt
  have hp_source : p ∈ (chartAt ℂ p).source := mem_chart_source ℂ p
  have hfp_source : f p ∈ (chartAt ℂ (f p)).source := mem_chart_source ℂ (f p)
  rw [contMDiffAt_iff_of_mem_source hp_source hfp_source] at hCM
  obtain ⟨_, hcdiff⟩ := hCM
  -- For target ℂ (model space), extChartAt is identity
  have htarget : extChartAt 𝓘(ℝ, ℂ) (f p) = PartialEquiv.refl ℂ := by
    simp only [extChartAt, chartAt_self_eq, OpenPartialHomeomorph.refl_partialEquiv,
      modelWithCornersSelf_partialEquiv, PartialEquiv.refl_trans, mfld_simps]
  -- For source, use extend_coe_symm: (f.extend I).symm = f.symm ∘ I.symm
  -- For 𝓘(ℝ, ℂ), I.symm = id, so (extChartAt).symm = chartAt.symm
  have hsource_symm : ∀ z, (extChartAt 𝓘(ℝ, ℂ) p).symm z = (chartAt ℂ p).symm z := by
    intro z
    simp only [extChartAt, OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe_symm,
      Function.comp_apply, id_eq]
  have hsource_val : extChartAt 𝓘(ℝ, ℂ) p p = (chartAt ℂ p) p := by simp only [mfld_simps]
  -- range 𝓘(ℝ, ℂ) = univ since I = id
  have hrange : Set.range (𝓘(ℝ, ℂ) : ℂ → ℂ) = Set.univ := by
    simp only [modelWithCornersSelf_coe, Set.range_id]
  -- Rewrite hcdiff using these simplifications
  have hcdiff' : ContDiffWithinAt ℝ n (f ∘ (chartAt ℂ p).symm) Set.univ ((chartAt ℂ p) p) := by
    have heq1 : (fun z => (extChartAt 𝓘(ℝ, ℂ) p).symm z) = (fun z => (chartAt ℂ p).symm z) :=
      funext hsource_symm
    have heq2 : (extChartAt 𝓘(ℝ, ℂ) (f p)) ∘ f = f := by
      rw [htarget]; rfl
    -- Rewrite hcdiff step by step
    simp only [heq1, hrange, hsource_val, htarget, PartialEquiv.refl_coe] at hcdiff
    exact hcdiff
  -- ContDiffWithinAt on univ gives ContDiffAt
  have hcdiffAt : ContDiffAt ℝ n (f ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) :=
    hcdiff'.contDiffAt Filter.univ_mem
  -- Nonzero-order ContDiffAt implies differentiability
  exact hcdiffAt.differentiableAt hn

/-- `C^∞` specialization of `differentiableAt_chart_comp_of_ne_zero`. -/
theorem differentiableAt_chart_comp {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℝ, ℂ) ⊤ M]
    {f : M → ℂ} (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤ f) (p : M) :
    DifferentiableAt ℝ (f ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) :=
  differentiableAt_chart_comp_of_ne_zero (n := (⊤ : WithTop ℕ∞)) hf WithTop.top_ne_zero p

/-- `smoothOrder` specialization of `differentiableAt_chart_comp_of_ne_zero`. -/
theorem differentiableAt_chart_comp_smoothOrder {M : Type*}
    [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) ⊤ M]
    {f : M → ℂ} (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder f) (p : M) :
    DifferentiableAt ℝ (f ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) :=
  differentiableAt_chart_comp_of_ne_zero (n := smoothOrder) hf smoothOrder_ne_zero p

/-- Variant: ContMDiffAt implies DifferentiableAt in chart. -/
theorem differentiableAt_chart_comp_of_contMDiffAt_of_ne_zero {M : Type*}
    [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) ⊤ M]
    {n : WithTop ℕ∞} {f : M → ℂ} {p : M}
    (hf : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n f p) (hn : n ≠ 0) :
    DifferentiableAt ℝ (f ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) := by
  -- Use contMDiffAt_iff_of_mem_source to extract ContDiffWithinAt
  have hp_source : p ∈ (chartAt ℂ p).source := mem_chart_source ℂ p
  have hfp_source : f p ∈ (chartAt ℂ (f p)).source := mem_chart_source ℂ (f p)
  rw [contMDiffAt_iff_of_mem_source hp_source hfp_source] at hf
  obtain ⟨_, hcdiff⟩ := hf
  -- For target ℂ (model space), extChartAt is identity
  have htarget : extChartAt 𝓘(ℝ, ℂ) (f p) = PartialEquiv.refl ℂ := by
    simp only [extChartAt, chartAt_self_eq, OpenPartialHomeomorph.refl_partialEquiv,
      modelWithCornersSelf_partialEquiv, PartialEquiv.refl_trans, mfld_simps]
  -- For source, use extend_coe_symm: (f.extend I).symm = f.symm ∘ I.symm
  have hsource_symm : ∀ z, (extChartAt 𝓘(ℝ, ℂ) p).symm z = (chartAt ℂ p).symm z := by
    intro z
    simp only [extChartAt, OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe_symm,
      Function.comp_apply, id_eq]
  have hsource_val : extChartAt 𝓘(ℝ, ℂ) p p = (chartAt ℂ p) p := by simp only [mfld_simps]
  have hrange : Set.range (𝓘(ℝ, ℂ) : ℂ → ℂ) = Set.univ := by
    simp only [modelWithCornersSelf_coe, Set.range_id]
  -- Rewrite hcdiff using these simplifications
  have hcdiff' : ContDiffWithinAt ℝ n (f ∘ (chartAt ℂ p).symm) Set.univ ((chartAt ℂ p) p) := by
    have heq1 : (fun z => (extChartAt 𝓘(ℝ, ℂ) p).symm z) = (fun z => (chartAt ℂ p).symm z) :=
      funext hsource_symm
    -- Rewrite hcdiff step by step
    simp only [heq1, hrange, hsource_val, htarget, PartialEquiv.refl_coe] at hcdiff
    exact hcdiff
  have hcdiffAt : ContDiffAt ℝ n (f ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) :=
    hcdiff'.contDiffAt Filter.univ_mem
  exact hcdiffAt.differentiableAt hn

/-- `C^∞` specialization of `differentiableAt_chart_comp_of_contMDiffAt_of_ne_zero`. -/
theorem differentiableAt_chart_comp_of_contMDiffAt {M : Type*}
    [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) ⊤ M]
    {f : M → ℂ} {p : M} (hf : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤ f p) :
    DifferentiableAt ℝ (f ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) :=
  differentiableAt_chart_comp_of_contMDiffAt_of_ne_zero
    (n := (⊤ : WithTop ℕ∞)) hf WithTop.top_ne_zero

/-- `smoothOrder` specialization of
`differentiableAt_chart_comp_of_contMDiffAt_of_ne_zero`. -/
theorem differentiableAt_chart_comp_of_contMDiffAt_smoothOrder {M : Type*}
    [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) ⊤ M]
    {f : M → ℂ} {p : M}
    (hf : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder f p) :
    DifferentiableAt ℝ (f ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) :=
  differentiableAt_chart_comp_of_contMDiffAt_of_ne_zero
    (n := smoothOrder) hf smoothOrder_ne_zero

/-!
## Smoothness of Wirtinger Derivatives

If f is smooth, then its Wirtinger derivatives are smooth.
This follows from the fact that fderiv of a smooth function is smooth.

**Mathematical argument**:
wirtingerDerivBar f z = (1/2)(fderiv ℝ f z 1 + I * fderiv ℝ f z I)

1. If f is C^{n+1}, then fderiv ℝ f is C^n
2. Evaluation at a fixed vector (like 1 or I) is a bounded linear operation on CLMs
3. Scalar multiplication and addition preserve smoothness
4. Hence wirtingerDerivBar f is C^n

We use fun_prop to automate the smoothness proofs.
-/

/-- Evaluation at a fixed vector is a continuous linear map on the space of CLMs. -/
def evalCLM (v : ℂ) : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ where
  toFun := fun L => L v
  map_add' := fun L₁ L₂ => by simp only [ContinuousLinearMap.add_apply]
  map_smul' := fun c L => by simp only [ContinuousLinearMap.smul_apply, RingHom.id_apply]
  cont := continuous_eval_const v

/-- wirtingerDerivBar f z is defined in terms of fderiv ℝ f z applied to 1 and I.
    Since evaluation at a fixed vector is a continuous linear operation,
    smoothness of fderiv ℝ f implies smoothness of wirtingerDerivBar f. -/
theorem wirtingerDerivBar_contDiff {f : ℂ → ℂ} {n : ℕ∞}
    (hf : ContDiff ℝ (n + 1) f) : ContDiff ℝ n (wirtingerDerivBar f) := by
  unfold wirtingerDerivBar
  -- fderiv ℝ f is ContDiff ℝ n when f is ContDiff ℝ (n + 1)
  have hfderiv : ContDiff ℝ n (fun z => fderiv ℝ f z) := hf.fderiv_right le_rfl
  -- Evaluation at a fixed vector is a CLM, hence smooth
  have heval1 : ContDiff ℝ n (fun z => fderiv ℝ f z 1) :=
    hfderiv.clm_apply contDiff_const
  have hevalI : ContDiff ℝ n (fun z => fderiv ℝ f z Complex.I) :=
    hfderiv.clm_apply contDiff_const
  -- Combine with scalar multiplication and addition
  have hsum : ContDiff ℝ n (fun z => fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) :=
    heval1.add (contDiff_const.mul hevalI)
  exact contDiff_const.mul hsum

/-- wirtingerDeriv f z is also smooth when f is smooth. -/
theorem wirtingerDeriv_contDiff {f : ℂ → ℂ} {n : ℕ∞}
    (hf : ContDiff ℝ (n + 1) f) : ContDiff ℝ n (wirtingerDeriv f) := by
  unfold wirtingerDeriv
  have hfderiv : ContDiff ℝ n (fun z => fderiv ℝ f z) := hf.fderiv_right le_rfl
  have heval1 : ContDiff ℝ n (fun z => fderiv ℝ f z 1) :=
    hfderiv.clm_apply contDiff_const
  have hevalI : ContDiff ℝ n (fun z => fderiv ℝ f z Complex.I) :=
    hfderiv.clm_apply contDiff_const
  have hdiff : ContDiff ℝ n (fun z => fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I) :=
    heval1.sub (contDiff_const.mul hevalI)
  exact contDiff_const.mul hdiff

private lemma withTopNatInf_add_one_ne_zero (n : ℕ∞) :
    ((n : WithTop ℕ∞) + 1) ≠ 0 := by
  cases n with
  | top =>
      simp
  | coe a =>
      intro h
      have h' : ((a : ℕ∞) + 1) = (0 : ℕ∞) := by
        exact WithTop.coe_eq_coe.mp h
      cases a with
      | zero =>
          simp at h'
      | succ b =>
          simp at h'

/-- Open-set version: if `f` is `C^(n+1)` on an open set, then `∂f/∂z̄` is `C^n` there. -/
theorem wirtingerDerivBar_contDiffOn {f : ℂ → ℂ} {s : Set ℂ} {n : ℕ∞}
    (hf : ContDiffOn ℝ (n + 1) f s) (hs : IsOpen s) :
    ContDiffOn ℝ n (wirtingerDerivBar f) s := by
  unfold wirtingerDerivBar
  have hsUnique : UniqueDiffOn ℝ s := hs.uniqueDiffOn
  have hfderivWithin : ContDiffOn ℝ n (fderivWithin ℝ f s) s :=
    hf.fderivWithin hsUnique le_rfl
  have hn1_ne_zero : ((n : WithTop ℕ∞) + 1) ≠ 0 := withTopNatInf_add_one_ne_zero n
  have hfderiv : ContDiffOn ℝ n (fun z => fderiv ℝ f z) s := by
    refine hfderivWithin.congr ?_
    intro z hz
    have hcontAt : ContDiffAt ℝ (n + 1) f z := hf.contDiffAt (hs.mem_nhds hz)
    have hdiff : DifferentiableAt ℝ f z := hcontAt.differentiableAt hn1_ne_zero
    exact (fderivWithin_eq_fderiv (hs.uniqueDiffWithinAt hz) hdiff).symm
  have heval1 : ContDiffOn ℝ n (fun z => fderiv ℝ f z 1) s :=
    hfderiv.clm_apply contDiffOn_const
  have hevalI : ContDiffOn ℝ n (fun z => fderiv ℝ f z Complex.I) s :=
    hfderiv.clm_apply contDiffOn_const
  have hsum : ContDiffOn ℝ n (fun z => fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) s :=
    heval1.add (contDiffOn_const.mul hevalI)
  exact contDiffOn_const.mul hsum

/-- Open-set version: if `f` is `C^(n+1)` on an open set, then `∂f/∂z` is `C^n` there. -/
theorem wirtingerDeriv_contDiffOn {f : ℂ → ℂ} {s : Set ℂ} {n : ℕ∞}
    (hf : ContDiffOn ℝ (n + 1) f s) (hs : IsOpen s) :
    ContDiffOn ℝ n (wirtingerDeriv f) s := by
  unfold wirtingerDeriv
  have hsUnique : UniqueDiffOn ℝ s := hs.uniqueDiffOn
  have hfderivWithin : ContDiffOn ℝ n (fderivWithin ℝ f s) s :=
    hf.fderivWithin hsUnique le_rfl
  have hn1_ne_zero : ((n : WithTop ℕ∞) + 1) ≠ 0 := withTopNatInf_add_one_ne_zero n
  have hfderiv : ContDiffOn ℝ n (fun z => fderiv ℝ f z) s := by
    refine hfderivWithin.congr ?_
    intro z hz
    have hcontAt : ContDiffAt ℝ (n + 1) f z := hf.contDiffAt (hs.mem_nhds hz)
    have hdiff : DifferentiableAt ℝ f z := hcontAt.differentiableAt hn1_ne_zero
    exact (fderivWithin_eq_fderiv (hs.uniqueDiffWithinAt hz) hdiff).symm
  have heval1 : ContDiffOn ℝ n (fun z => fderiv ℝ f z 1) s :=
    hfderiv.clm_apply contDiffOn_const
  have hevalI : ContDiffOn ℝ n (fun z => fderiv ℝ f z Complex.I) s :=
    hfderiv.clm_apply contDiffOn_const
  have hdiff : ContDiffOn ℝ n (fun z => fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I) s :=
    heval1.sub (contDiffOn_const.mul hevalI)
  exact contDiffOn_const.mul hdiff

/-- wirtingerDerivBar of a C^∞ function is C^∞. -/
theorem wirtingerDerivBar_smooth {f : ℂ → ℂ}
    (hf : ∀ n : ℕ, ContDiff ℝ n f) : ∀ n : ℕ, ContDiff ℝ n (wirtingerDerivBar f) := by
  intro n
  -- We need f to be C^{n+1}, and wirtingerDerivBar_contDiff gives C^n
  have hn1 : ContDiff ℝ (↑(n + 1) : ℕ∞) f := hf (n + 1)
  -- Show (n+1 : ℕ) = (n : ℕ∞) + 1 when coerced
  have heq : (↑(n + 1) : ℕ∞) = (↑n : ℕ∞) + 1 := by simp [Nat.cast_add]
  rw [heq] at hn1
  exact wirtingerDerivBar_contDiff hn1

/-- wirtingerDeriv of a C^∞ function is C^∞. -/
theorem wirtingerDeriv_smooth {f : ℂ → ℂ}
    (hf : ∀ n : ℕ, ContDiff ℝ n f) : ∀ n : ℕ, ContDiff ℝ n (wirtingerDeriv f) := by
  intro n
  have hn1 : ContDiff ℝ (↑(n + 1) : ℕ∞) f := hf (n + 1)
  have heq : (↑(n + 1) : ℕ∞) = (↑n : ℕ∞) + 1 := by simp [Nat.cast_add]
  rw [heq] at hn1
  exact wirtingerDeriv_contDiff hn1

/-!
## The Laplacian in Terms of Wirtinger Derivatives

The Laplacian Δf = ∂²f/∂x² + ∂²f/∂y² can be written as:
  Δf = 4 · ∂²f/∂z∂z̄
-/

/-- The Laplacian equals 4 times the mixed Wirtinger derivative (commutativity).
    This follows from equality of mixed partial derivatives.

    **Proof sketch**:
    - ∂/∂z = (1/2)(∂/∂x - i∂/∂y)
    - ∂/∂z̄ = (1/2)(∂/∂x + i∂/∂y)
    - ∂/∂z(∂/∂z̄) = (1/4)(∂²/∂x² + ∂²/∂y²) by Schwarz's theorem (mixed partials commute)
    - ∂/∂z̄(∂/∂z) = (1/4)(∂²/∂x² + ∂²/∂y²) by Schwarz's theorem
    - Hence they're equal.

    This requires connecting Wirtinger derivatives to second-order Fréchet derivatives
    and using `ContDiffAt.isSymmSndFDerivAt` from Mathlib. -/
theorem laplacian_eq_four_wirtinger_mixed_at (f : ℂ → ℂ) (z : ℂ)
    (hf : ContDiffAt ℝ 2 f z) :
    wirtingerDeriv (wirtingerDerivBar f) z = wirtingerDerivBar (wirtingerDeriv f) z := by
  -- Use the symmetry of second derivatives from Mathlib
  -- For C² functions over ℝ: fderiv ℝ (fderiv ℝ f) z v w = fderiv ℝ (fderiv ℝ f) z w v
  have hsymm : IsSymmSndFDerivAt ℝ f z := by
    apply ContDiffAt.isSymmSndFDerivAt hf
    simp only [minSmoothness_of_isRCLikeNormedField, le_refl]

  -- Define: D²(v)(w) = fderiv ℝ (fderiv ℝ f) z v w (the second derivative)
  set D2 := fderiv ℝ (fderiv ℝ f) z with hD2

  -- By symmetry: D²(1)(I) = D²(I)(1)
  have hsymm_1_I : D2 1 Complex.I = D2 Complex.I 1 := hsymm 1 Complex.I

  -- Get differentiability
  have hdiff_fderiv : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero

  -- Define helper functions for evaluation at 1 and I
  let eval1 : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ 1
  let evalI : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ Complex.I

  -- Differentiability of the component functions at z
  have hdiff1 : DifferentiableAt ℝ (fun w => fderiv ℝ f w 1) z := by
    have h : DifferentiableAt ℝ (eval1 ∘ fderiv ℝ f) z :=
      eval1.differentiableAt.comp z hdiff_fderiv
    exact h
  have hdiffI : DifferentiableAt ℝ (fun w => fderiv ℝ f w Complex.I) z := by
    have h : DifferentiableAt ℝ (evalI ∘ fderiv ℝ f) z :=
      evalI.differentiableAt.comp z hdiff_fderiv
    exact h

  -- The key lemma: fderiv ℝ (fun w => fderiv ℝ f w v) z u = D2 u v
  have hD2_apply : ∀ u v, fderiv ℝ (fun w => fderiv ℝ f w v) z u = D2 u v := by
    intro u v
    let evalV : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ v
    have hcomp : fderiv ℝ (evalV ∘ fderiv ℝ f) z = evalV.comp (fderiv ℝ (fderiv ℝ f) z) := by
      rw [fderiv_comp z evalV.differentiableAt hdiff_fderiv]
      simp [ContinuousLinearMap.fderiv]
    calc fderiv ℝ (fun w => fderiv ℝ f w v) z u
      _ = (fderiv ℝ (evalV ∘ fderiv ℝ f) z) u := rfl
      _ = (evalV.comp D2) u := by rw [hcomp]
      _ = evalV (D2 u) := rfl
      _ = D2 u v := rfl

  -- Define the inner functions without let bindings for wirtingerDerivBar/wirtingerDeriv
  -- wirtingerDerivBar f z' = (1/2)(fderiv ℝ f z' 1 + I * fderiv ℝ f z' I)
  -- wirtingerDeriv f z' = (1/2)(fderiv ℝ f z' 1 - I * fderiv ℝ f z' I)

  -- Since wirtingerDerivBar and wirtingerDeriv use `let L := fderiv ℝ f z'`,
  -- we need to show they're equal to our simplified forms
  have heq_bar : ∀ z', wirtingerDerivBar f z' =
      (1/2 : ℂ) * (fderiv ℝ f z' 1 + Complex.I * fderiv ℝ f z' Complex.I) := by
    intro z'; unfold wirtingerDerivBar; ring
  have heq_hol : ∀ z', wirtingerDeriv f z' =
      (1/2 : ℂ) * (fderiv ℝ f z' 1 - Complex.I * fderiv ℝ f z' Complex.I) := by
    intro z'; unfold wirtingerDeriv; ring

  -- Compute fderiv of wirtingerDerivBar f at z using mulLeftCLM-based approach
  -- to avoid fderiv_const_smul (needs unsynthesizable Module ℂ (ℂ →L[ℝ] ℂ))
  have hfderiv_bar_apply : ∀ u, fderiv ℝ (wirtingerDerivBar f) z u =
      (1/2 : ℂ) * (D2 u 1 + Complex.I * D2 u Complex.I) := by
    intro u
    -- Decompose wirtingerDerivBar f as Pi-sum of const * component
    have heq3 : wirtingerDerivBar f =
        (fun w => (1/2 : ℂ) * fderiv ℝ f w 1) +
        (fun w => (Complex.I / 2) * fderiv ℝ f w Complex.I) := by
      ext z'; simp only [Pi.add_apply]; rw [heq_bar z']; ring
    have ha : DifferentiableAt ℝ (fun w => (1/2 : ℂ) * fderiv ℝ f w 1) z :=
      (mulLeftCLM (1/2)).differentiableAt.comp z hdiff1
    have hb : DifferentiableAt ℝ (fun w => (Complex.I / 2) * fderiv ℝ f w Complex.I) z :=
      (mulLeftCLM (Complex.I / 2)).differentiableAt.comp z hdiffI
    rw [heq3, fderiv_add ha hb, ContinuousLinearMap.add_apply,
        fderiv_const_mul_apply' hdiff1 (1/2 : ℂ) u,
        fderiv_const_mul_apply' hdiffI (Complex.I / 2) u,
        hD2_apply u 1, hD2_apply u Complex.I]
    ring

  have hfderiv_hol_apply : ∀ u, fderiv ℝ (wirtingerDeriv f) z u =
      (1/2 : ℂ) * (D2 u 1 - Complex.I * D2 u Complex.I) := by
    intro u
    -- Decompose wirtingerDeriv f as Pi-difference of const * component
    have heq3 : wirtingerDeriv f =
        (fun w => (1/2 : ℂ) * fderiv ℝ f w 1) -
        (fun w => (Complex.I / 2) * fderiv ℝ f w Complex.I) := by
      ext z'; simp only [Pi.sub_apply]; rw [heq_hol z']; ring
    have ha : DifferentiableAt ℝ (fun w => (1/2 : ℂ) * fderiv ℝ f w 1) z :=
      (mulLeftCLM (1/2)).differentiableAt.comp z hdiff1
    have hb : DifferentiableAt ℝ (fun w => (Complex.I / 2) * fderiv ℝ f w Complex.I) z :=
      (mulLeftCLM (Complex.I / 2)).differentiableAt.comp z hdiffI
    rw [heq3, fderiv_sub ha hb, ContinuousLinearMap.sub_apply,
        fderiv_const_mul_apply' hdiff1 (1/2 : ℂ) u,
        fderiv_const_mul_apply' hdiffI (Complex.I / 2) u,
        hD2_apply u 1, hD2_apply u Complex.I]
    ring

  -- Now compute both sides
  -- LHS = wirtingerDeriv (wirtingerDerivBar f) z
  --     = (1/2)(fderiv ℝ (wirtingerDerivBar f) z 1 - I * fderiv ℝ (wirtingerDerivBar f) z I)
  -- RHS = wirtingerDerivBar (wirtingerDeriv f) z
  --     = (1/2)(fderiv ℝ (wirtingerDeriv f) z 1 + I * fderiv ℝ (wirtingerDeriv f) z I)

  -- Expand wirtingerDeriv (wirtingerDerivBar f) z
  have hLHS : wirtingerDeriv (wirtingerDerivBar f) z =
      (1/2 : ℂ) * (fderiv ℝ (wirtingerDerivBar f) z 1 -
                   Complex.I * fderiv ℝ (wirtingerDerivBar f) z Complex.I) := by
    unfold wirtingerDeriv; ring

  -- Expand wirtingerDerivBar (wirtingerDeriv f) z
  have hRHS : wirtingerDerivBar (wirtingerDeriv f) z =
      (1/2 : ℂ) * (fderiv ℝ (wirtingerDeriv f) z 1 +
                   Complex.I * fderiv ℝ (wirtingerDeriv f) z Complex.I) := by
    unfold wirtingerDerivBar; ring

  rw [hLHS, hRHS, hfderiv_bar_apply 1, hfderiv_bar_apply Complex.I,
      hfderiv_hol_apply 1, hfderiv_hol_apply Complex.I]
  -- Now both sides are expressions in D2
  rw [hsymm_1_I]
  ring

/-- Global `C²` version of mixed Wirtinger commutativity. -/
theorem laplacian_eq_four_wirtinger_mixed (f : ℂ → ℂ) (z : ℂ)
    (hf : ContDiff ℝ 2 f) :
    wirtingerDeriv (wirtingerDerivBar f) z = wirtingerDerivBar (wirtingerDeriv f) z := by
  exact laplacian_eq_four_wirtinger_mixed_at f z hf.contDiffAt

end RiemannSurfaces.Analytic.Infrastructure
