import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.Algebra.Structures
import StringGeometry.RiemannSurfaces.Analytic.Basic
import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.Infrastructure.RealSmoothness

/-!
# Differential Forms on Riemann Surfaces

This file develops the theory of differential forms on Riemann surfaces,
with particular emphasis on the (p,q)-decomposition that is fundamental
for Hodge theory and the ∂̄-operator.

## Mathematical Background

### The Cotangent Bundle and Forms

For a Riemann surface Σ (a 1-dimensional complex manifold), the tangent space
T_p Σ at each point p is a 1-dimensional ℂ-vector space. The cotangent space
T*_p Σ is its dual.

Using mathlib's model `𝓘(ℂ, ℂ)` (modelWithCornersSelf ℂ ℂ), the tangent and
cotangent spaces are naturally identified with ℂ. A smooth 1-form is a smooth
section of the cotangent bundle.

### (p,q)-Decomposition

In local holomorphic coordinates z = x + iy:
- dz = dx + i dy spans T*^{1,0} (holomorphic cotangent space)
- dz̄ = dx - i dy spans T*^{0,1} (antiholomorphic cotangent space)

The complexified cotangent bundle decomposes: T*_ℂ Σ = T*^{1,0} ⊕ T*^{0,1}

A (1,0)-form has local expression f(z) dz
A (0,1)-form has local expression g(z) dz̄
A (1,1)-form has local expression h(z) dz ∧ dz̄

### Transformation Rules

Under coordinate change z ↦ w = φ(z):
- dw = φ'(z) dz, so f(z) dz = f(φ⁻¹(w)) · (φ⁻¹)'(w) dw
- dw̄ = conj(φ'(z)) dz̄
- dw ∧ dw̄ = |φ'(z)|² dz ∧ dz̄

These transformation rules are encoded in the bundle structure.

### Smoothness Model

Forms use ℝ-smoothness (`ContMDiff 𝓘(ℝ, ℂ)`) rather than ℂ-smoothness (`ContMDiff 𝓘(ℂ, ℂ)`).
This is mathematically correct because:
1. Complex conjugation is ℝ-smooth but not ℂ-smooth
2. The ∂̄-operator involves conjugation
3. (0,1)-forms transform via conjugate of transition functions

Holomorphic forms are the subtype of (1,0)-forms with MDifferentiable sections.

## Main Definitions

* `SmoothFunction` - ℂ-smooth ℂ-valued functions (holomorphic-smooth)
* `Form_10` - (1,0)-forms (ℝ-smooth sections)
* `Form_01` - (0,1)-forms (ℝ-smooth sections)
* `Form_11` - (1,1)-forms (area/volume forms)
* `HolomorphicForm` - Holomorphic 1-forms

## References

* Griffiths, Harris "Principles of Algebraic Geometry" Ch 0.5-0.7
* Wells "Differential Analysis on Complex Manifolds"
* Forster "Lectures on Riemann Surfaces"
-/

namespace RiemannSurfaces.Analytic

open scoped Manifold
open Complex Topology

/-!
## Smooth Functions on Riemann Surfaces

We work with `ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ⊤` which captures C^∞ functions in the complex sense.
For a function f : M → ℂ where M is a Riemann surface, this means f is smooth as a map
between complex manifolds. Note that this is stronger than real smoothness but weaker than
holomorphicity (which is `MDifferentiable`).
-/

variable (RS : RiemannSurface)

/-- A smooth function on a Riemann surface (smooth in the complex manifold sense).
    This is ℂ-smoothness, stronger than ℝ-smoothness. -/
structure SmoothFunction (RS : RiemannSurface) where
  toFun : RS.carrier → ℂ
  smooth' : letI := RS.topology
            letI := RS.chartedSpace
            ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ⊤ toFun

namespace SmoothFunction

variable {RS : RiemannSurface}

instance : CoeFun (SmoothFunction RS) (fun _ => RS.carrier → ℂ) := ⟨toFun⟩

@[ext]
theorem ext {f g : SmoothFunction RS} (h : ∀ p, f.toFun p = g.toFun p) : f = g := by
  cases f; cases g; congr 1; funext p; exact h p

noncomputable def const (c : ℂ) : SmoothFunction RS where
  toFun := fun _ => c
  smooth' := by letI := RS.topology; letI := RS.chartedSpace; exact contMDiff_const

noncomputable instance : Zero (SmoothFunction RS) := ⟨const 0⟩
noncomputable instance : One (SmoothFunction RS) := ⟨const 1⟩

noncomputable def add (f g : SmoothFunction RS) : SmoothFunction RS where
  toFun := fun p => f.toFun p + g.toFun p
  smooth' := by letI := RS.topology; letI := RS.chartedSpace; exact f.smooth'.add g.smooth'

noncomputable instance : Add (SmoothFunction RS) := ⟨add⟩

noncomputable def neg (f : SmoothFunction RS) : SmoothFunction RS where
  toFun := fun p => -f.toFun p
  smooth' := by letI := RS.topology; letI := RS.chartedSpace; exact f.smooth'.neg

noncomputable instance : Neg (SmoothFunction RS) := ⟨neg⟩

noncomputable def sub (f g : SmoothFunction RS) : SmoothFunction RS where
  toFun := fun p => f.toFun p - g.toFun p
  smooth' := by letI := RS.topology; letI := RS.chartedSpace; exact f.smooth'.sub g.smooth'

noncomputable instance : Sub (SmoothFunction RS) := ⟨sub⟩

noncomputable def mul (f g : SmoothFunction RS) : SmoothFunction RS where
  toFun := fun p => f.toFun p * g.toFun p
  smooth' := by
    letI := RS.topology; letI := RS.chartedSpace
    exact f.smooth'.mul g.smooth'

noncomputable instance : Mul (SmoothFunction RS) := ⟨mul⟩

-- Algebraic properties
@[simp] lemma add_toFun (f g : SmoothFunction RS) (p : RS.carrier) :
    (f + g).toFun p = f.toFun p + g.toFun p := rfl

@[simp] lemma neg_toFun (f : SmoothFunction RS) (p : RS.carrier) :
    (-f).toFun p = -f.toFun p := rfl

@[simp] lemma sub_toFun (f g : SmoothFunction RS) (p : RS.carrier) :
    (f - g).toFun p = f.toFun p - g.toFun p := rfl

@[simp] lemma mul_toFun (f g : SmoothFunction RS) (p : RS.carrier) :
    (f * g).toFun p = f.toFun p * g.toFun p := rfl

@[simp] lemma zero_toFun (p : RS.carrier) : (0 : SmoothFunction RS).toFun p = 0 := rfl
@[simp] lemma one_toFun (p : RS.carrier) : (1 : SmoothFunction RS).toFun p = 1 := rfl

noncomputable instance : CommRing (SmoothFunction RS) where
  add := add
  add_assoc a b c := by ext p; exact add_assoc _ _ _
  zero := 0
  zero_add a := by ext p; exact zero_add _
  add_zero a := by ext p; exact add_zero _
  neg := neg
  neg_add_cancel a := by ext p; exact neg_add_cancel _
  add_comm a b := by ext p; exact add_comm _ _
  mul := mul
  mul_assoc a b c := by ext p; exact mul_assoc _ _ _
  one := 1
  one_mul a := by ext p; exact one_mul _
  mul_one a := by ext p; exact mul_one _
  left_distrib a b c := by ext p; exact mul_add _ _ _
  right_distrib a b c := by ext p; exact add_mul _ _ _
  mul_comm a b := by ext p; exact mul_comm _ _
  zero_mul a := by ext p; exact zero_mul _
  mul_zero a := by ext p; exact mul_zero _
  sub_eq_add_neg a b := by ext p; exact sub_eq_add_neg _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Convert a ℂ-smooth function to an ℝ-smooth function. -/
noncomputable def toRealSmooth (f : SmoothFunction RS) : RealSmoothFunction RS :=
  RealSmoothFunction.ofHolomorphic f.toFun f.smooth'

end SmoothFunction

/-!
## Helper for ℝ-smooth multiplication

Since there is no ContMDiffMul 𝓘(ℝ, ℂ) instance, we provide explicit proofs.
-/

/-- Helper: multiplication of ℝ-smooth functions is ℝ-smooth. -/
theorem contMDiff_mul_real {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {n : WithTop ℕ∞} {f g : M → ℂ}
    (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n f) (hg : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n g) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (fun p => f p * g p) := by
  have hmul : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun p : ℂ × ℂ => p.1 * p.2) := contDiff_mul
  have hmulN : ContDiff ℝ n (fun p : ℂ × ℂ => p.1 * p.2) := by
    have hn_top : n ≤ (⊤ : WithTop ℕ∞) := by
      cases n with
      | top => exact le_rfl
      | coe a => exact (WithTop.coe_lt_top a).le
    exact hmul.of_le (m := n) (n := (⊤ : WithTop ℕ∞)) hn_top
  have hpair : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ × ℂ) n (fun p => (f p, g p)) := hf.prodMk_space hg
  exact hmulN.comp_contMDiff hpair

/-!
## Differential Forms

### Definition via Cotangent Bundle Sections

For a Riemann surface using the model 𝓘(ℂ, ℂ), the cotangent space at each point
is naturally identified with ℂ.

The (p,q)-decomposition arises from the complex structure:
- (1,0)-forms transform by φ' under holomorphic coordinate changes z ↦ w = φ(z)
- (0,1)-forms transform by conj(φ')

We encode this by:
- Form_10: sections of T*^{1,0}, the holomorphic cotangent bundle
- Form_01: sections of T*^{0,1}, related to Form_10 by complex conjugation

**Important**: Forms use ℝ-smoothness (`ContMDiff 𝓘(ℝ, ℂ)`) to allow:
1. Conjugation operations (which are ℝ-smooth but not ℂ-smooth)
2. The ∂̄-operator (which involves conjugation)
3. Proper treatment of (0,1)-forms

The key structural property distinguishing these is:
- Form_10.conj : Form_10 → Form_01
- Form_01.conj : Form_01 → Form_10
with conj ∘ conj = id.
-/

/-- A smooth (1,0)-form on a Riemann surface.

    A (1,0)-form assigns to each point p ∈ Σ a covector in T*^{1,0}_p Σ.
    In local coordinates it has the form f(z) dz.

    Under coordinate change z ↦ w = φ(z):
    f(z) dz = f(φ⁻¹(w)) · (φ⁻¹)'(w) dw

    The coefficient function transforms by the derivative (holomorphic transformation).

    Uses ℝ-smoothness to support conjugation operations. -/
structure Form_10 (RS : RiemannSurface) where
  /-- The coefficient in the canonical trivialization -/
  toSection : RS.carrier → ℂ
  /-- ℝ-smoothness of the section -/
  smooth' : letI := RS.topology
            letI := RS.chartedSpace
            ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder toSection

/-- A smooth (0,1)-form on a Riemann surface.

    A (0,1)-form in local coordinates has the form g(z) dz̄.
    Under coordinate change z ↦ w = φ(z):
    g(z) dz̄ = g(φ⁻¹(w)) · conj((φ⁻¹)'(w)) dw̄

    The coefficient transforms by the conjugate of the derivative (antiholomorphic).

    Uses ℝ-smoothness to support conjugation operations. -/
structure Form_01 (RS : RiemannSurface) where
  toSection : RS.carrier → ℂ
  smooth' : letI := RS.topology
            letI := RS.chartedSpace
            ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder toSection

/-- A (1,1)-form on a Riemann surface.

    A (1,1)-form in local coordinates has the form h(z) dz ∧ dz̄.
    Note: dz ∧ dz̄ = -2i dx ∧ dy, so a (1,1)-form is an area form.

    **Design note on smoothness**:
    Unlike Form_10 and Form_01, we do NOT require global `ContMDiff` smoothness.
    The coefficient of a (1,1)-form transforms by |T'|² under chart transition
    T = φ ∘ ψ⁻¹. The `toSection` field stores the coefficient in the chart
    picked by `chartAt` at each point, which is chart-dependent. Global `ContMDiff`
    is not a well-defined condition for such chart-dependent sections.

    All meaningful operations (equality testing, ∂̄-closedness = 0, linearity)
    work pointwise on `toSection` and are chart-independent when they should be
    (e.g., `toSection p = 0` iff the form vanishes at p, regardless of chart). -/
structure Form_11 (RS : RiemannSurface) where
  toSection : RS.carrier → ℂ

/-!
## Vector Space Structure on Forms
-/

namespace Form_10

variable {RS : RiemannSurface}

instance : CoeFun (Form_10 RS) (fun _ => RS.carrier → ℂ) := ⟨toSection⟩

@[ext]
theorem ext {ω₁ ω₂ : Form_10 RS} (h : ω₁.toSection = ω₂.toSection) : ω₁ = ω₂ := by
  cases ω₁; cases ω₂; simp_all

noncomputable instance : Zero (Form_10 RS) where
  zero := ⟨fun _ => 0, by letI := RS.topology; letI := RS.chartedSpace; exact contMDiff_const⟩

noncomputable instance : Add (Form_10 RS) where
  add ω₁ ω₂ := ⟨fun p => ω₁.toSection p + ω₂.toSection p,
    by letI := RS.topology; letI := RS.chartedSpace; exact ω₁.smooth'.add ω₂.smooth'⟩

noncomputable instance : Neg (Form_10 RS) where
  neg ω := ⟨fun p => -ω.toSection p,
    by letI := RS.topology; letI := RS.chartedSpace; exact ω.smooth'.neg⟩

noncomputable instance : Sub (Form_10 RS) where
  sub ω₁ ω₂ := ⟨fun p => ω₁.toSection p - ω₂.toSection p,
    by letI := RS.topology; letI := RS.chartedSpace; exact ω₁.smooth'.sub ω₂.smooth'⟩

noncomputable instance : SMul ℂ (Form_10 RS) where
  smul c ω := ⟨fun p => c * ω.toSection p,
    by
      letI := RS.topology; letI := RS.chartedSpace
      exact contMDiff_mul_real contMDiff_const ω.smooth'⟩

/-- Multiplication by a smooth function -/
noncomputable instance : SMul (SmoothFunction RS) (Form_10 RS) where
  smul f ω := ⟨fun p => f.toFun p * ω.toSection p,
    by
      letI := RS.topology; letI := RS.chartedSpace
      -- ℂ-smooth implies ℝ-smooth, so we can use the ℂ-smooth function
      exact contMDiff_mul_real
        ((contMDiff_real_of_complex_rs f.smooth').of_le smoothOrder_le_top) ω.smooth'⟩

/-- Multiplication by an ℝ-smooth function -/
noncomputable instance : SMul (RealSmoothFunction RS) (Form_10 RS) where
  smul f ω := ⟨fun p => f.toFun p * ω.toSection p,
    by
      letI := RS.topology; letI := RS.chartedSpace
      have hmul : ContDiff ℝ ⊤ (fun p : ℂ × ℂ => p.1 * p.2) := contDiff_mul
      have hmulSmooth : ContDiff ℝ smoothOrder (fun p : ℂ × ℂ => p.1 * p.2) :=
        hmul.of_le smoothOrder_le_top
      have hpair :
          ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ × ℂ) smoothOrder (fun p => (f.toFun p, ω.toSection p)) :=
        f.smooth'.prodMk_space ω.smooth'
      exact hmulSmooth.comp_contMDiff hpair⟩

@[simp] lemma add_toSection (ω₁ ω₂ : Form_10 RS) (p : RS.carrier) :
    (ω₁ + ω₂).toSection p = ω₁.toSection p + ω₂.toSection p := rfl

@[simp] lemma neg_toSection (ω : Form_10 RS) (p : RS.carrier) :
    (-ω).toSection p = -ω.toSection p := rfl

@[simp] lemma zero_toSection (p : RS.carrier) : (0 : Form_10 RS).toSection p = 0 := rfl

@[simp] lemma smul_toSection (c : ℂ) (ω : Form_10 RS) (p : RS.carrier) :
    (c • ω).toSection p = c * ω.toSection p := rfl

noncomputable instance : AddCommGroup (Form_10 RS) where
  add_assoc a b c := by ext p; exact add_assoc _ _ _
  zero_add a := by ext p; exact zero_add _
  add_zero a := by ext p; exact add_zero _
  neg_add_cancel a := by ext p; exact neg_add_cancel _
  add_comm a b := by ext p; exact add_comm _ _
  sub_eq_add_neg a b := by ext p; exact sub_eq_add_neg _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

noncomputable instance : Module ℂ (Form_10 RS) where
  one_smul a := by ext p; exact one_mul _
  mul_smul c d a := by ext p; exact mul_assoc _ _ _
  smul_zero c := by ext p; exact mul_zero _
  smul_add c a b := by ext p; exact mul_add _ _ _
  add_smul c d a := by ext p; exact add_mul _ _ _
  zero_smul a := by ext p; exact zero_mul _

end Form_10

namespace Form_01

variable {RS : RiemannSurface}

instance : CoeFun (Form_01 RS) (fun _ => RS.carrier → ℂ) := ⟨toSection⟩

@[ext]
theorem ext {ω₁ ω₂ : Form_01 RS} (h : ω₁.toSection = ω₂.toSection) : ω₁ = ω₂ := by
  cases ω₁; cases ω₂; simp_all

noncomputable instance : Zero (Form_01 RS) where
  zero := ⟨fun _ => 0, by letI := RS.topology; letI := RS.chartedSpace; exact contMDiff_const⟩

noncomputable instance : Add (Form_01 RS) where
  add ω₁ ω₂ := ⟨fun p => ω₁.toSection p + ω₂.toSection p,
    by letI := RS.topology; letI := RS.chartedSpace; exact ω₁.smooth'.add ω₂.smooth'⟩

noncomputable instance : Neg (Form_01 RS) where
  neg ω := ⟨fun p => -ω.toSection p,
    by letI := RS.topology; letI := RS.chartedSpace; exact ω.smooth'.neg⟩

noncomputable instance : Sub (Form_01 RS) where
  sub ω₁ ω₂ := ⟨fun p => ω₁.toSection p - ω₂.toSection p,
    by letI := RS.topology; letI := RS.chartedSpace; exact ω₁.smooth'.sub ω₂.smooth'⟩

noncomputable instance : SMul ℂ (Form_01 RS) where
  smul c ω := ⟨fun p => c * ω.toSection p,
    by
      letI := RS.topology; letI := RS.chartedSpace
      exact contMDiff_mul_real contMDiff_const ω.smooth'⟩

noncomputable instance : SMul (SmoothFunction RS) (Form_01 RS) where
  smul f ω := ⟨fun p => f.toFun p * ω.toSection p,
    by
      letI := RS.topology; letI := RS.chartedSpace
      exact contMDiff_mul_real
        ((contMDiff_real_of_complex_rs f.smooth').of_le smoothOrder_le_top) ω.smooth'⟩

noncomputable instance : SMul (RealSmoothFunction RS) (Form_01 RS) where
  smul f ω := ⟨fun p => f.toFun p * ω.toSection p,
    by
      letI := RS.topology; letI := RS.chartedSpace
      have hmul : ContDiff ℝ ⊤ (fun p : ℂ × ℂ => p.1 * p.2) := contDiff_mul
      have hmulSmooth : ContDiff ℝ smoothOrder (fun p : ℂ × ℂ => p.1 * p.2) :=
        hmul.of_le smoothOrder_le_top
      have hpair :
          ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ × ℂ) smoothOrder (fun p => (f.toFun p, ω.toSection p)) :=
        f.smooth'.prodMk_space ω.smooth'
      exact hmulSmooth.comp_contMDiff hpair⟩

@[simp] lemma add_toSection (ω₁ ω₂ : Form_01 RS) (p : RS.carrier) :
    (ω₁ + ω₂).toSection p = ω₁.toSection p + ω₂.toSection p := rfl

@[simp] lemma neg_toSection (ω : Form_01 RS) (p : RS.carrier) :
    (-ω).toSection p = -ω.toSection p := rfl

@[simp] lemma zero_toSection (p : RS.carrier) : (0 : Form_01 RS).toSection p = 0 := rfl

@[simp] lemma smul_toSection (c : ℂ) (ω : Form_01 RS) (p : RS.carrier) :
    (c • ω).toSection p = c * ω.toSection p := rfl

noncomputable instance : AddCommGroup (Form_01 RS) where
  add_assoc a b c := by ext p; exact add_assoc _ _ _
  zero_add a := by ext p; exact zero_add _
  add_zero a := by ext p; exact add_zero _
  neg_add_cancel a := by ext p; exact neg_add_cancel _
  add_comm a b := by ext p; exact add_comm _ _
  sub_eq_add_neg a b := by ext p; exact sub_eq_add_neg _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

noncomputable instance : Module ℂ (Form_01 RS) where
  one_smul a := by ext p; exact one_mul _
  mul_smul c d a := by ext p; exact mul_assoc _ _ _
  smul_zero c := by ext p; exact mul_zero _
  smul_add c a b := by ext p; exact mul_add _ _ _
  add_smul c d a := by ext p; exact add_mul _ _ _
  zero_smul a := by ext p; exact zero_mul _

end Form_01

namespace Form_11

variable {RS : RiemannSurface}

instance : CoeFun (Form_11 RS) (fun _ => RS.carrier → ℂ) := ⟨toSection⟩

@[ext]
theorem ext {ω₁ ω₂ : Form_11 RS} (h : ω₁.toSection = ω₂.toSection) : ω₁ = ω₂ := by
  cases ω₁; cases ω₂; simp_all

instance : Zero (Form_11 RS) where
  zero := ⟨fun _ => 0⟩

instance : Add (Form_11 RS) where
  add ω₁ ω₂ := ⟨fun p => ω₁.toSection p + ω₂.toSection p⟩

instance : Neg (Form_11 RS) where
  neg ω := ⟨fun p => -ω.toSection p⟩

instance : Sub (Form_11 RS) where
  sub ω₁ ω₂ := ⟨fun p => ω₁.toSection p - ω₂.toSection p⟩

instance : SMul ℂ (Form_11 RS) where
  smul c ω := ⟨fun p => c * ω.toSection p⟩

noncomputable instance : SMul (SmoothFunction RS) (Form_11 RS) where
  smul f ω := ⟨fun p => f.toFun p * ω.toSection p⟩

instance : SMul (RealSmoothFunction RS) (Form_11 RS) where
  smul f ω := ⟨fun p => f.toFun p * ω.toSection p⟩

@[simp] lemma add_toSection (ω₁ ω₂ : Form_11 RS) (p : RS.carrier) :
    (ω₁ + ω₂).toSection p = ω₁.toSection p + ω₂.toSection p := rfl

@[simp] lemma neg_toSection (ω : Form_11 RS) (p : RS.carrier) :
    (-ω).toSection p = -ω.toSection p := rfl

@[simp] lemma zero_toSection (p : RS.carrier) : (0 : Form_11 RS).toSection p = 0 := rfl

@[simp] lemma smul_toSection (c : ℂ) (ω : Form_11 RS) (p : RS.carrier) :
    (c • ω).toSection p = c * ω.toSection p := rfl

instance : AddCommGroup (Form_11 RS) where
  add_assoc a b c := by ext p; exact add_assoc _ _ _
  zero_add a := by ext p; exact zero_add _
  add_zero a := by ext p; exact add_zero _
  neg_add_cancel a := by ext p; exact neg_add_cancel _
  add_comm a b := by ext p; exact add_comm _ _
  sub_eq_add_neg a b := by ext p; exact sub_eq_add_neg _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module ℂ (Form_11 RS) where
  one_smul a := by ext p; exact one_mul _
  mul_smul c d a := by ext p; exact mul_assoc _ _ _
  smul_zero c := by ext p; exact mul_zero _
  smul_add c a b := by ext p; exact mul_add _ _ _
  add_smul c d a := by ext p; exact add_mul _ _ _
  zero_smul a := by ext p; exact zero_mul _

end Form_11

/-!
## 1-Forms as Direct Sum

A general smooth 1-form decomposes as Ω¹ = Ω^{1,0} ⊕ Ω^{0,1}.
-/

/-- A smooth 1-form on a Riemann surface is the direct sum of (1,0) and (0,1) parts. -/
structure Form_1 (RS : RiemannSurface) where
  component_10 : Form_10 RS
  component_01 : Form_01 RS

namespace Form_1

variable {RS : RiemannSurface}

@[ext]
theorem ext {ω₁ ω₂ : Form_1 RS}
    (h10 : ω₁.component_10 = ω₂.component_10)
    (h01 : ω₁.component_01 = ω₂.component_01) : ω₁ = ω₂ := by
  cases ω₁; cases ω₂; simp_all

noncomputable instance : Zero (Form_1 RS) := ⟨⟨0, 0⟩⟩
noncomputable instance : Add (Form_1 RS) where
  add ω₁ ω₂ := ⟨ω₁.component_10 + ω₂.component_10, ω₁.component_01 + ω₂.component_01⟩
noncomputable instance : Neg (Form_1 RS) where
  neg ω := ⟨-ω.component_10, -ω.component_01⟩
noncomputable instance : SMul ℂ (Form_1 RS) where
  smul c ω := ⟨c • ω.component_10, c • ω.component_01⟩

noncomputable instance : AddCommGroup (Form_1 RS) where
  add_assoc a b c := by ext <;> exact add_assoc _ _ _
  zero_add a := by ext <;> exact zero_add _
  add_zero a := by ext <;> exact add_zero _
  neg_add_cancel a := by ext <;> exact neg_add_cancel _
  add_comm a b := by ext <;> exact add_comm _ _
  sub_eq_add_neg a b := by ext <;> exact sub_eq_add_neg _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

noncomputable instance : Module ℂ (Form_1 RS) where
  one_smul a := by
    show Form_1.mk (1 • a.component_10) (1 • a.component_01) = a
    simp only [one_smul]
  mul_smul c d a := by
    show Form_1.mk ((c * d) • a.component_10) ((c * d) • a.component_01) =
         Form_1.mk (c • d • a.component_10) (c • d • a.component_01)
    simp only [mul_smul]
  smul_zero c := by
    show Form_1.mk (c • (0 : Form_10 RS)) (c • (0 : Form_01 RS)) = ⟨0, 0⟩
    simp only [smul_zero]
  smul_add c a b := by
    show Form_1.mk (c • (a.component_10 + b.component_10)) (c • (a.component_01 + b.component_01)) =
         Form_1.mk (c • a.component_10 + c • b.component_10) (c • a.component_01 + c • b.component_01)
    simp only [smul_add]
  add_smul c d a := by
    show Form_1.mk ((c + d) • a.component_10) ((c + d) • a.component_01) =
         Form_1.mk (c • a.component_10 + d • a.component_10) (c • a.component_01 + d • a.component_01)
    simp only [add_smul]
  zero_smul a := by
    show Form_1.mk ((0 : ℂ) • a.component_10) ((0 : ℂ) • a.component_01) = ⟨0, 0⟩
    simp only [zero_smul]

noncomputable def of_10 (ω : Form_10 RS) : Form_1 RS := ⟨ω, 0⟩
noncomputable def of_01 (ω : Form_01 RS) : Form_1 RS := ⟨0, ω⟩

theorem decomposition (ω : Form_1 RS) :
    ω = of_10 ω.component_10 + of_01 ω.component_01 := by
  cases ω with | mk c10 c01 =>
  show Form_1.mk c10 c01 = Form_1.mk (c10 + 0) (0 + c01)
  simp only [add_zero, zero_add]

end Form_1

/-!
## Wedge Product
-/

/-- Wedge product (1,0) ∧ (0,1) → (1,1): (f dz) ∧ (g dz̄) = fg dz ∧ dz̄ -/
def wedge_10_01 {RS : RiemannSurface}
    (ω₁ : Form_10 RS) (ω₂ : Form_01 RS) : Form_11 RS :=
  ⟨fun p => ω₁.toSection p * ω₂.toSection p⟩

/-- Wedge product (0,1) ∧ (1,0) → (1,1): (g dz̄) ∧ (f dz) = -fg dz ∧ dz̄ -/
def wedge_01_10 {RS : RiemannSurface}
    (ω₁ : Form_01 RS) (ω₂ : Form_10 RS) : Form_11 RS :=
  ⟨fun p => -(ω₁.toSection p * ω₂.toSection p)⟩

theorem wedge_antisymm {RS : RiemannSurface} (ω₁ : Form_10 RS) (ω₂ : Form_01 RS) :
    wedge_01_10 ω₂ ω₁ = -wedge_10_01 ω₁ ω₂ := by
  apply Form_11.ext
  funext p
  show -(ω₂.toSection p * ω₁.toSection p) = -(ω₁.toSection p * ω₂.toSection p)
  ring

/-!
## Complex Conjugation

The key structural property distinguishing (1,0) and (0,1) forms:
conjugation exchanges them.

With ℝ-smoothness, conjugation proofs are now straightforward:
- Conjugation is ℝ-smooth (proved in RealSmoothness.lean)
- Composition of ℝ-smooth functions is ℝ-smooth
-/

/-- Complex conjugation (1,0) → (0,1): conj(f dz) = conj(f) dz̄ -/
noncomputable def Form_10.conj {RS : RiemannSurface} (ω : Form_10 RS) : Form_01 RS :=
  ⟨fun p => starRingEnd ℂ (ω.toSection p),
   by
     letI := RS.topology; letI := RS.chartedSpace
     exact conj_contMDiff_real ω.smooth'⟩

/-- Complex conjugation (0,1) → (1,0): conj(g dz̄) = conj(g) dz -/
noncomputable def Form_01.conj {RS : RiemannSurface} (ω : Form_01 RS) : Form_10 RS :=
  ⟨fun p => starRingEnd ℂ (ω.toSection p),
   by
     letI := RS.topology; letI := RS.chartedSpace
     exact conj_contMDiff_real ω.smooth'⟩

/-- Complex conjugation on (1,1)-forms: conj(h dz ∧ dz̄) = conj(h) dz ∧ dz̄ -/
def Form_11.conj {RS : RiemannSurface} (ω : Form_11 RS) : Form_11 RS :=
  ⟨fun p => starRingEnd ℂ (ω.toSection p)⟩

@[simp] lemma Form_10.conj_toSection {RS : RiemannSurface} (ω : Form_10 RS) (p : RS.carrier) :
    ω.conj.toSection p = starRingEnd ℂ (ω.toSection p) := rfl

@[simp] lemma Form_01.conj_toSection {RS : RiemannSurface} (ω : Form_01 RS) (p : RS.carrier) :
    ω.conj.toSection p = starRingEnd ℂ (ω.toSection p) := rfl

@[simp] lemma Form_11.conj_toSection {RS : RiemannSurface} (ω : Form_11 RS) (p : RS.carrier) :
    ω.conj.toSection p = starRingEnd ℂ (ω.toSection p) := rfl

theorem Form_10.conj_conj {RS : RiemannSurface} (ω : Form_10 RS) : ω.conj.conj = ω := by
  ext p; simp only [Form_10.conj_toSection, Form_01.conj_toSection, starRingEnd_self_apply]

theorem Form_01.conj_conj {RS : RiemannSurface} (ω : Form_01 RS) : ω.conj.conj = ω := by
  ext p; simp only [Form_01.conj_toSection, Form_10.conj_toSection, starRingEnd_self_apply]

theorem Form_11.conj_conj {RS : RiemannSurface} (ω : Form_11 RS) : ω.conj.conj = ω := by
  ext p; simp only [Form_11.conj_toSection, starRingEnd_self_apply]

/-- Conjugation is additive on (1,0)-forms. -/
theorem Form_10.conj_add {RS : RiemannSurface} (ω₁ ω₂ : Form_10 RS) :
    (ω₁ + ω₂).conj = ω₁.conj + ω₂.conj := by
  ext p; simp only [Form_10.conj_toSection, Form_10.add_toSection, Form_01.add_toSection, map_add]

/-- Conjugation is additive on (0,1)-forms. -/
theorem Form_01.conj_add {RS : RiemannSurface} (ω₁ ω₂ : Form_01 RS) :
    (ω₁ + ω₂).conj = ω₁.conj + ω₂.conj := by
  ext p; simp only [Form_01.conj_toSection, Form_01.add_toSection, Form_10.add_toSection, map_add]

/-- Conjugation respects scalar multiplication with conjugate scalar. -/
theorem Form_10.conj_smul {RS : RiemannSurface} (c : ℂ) (ω : Form_10 RS) :
    (c • ω).conj = (starRingEnd ℂ c) • ω.conj := by
  ext p; simp only [Form_10.conj_toSection, Form_10.smul_toSection, Form_01.smul_toSection, map_mul]

theorem Form_01.conj_smul {RS : RiemannSurface} (c : ℂ) (ω : Form_01 RS) :
    (c • ω).conj = (starRingEnd ℂ c) • ω.conj := by
  ext p; simp only [Form_01.conj_toSection, Form_01.smul_toSection, Form_10.smul_toSection, map_mul]

/-- Conjugation of zero (1,0)-form is zero (0,1)-form. -/
@[simp] theorem Form_10.conj_zero {RS : RiemannSurface} :
    (0 : Form_10 RS).conj = 0 := by
  ext p
  simp only [Form_10.conj_toSection, Form_10.zero_toSection, Form_01.zero_toSection, map_zero]

/-- Conjugation of zero (0,1)-form is zero (1,0)-form. -/
@[simp] theorem Form_01.conj_zero {RS : RiemannSurface} :
    (0 : Form_01 RS).conj = 0 := by
  ext p
  simp only [Form_01.conj_toSection, Form_01.zero_toSection, Form_10.zero_toSection, map_zero]

/-- Conjugation of zero (1,1)-form is zero (1,1)-form. -/
@[simp] theorem Form_11.conj_zero {RS : RiemannSurface} :
    (0 : Form_11 RS).conj = 0 := by
  ext p
  simp only [Form_11.conj_toSection, Form_11.zero_toSection, map_zero]

/-!
## Holomorphic Forms
-/

/-- A (1,0)-form is holomorphic if its coefficient is holomorphic (MDifferentiable). -/
def Form_10.IsHolomorphic {RS : RiemannSurface} (ω : Form_10 RS) : Prop :=
  letI := RS.topology
  letI := RS.chartedSpace
  MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω.toSection

/-- The space of holomorphic 1-forms -/
def HolomorphicForm (RS : RiemannSurface) := { ω : Form_10 RS // ω.IsHolomorphic }

/-- Create a (1,0)-form from a ℂ-smooth function (like a holomorphic function). -/
noncomputable def Form_10.ofComplexSmooth {RS : RiemannSurface}
    (f : RS.carrier → ℂ)
    (hf : letI := RS.topology
          letI := RS.chartedSpace
          letI := RS.isManifold
          ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ⊤ f) : Form_10 RS where
  toSection := f
  smooth' := by
    letI := RS.topology
    letI := RS.chartedSpace
    exact (contMDiff_real_of_complex_rs hf).of_le smoothOrder_le_top

/-!
## Real Forms
-/

/-- A 1-form is real if conj(ω^{1,0}) = ω^{0,1} -/
def Form_1.IsReal {RS : RiemannSurface} (ω : Form_1 RS) : Prop :=
  ω.component_01 = ω.component_10.conj

noncomputable def realForm_of_10 {RS : RiemannSurface} (ω : Form_10 RS) : Form_1 RS :=
  ⟨ω, ω.conj⟩

theorem realForm_of_10_isReal {RS : RiemannSurface} (ω : Form_10 RS) :
    (realForm_of_10 ω).IsReal := rfl

/-!
## Area Form
-/

/-- The standard area form: (i/2) dz ∧ dz̄ = dx ∧ dy -/
noncomputable def areaForm (RS : RiemannSurface) : Form_11 RS :=
  ⟨fun _ => Complex.I / 2⟩

def Form_11.IsRealValued {RS : RiemannSurface} (ω : Form_11 RS) : Prop :=
  ∀ p, (ω.toSection p).im = 0

def Form_11.IsPositive {RS : RiemannSurface} (ω : Form_11 RS) : Prop :=
  ∀ p, 0 < (ω.toSection p).im

end RiemannSurfaces.Analytic
