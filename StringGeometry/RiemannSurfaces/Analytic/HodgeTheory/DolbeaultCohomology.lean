import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.HodgeDecomposition

/-!
# Dolbeault Cohomology H^{0,1}

This file defines the Dolbeault cohomology group H^{0,1}(X, O) = Ω^{0,1} / im(∂̄)
for a Riemann surface X.

## Critical distinction: ℂ-smooth vs ℝ-smooth

The existing `dbar_fun : SmoothFunction RS → Form_01 RS` acts on `SmoothFunction`,
which requires `ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ⊤` (holomorphic). Since ∂̄(holomorphic) = 0,
this operator is trivially zero. For non-trivial Dolbeault cohomology, we need ∂̄ acting
on the **larger** space of ℝ-smooth functions `RealSmoothFunction RS`.

## Main definitions

* `dbar_real` — The ∂̄ operator on ℝ-smooth functions: Ω^{0,0}_ℝ → Ω^{0,1}
* `dbarImage RS` — The image of ∂̄ : Ω^{0,0}_ℝ → Ω^{0,1} as a ℂ-submodule
* `DolbeaultH01 RS` — H^{0,1}(X, O) = Ω^{0,1} / im(∂̄)
* `h1_dolbeault_trivial CRS` — h¹(O) = dim_ℂ H^{0,1}

## Key theorems (with sorrys depending on Hodge theory)

* `dolbeault_hodge_iso` — H^{0,1} ≅ Harmonic01Forms (Hodge decomposition)
* `h1_trivial_eq_genus` — h¹(O) = g (topological genus)
-/

namespace RiemannSurfaces.Analytic

open Complex Topology Classical

/-!
## The ∂̄-operator on ℝ-smooth functions

The key operator for Dolbeault cohomology. Unlike `dbar_fun` which acts on
holomorphic functions (and is trivially zero), `dbar_real` acts on
ℝ-smooth functions and produces non-trivial (0,1)-forms.
-/

/-- Smoothness infrastructure for `dbar_real`.

This isolates the genuine manifold-analytic proof obligation away from the
`def` body, in line with the local agent rule forbidding `sorry` inside defs. -/
private theorem dbar_real_smooth_section (f : RealSmoothFunction RS) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) smoothOrder
      (fun p : RS.carrier =>
      let e := @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p
      wirtingerDeriv_zbar (f.toFun ∘ e.symm) (e p)) := by
  simpa [dbar_real_hd] using (dbar_real_hd (RS := RS) f).smooth'

/-- The ∂̄-operator on ℝ-smooth functions: Ω^{0,0}_ℝ(X) → Ω^{0,1}(X).

    For f : X → ℂ a ℝ-smooth function, (∂̄f)(p) = (∂f/∂z̄)(chart(p)) where
    z = chart(p) is a local coordinate.

    This is the non-trivial version of ∂̄ — unlike `dbar_fun` (which acts on
    holomorphic functions and is always zero), `dbar_real` acts on the larger
    space of ℝ-smooth functions and produces non-zero (0,1)-forms in general.

    A function f is holomorphic iff ∂̄_real f = 0. -/
noncomputable def dbar_real (f : RealSmoothFunction RS) : Form_01 RS where
  toSection := fun p =>
    letI := RS.topology
    letI := RS.chartedSpace
    let e := @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p
    wirtingerDeriv_zbar (f.toFun ∘ e.symm) (e p)
  smooth' := dbar_real_smooth_section f

/-- Helper: extract DifferentiableAt from RealSmoothFunction. -/
private theorem realSmooth_differentiableAt_chart (f : RealSmoothFunction RS) (p : RS.carrier) :
    letI := RS.topology
    letI := RS.chartedSpace
    haveI := RS.isManifold
    DifferentiableAt ℝ (f.toFun ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) := by
  letI := RS.topology; letI := RS.chartedSpace; haveI := RS.isManifold
  haveI := isManifold_real_of_complex (M := RS.carrier)
  exact Infrastructure.differentiableAt_chart_comp_smoothOrder f.smooth' p

theorem dbar_real_add (f g : RealSmoothFunction RS) :
    dbar_real (f + g) = dbar_real f + dbar_real g := by
  ext p
  show (dbar_real (f + g)).toSection p = ((dbar_real f) + (dbar_real g)).toSection p
  simp only [Form_01.add_toSection]
  -- Both sides unfold to wirtingerDerivBar applied to compositions with chart
  show wirtingerDeriv_zbar ((f + g).toFun ∘ _) _ =
    wirtingerDeriv_zbar (f.toFun ∘ _) _ + wirtingerDeriv_zbar (g.toFun ∘ _) _
  simp only [wirtingerDeriv_zbar]
  -- The composition (f+g) ∘ e.symm = (f ∘ e.symm) + (g ∘ e.symm) pointwise
  letI := RS.topology; letI := RS.chartedSpace; haveI := RS.isManifold
  have hcomp : (f + g).toFun ∘ (chartAt ℂ p).symm =
      (f.toFun ∘ (chartAt ℂ p).symm) + (g.toFun ∘ (chartAt ℂ p).symm) :=
    funext fun z => by simp [RealSmoothFunction.add_toFun]
  rw [hcomp]
  exact Infrastructure.wirtingerDerivBar_add
    (realSmooth_differentiableAt_chart f p) (realSmooth_differentiableAt_chart g p)

theorem dbar_real_zero : dbar_real (0 : RealSmoothFunction RS) = 0 := by
  ext p
  show (dbar_real (0 : RealSmoothFunction RS)).toSection p = (0 : Form_01 RS).toSection p
  simp only [Form_01.zero_toSection]
  show wirtingerDeriv_zbar ((0 : RealSmoothFunction RS).toFun ∘ _) _ = 0
  simp only [wirtingerDeriv_zbar]
  letI := RS.topology; letI := RS.chartedSpace; haveI := RS.isManifold
  have hcomp : (0 : RealSmoothFunction RS).toFun ∘ (chartAt ℂ p).symm = fun _ => (0 : ℂ) :=
    funext fun z => by simp [RealSmoothFunction.zero_toFun]
  rw [hcomp]
  exact Infrastructure.wirtingerDerivBar_const 0

/-- ∂̄(c · f) = c · ∂̄f for constant c ∈ ℂ and ℝ-smooth f.
    Here scalar multiplication on RealSmoothFunction is via const(c) * f. -/
theorem dbar_real_const_mul (c : ℂ) (f : RealSmoothFunction RS) :
    dbar_real (RealSmoothFunction.const c * f) = c • dbar_real f := by
  ext p
  show (dbar_real (RealSmoothFunction.const c * f)).toSection p = (c • dbar_real f).toSection p
  simp only [Form_01.smul_toSection]
  show wirtingerDeriv_zbar ((RealSmoothFunction.const c * f).toFun ∘ _) _ =
    c * wirtingerDeriv_zbar (f.toFun ∘ _) _
  simp only [wirtingerDeriv_zbar]
  letI := RS.topology; letI := RS.chartedSpace; haveI := RS.isManifold
  -- (const c * f) ∘ e.symm = c • (f ∘ e.symm)
  have hcomp : (RealSmoothFunction.const c * f).toFun ∘ (chartAt ℂ p).symm =
      c • (f.toFun ∘ (chartAt ℂ p).symm) :=
    funext fun z => by
      simp only [Function.comp_apply, RealSmoothFunction.mul_toFun,
        Pi.smul_apply, smul_eq_mul, RealSmoothFunction.const]
  rw [hcomp]
  exact Infrastructure.wirtingerDerivBar_const_smul c (realSmooth_differentiableAt_chart f p)

/-- Holomorphic functions have ∂̄ = 0 (consistent with dbar_fun). -/
theorem dbar_real_of_holomorphic (f : SmoothFunction RS) :
    dbar_real f.toRealSmooth = 0 := by
  -- dbar_real f.toRealSmooth has the same section as dbar_fun f
  -- (since f.toRealSmooth.toFun = f.toFun definitionally)
  have heq : dbar_real f.toRealSmooth = dbar_fun f := by
    apply Form_01.ext; funext p; rfl
  have hzero : dbar_fun f = 0 := dbar_fun_eq_zero f
  exact heq.trans hzero

/-- A (0,1)-form is ∂̄-exact (in the ℝ-smooth sense) if it's in the image
    of ∂̄ : Ω^{0,0}_ℝ → Ω^{0,1}. -/
def Form_01.IsDbarExactReal (ω : Form_01 RS) : Prop :=
  ∃ f : RealSmoothFunction RS, dbar_real f = ω

/-- The image of ∂̄ : Ω^{0,0}_ℝ(X) → Ω^{0,1}(X) as a ℂ-submodule of Ω^{0,1}.

    An element ω ∈ Ω^{0,1} is in the image iff ω = ∂̄f for some ℝ-smooth function f. -/
def dbarImage (RS : RiemannSurface) : Submodule ℂ (Form_01 RS) where
  carrier := { ω | ω.IsDbarExactReal }
  add_mem' := by
    intro ω₁ ω₂ ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩
    exact ⟨f₁ + f₂, by rw [dbar_real_add, hf₁, hf₂]⟩
  zero_mem' := ⟨0, dbar_real_zero⟩
  smul_mem' := by
    intro c ω ⟨f, hf⟩
    exact ⟨RealSmoothFunction.const c * f, by rw [dbar_real_const_mul, hf]⟩

/-- The Dolbeault cohomology group H^{0,1}(X, O) = Ω^{0,1}(X) / im(∂̄).

    This is the proper analytic definition of the first cohomology group
    of the structure sheaf. By the Hodge theorem, this is isomorphic to
    the space of harmonic (0,1)-forms and has dimension g (the topological genus).

    **Note on the ∂̄ operator used:** We use `dbar_real` which acts on
    ℝ-smooth functions (not the trivially-zero `dbar_fun` on holomorphic functions). -/
def DolbeaultH01 (RS : RiemannSurface) := Form_01 RS ⧸ dbarImage RS

/-- H^{0,1}(X, O) inherits an AddCommGroup structure from the quotient. -/
noncomputable instance (RS : RiemannSurface) : AddCommGroup (DolbeaultH01 RS) :=
  Submodule.Quotient.addCommGroup _

/-- H^{0,1}(X, O) inherits a ℂ-module structure from the quotient. -/
noncomputable instance (RS : RiemannSurface) : Module ℂ (DolbeaultH01 RS) :=
  Submodule.Quotient.module _

/-- h¹(O) = dim_ℂ H^{0,1}(X, O) = dim_ℂ (Ω^{0,1} / im ∂̄).

    This is the proper analytic definition of h¹ for the trivial bundle.
    By the Hodge theorem, this equals the topological genus g. -/
noncomputable def h1_dolbeault_trivial (CRS : CompactRiemannSurface) : ℕ :=
  Module.finrank ℂ (DolbeaultH01 CRS.toRiemannSurface)

/-!
## Connection to Hodge Theory

The Hodge theorem gives a canonical isomorphism H^{0,1} ≅ Harmonic01Forms,
identifying each Dolbeault class with its unique harmonic representative.
-/

/-- Hodge theorem: H^{0,1}(X, O) ≅ Harmonic01Forms(X) (as sets, via bijection).

    Every class in H^{0,1} has a unique harmonic representative.
    This follows from the Hodge decomposition:
    every (0,1)-form ω decomposes as ω = ω_harm + ∂̄f (with f ℝ-smooth).

    Note: Harmonic01Forms is a subtype of Form_01, not yet equipped with
    Module ℂ structure. The bijection is stated at the type level. -/
theorem dolbeault_hodge_iso (CRS : CompactRiemannSurface) :
    ∃ (f : DolbeaultH01 CRS.toRiemannSurface → Harmonic01Forms CRS.toRiemannSurface),
      Function.Bijective f := by
  sorry -- Requires: Hodge decomposition (every ω = ω_harm + ∂̄f with f ℝ-smooth)
         -- + uniqueness of harmonic representative

/-- h¹(O) = g (topological genus).

    **Proof chain:**
    1. H^{0,1}(X, O) ≅ Harmonic01Forms(X)  (Hodge decomposition: dolbeault_hodge_iso)
    2. Harmonic01Forms(X) ≅ conj(Harmonic10Forms(X))  (conjugate_harmonic_iso, PROVEN)
    3. dim Harmonic10Forms(X) = g  (Hodge theorem: dim_harmonic_10_eq_genus)

    Here g = CRS.genus is the TOPOLOGICAL genus of the surface. This theorem
    connects the analytic invariant dim H^{0,1} to the topological invariant g. -/
theorem h1_trivial_eq_genus (CRS : CompactRiemannSurface) :
    h1_dolbeault_trivial CRS = CRS.genus := by
  sorry -- from dolbeault_hodge_iso + conjugate_harmonic_iso_bijective + dim_harmonic_10_eq_genus

/-!
## Twisted Dolbeault Cohomology H^{0,1}(O(D))

For a holomorphic line bundle O(D) on a compact Riemann surface X, the twisted
∂̄ operator acts on smooth sections of O(D). Since every line bundle on a surface
is smoothly trivial, we can identify smooth sections with smooth functions via a
smooth trivialization. In this trivialization, ∂̄_D becomes ∂̄ + A where
A ∈ Ω^{0,1}(X) is a (0,1)-connection form encoding the holomorphic structure.

The twisted Dolbeault cohomology is H^{0,1}(O(D)) = Ω^{0,1} / im(∂̄ + A).
Its dimension h¹(D) = dim_ℂ H^{0,1}(O(D)) is independent of the choice of
trivialization (different choices of A give isomorphic quotients).
-/

/-- The twisted ∂̄ operator: ∂̄_A(f) = ∂̄f + A · f, where A ∈ Ω^{0,1} is a
    connection form for a holomorphic line bundle.

    In a smooth trivialization of the line bundle O(D), the ∂̄ operator on
    smooth sections becomes ∂̄ + A where A encodes the holomorphic structure.
    For A = 0, this reduces to the ordinary ∂̄ operator `dbar_real`. -/
noncomputable def dbar_twisted (A : Form_01 RS) (f : RealSmoothFunction RS) :
    Form_01 RS where
  toSection := fun p => (dbar_real f).toSection p + f.toFun p * A.toSection p
  smooth' := by
    letI := RS.topology
    letI := RS.chartedSpace
    have hmul := contMDiff_mul_real f.smooth' A.smooth'
    exact (dbar_real f).smooth'.add hmul

/-- Twisted ∂̄ is additive: ∂̄_A(f+g) = ∂̄_A(f) + ∂̄_A(g). -/
private theorem dbar_twisted_add (A : Form_01 RS) (f g : RealSmoothFunction RS) :
    dbar_twisted A (f + g) = dbar_twisted A f + dbar_twisted A g := by
  apply Form_01.ext; funext p
  show (dbar_real (f + g)).toSection p + (f + g).toFun p * A.toSection p =
    ((dbar_real f).toSection p + f.toFun p * A.toSection p) +
    ((dbar_real g).toSection p + g.toFun p * A.toSection p)
  have h : (dbar_real (f + g)).toSection p =
      (dbar_real f).toSection p + (dbar_real g).toSection p := by
    rw [dbar_real_add]; rfl
  rw [h, RealSmoothFunction.add_toFun]; ring

/-- Twisted ∂̄ of zero is zero: ∂̄_A(0) = 0. -/
private theorem dbar_twisted_zero (A : Form_01 RS) :
    dbar_twisted A 0 = 0 := by
  apply Form_01.ext; funext p
  show (dbar_real 0).toSection p + (0 : RealSmoothFunction RS).toFun p * A.toSection p =
    (0 : Form_01 RS).toSection p
  have h : (dbar_real 0).toSection p = 0 := by rw [dbar_real_zero]; rfl
  rw [h, RealSmoothFunction.zero_toFun, Form_01.zero_toSection, zero_mul, add_zero]

/-- Twisted ∂̄ is ℂ-homogeneous: ∂̄_A(c·f) = c · ∂̄_A(f). -/
private theorem dbar_twisted_const_mul (A : Form_01 RS) (c : ℂ) (f : RealSmoothFunction RS) :
    dbar_twisted A (RealSmoothFunction.const c * f) = c • dbar_twisted A f := by
  apply Form_01.ext; funext p
  show (dbar_real (RealSmoothFunction.const c * f)).toSection p +
    (RealSmoothFunction.const c * f).toFun p * A.toSection p =
    c * ((dbar_real f).toSection p + f.toFun p * A.toSection p)
  have h : (dbar_real (RealSmoothFunction.const c * f)).toSection p =
      c * (dbar_real f).toSection p := by
    rw [dbar_real_const_mul]; rfl
  rw [h, RealSmoothFunction.mul_toFun]
  simp only [RealSmoothFunction.const]; ring

/-- Image of the twisted ∂̄_A operator as a submodule of Ω^{0,1}. -/
def twistedDbarImage (RS : RiemannSurface) (A : Form_01 RS) :
    Submodule ℂ (Form_01 RS) where
  carrier := { ω | ∃ f : RealSmoothFunction RS, dbar_twisted A f = ω }
  add_mem' := by
    intro a b ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨f + g, by rw [dbar_twisted_add, hf, hg]⟩
  zero_mem' := ⟨0, dbar_twisted_zero A⟩
  smul_mem' := by
    intro c ω ⟨f, hf⟩
    exact ⟨RealSmoothFunction.const c * f, by rw [dbar_twisted_const_mul, hf]⟩

/-- Twisted Dolbeault cohomology H^{0,1}(O(D)) = Ω^{0,1} / im(∂̄_A).

    For A = 0, this is the ordinary Dolbeault cohomology `DolbeaultH01`.
    For general A (encoding a line bundle O(D)), this gives H^{0,1}(O(D)). -/
noncomputable def TwistedDolbeaultH01 (RS : RiemannSurface) (A : Form_01 RS) :=
  Form_01 RS ⧸ twistedDbarImage RS A

noncomputable instance twistedDolbeaultAddCommGroup (RS : RiemannSurface) (A : Form_01 RS) :
    AddCommGroup (TwistedDolbeaultH01 RS A) :=
  Submodule.Quotient.addCommGroup _

noncomputable instance twistedDolbeaultModule (RS : RiemannSurface) (A : Form_01 RS) :
    Module ℂ (TwistedDolbeaultH01 RS A) :=
  Submodule.Quotient.module _

end RiemannSurfaces.Analytic
