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

/-- The canonical and local-copy `∂̄` operators coincide pointwise on coefficients. -/
theorem dbar_real_eq_dbar_real_hd (f : RealSmoothFunction RS) :
    dbar_real (RS := RS) f = dbar_real_hd (RS := RS) f := by
  ext p
  rfl

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

theorem dbar_real_smul (c : ℂ) (f : RealSmoothFunction RS) :
    dbar_real (c • f) = c • dbar_real f := by
  simpa [RealSmoothFunction.smul_def] using dbar_real_const_mul (RS := RS) c f

/-- Additive homomorphism `f ↦ ∂̄f`. -/
noncomputable def dbarRealAddHom (RS : RiemannSurface) :
    RealSmoothFunction RS →+ Form_01 RS where
  toFun := dbar_real
  map_zero' := dbar_real_zero (RS := RS)
  map_add' := dbar_real_add (RS := RS)

/-- Linear map `f ↦ ∂̄f` over `ℂ`. -/
noncomputable def dbarRealLinearMap (RS : RiemannSurface) :
    RealSmoothFunction RS →ₗ[ℂ] Form_01 RS where
  toFun := dbar_real
  map_add' := dbar_real_add (RS := RS)
  map_smul' := dbar_real_smul (RS := RS)

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
    exact ⟨c • f, by rw [dbar_real_smul, hf]⟩

/-- Additive content of `dbarImage`: it is exactly the range of `dbarRealAddHom`. -/
theorem dbarImage_toAddSubgroup_eq_range (RS : RiemannSurface) :
    (dbarImage RS).toAddSubgroup = (dbarRealAddHom (RS := RS)).range := by
  ext ω
  constructor
  · intro hω
    rcases hω with ⟨f, rfl⟩
    exact ⟨f, rfl⟩
  · intro hω
    rcases hω with ⟨f, rfl⟩
    exact ⟨f, rfl⟩

/-- Linear content of `dbarImage`: it is exactly the range of `dbarRealLinearMap`. -/
theorem dbarImage_eq_range_linearMap (RS : RiemannSurface) :
    dbarImage RS = (dbarRealLinearMap (RS := RS)).range := by
  ext ω
  constructor
  · intro hω
    rcases hω with ⟨f, rfl⟩
    exact ⟨f, rfl⟩
  · intro hω
    rcases hω with ⟨f, rfl⟩
    exact ⟨f, rfl⟩

/-- The canonical and local-copy `∂̄` image submodules coincide. -/
theorem dbarImage_eq_dbarImage_hd (RS : RiemannSurface) :
    dbarImage RS = dbarImage_hd RS := by
  ext ω
  constructor
  · intro hω
    rcases hω with ⟨f, hf⟩
    refine ⟨f, ?_⟩
    simpa [dbar_real_eq_dbar_real_hd (RS := RS) f] using hf
  · intro hω
    rcases hω with ⟨f, hf⟩
    refine ⟨f, ?_⟩
    simpa [dbar_real_eq_dbar_real_hd (RS := RS) f] using hf

/-- The Dolbeault cohomology group H^{0,1}(X, O) = Ω^{0,1}(X) / im(∂̄).

    This is the proper analytic definition of the first cohomology group
    of the structure sheaf. By the Hodge theorem, this is isomorphic to
    the space of harmonic (0,1)-forms and has dimension g (the topological genus).

    **Note on the ∂̄ operator used:** We use `dbar_real` which acts on
    ℝ-smooth functions (not the trivially-zero `dbar_fun` on holomorphic functions). -/
def DolbeaultH01 (RS : RiemannSurface) := Form_01 RS ⧸ dbarImage RS

/-- Normal form of Dolbeault quotient using the linear-map image. -/
theorem DolbeaultH01_eq_quotient_linearRange (RS : RiemannSurface) :
    DolbeaultH01 RS = (Form_01 RS ⧸ (dbarRealLinearMap (RS := RS)).range) := by
  simp [DolbeaultH01, dbarImage_eq_range_linearMap]

/-- For compact surfaces, the local-copy and canonical Dolbeault quotients coincide. -/
theorem SheafH1O_eq_DolbeaultH01 (CRS : CompactRiemannSurface) :
    SheafH1O CRS = DolbeaultH01 CRS.toRiemannSurface := by
  simp [SheafH1O, DolbeaultH01, dbarImage_eq_dbarImage_hd]

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
  let RS := CRS.toRiemannSurface
  obtain ⟨isoSheaf, hbijSheaf⟩ := dolbeault_isomorphism_01 CRS
  let eSheafToDolbeault : SheafH1O CRS ≃ DolbeaultH01 RS :=
    Equiv.cast (SheafH1O_eq_DolbeaultH01 CRS)
  let harmonicToDolbeault : Harmonic01Forms RS → DolbeaultH01 RS :=
    fun η => eSheafToDolbeault (isoSheaf η)
  have hbij_harmonicToDolbeault : Function.Bijective harmonicToDolbeault := by
    exact eSheafToDolbeault.bijective.comp hbijSheaf
  let eDolbeault : Harmonic01Forms RS ≃ DolbeaultH01 RS :=
    Equiv.ofBijective harmonicToDolbeault hbij_harmonicToDolbeault
  refine ⟨eDolbeault.symm, ?_⟩
  exact eDolbeault.symm.bijective

/-- Canonical equivalence package extracted from `dolbeault_hodge_iso`. -/
noncomputable def dolbeaultHodgeEquiv (CRS : CompactRiemannSurface) :
    DolbeaultH01 CRS.toRiemannSurface ≃ Harmonic01Forms CRS.toRiemannSurface := by
  classical
  exact Equiv.ofBijective
    (Classical.choose (dolbeault_hodge_iso CRS))
    (Classical.choose_spec (dolbeault_hodge_iso CRS))

/-- Linear-bijective Dolbeault/Hodge bridge from exact-harmonic vanishing. -/
theorem dolbeault_hodge_linear_bijective_of_exact_harmonic01_vanishes
    (CRS : CompactRiemannSurface)
    (hvanish :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        (dbar_real_hd f).IsHarmonic →
          dbar_real_hd f = 0) :
    ∃ f : DolbeaultH01 CRS.toRiemannSurface →ₗ[ℂ]
      Harmonic01Forms CRS.toRiemannSurface,
      Function.Bijective f := by
  let RS := CRS.toRiemannSurface
  obtain ⟨fSheaf, hfSheaf⟩ :=
    dolbeault_isomorphism_01_linear_of_exact_harmonic01_vanishes CRS hvanish
  let hSheaf : SheafH1O CRS = DolbeaultH01 RS := SheafH1O_eq_DolbeaultH01 CRS
  let eSheafToDolbeault : SheafH1O CRS ≃ₗ[ℂ] DolbeaultH01 RS :=
    { toEquiv := Equiv.cast hSheaf
      map_add' := by
        intro x y
        cases hSheaf
        rfl
      map_smul' := by
        intro c x
        cases hSheaf
        rfl }
  let eHarmToDolbeault : Harmonic01Forms RS ≃ₗ[ℂ] DolbeaultH01 RS :=
    (LinearEquiv.ofBijective fSheaf hfSheaf).trans eSheafToDolbeault
  refine ⟨eHarmToDolbeault.symm, ?_⟩
  exact eHarmToDolbeault.symm.bijective

/-- If `DolbeaultH01` is identified with `Harmonic01Forms` via a bijection, then
there exists an injective genus-indexed family in `DolbeaultH01`.
This is a reusable lower-bound bridge independent of finrank machinery. -/
theorem dolbeault_has_genus_injective_family_of_bijective
    (CRS : CompactRiemannSurface)
    (f : DolbeaultH01 CRS.toRiemannSurface → Harmonic01Forms CRS.toRiemannSurface)
    (hf : Function.Bijective f) :
    ∃ (basis : Fin CRS.genus → DolbeaultH01 CRS.toRiemannSurface),
      Function.Injective basis := by
  obtain ⟨basisH, hbasisH⟩ := dim_harmonic_01_eq_genus CRS
  let e : DolbeaultH01 CRS.toRiemannSurface ≃ Harmonic01Forms CRS.toRiemannSurface :=
    Equiv.ofBijective f hf
  refine ⟨fun i => e.symm (basisH i), ?_⟩
  intro i j hij
  apply hbasisH
  simpa using congrArg e hij

/-- `DolbeaultH01` carries an injective genus-indexed family.
Obtained from `dolbeault_hodge_iso` and `dim_harmonic_01_eq_genus`. -/
theorem dolbeault_has_genus_injective_family (CRS : CompactRiemannSurface) :
    ∃ (basis : Fin CRS.genus → DolbeaultH01 CRS.toRiemannSurface),
      Function.Injective basis := by
  obtain ⟨f, hf⟩ := dolbeault_hodge_iso CRS
  exact dolbeault_has_genus_injective_family_of_bijective CRS f hf

/-- Linear-structure bridge for `h1_trivial_eq_genus`:
if Dolbeault cohomology is linearly equivalent to harmonic `(0,1)` forms and
the harmonic side has finrank `g`, then `h¹(O)=g`. -/
theorem h1_trivial_eq_genus_of_linearEquiv
    (CRS : CompactRiemannSurface)
    (e : DolbeaultH01 CRS.toRiemannSurface ≃ₗ[ℂ]
      Harmonic01Forms CRS.toRiemannSurface)
    (hfin_harm : Module.finrank ℂ (Harmonic01Forms CRS.toRiemannSurface) = CRS.genus) :
    h1_dolbeault_trivial CRS = CRS.genus := by
  unfold h1_dolbeault_trivial
  rw [LinearEquiv.finrank_eq e, hfin_harm]

/-- Variant of `h1_trivial_eq_genus_of_linearEquiv` using a bijective linear map. -/
theorem h1_trivial_eq_genus_of_linearMap_bijective
    (CRS : CompactRiemannSurface)
    (f : DolbeaultH01 CRS.toRiemannSurface →ₗ[ℂ]
      Harmonic01Forms CRS.toRiemannSurface)
    (hf : Function.Bijective f)
    (hfin_harm : Module.finrank ℂ (Harmonic01Forms CRS.toRiemannSurface) = CRS.genus) :
    h1_dolbeault_trivial CRS = CRS.genus := by
  exact h1_trivial_eq_genus_of_linearEquiv CRS (LinearEquiv.ofBijective f hf) hfin_harm

/-- h¹(O) = g (topological genus).

    Here g = CRS.genus is the TOPOLOGICAL genus of the surface.

    Current formal bridge status:
    1. `dolbeault_hodge_iso` gives a bijection `DolbeaultH01 ≃ Harmonic01Forms`.
    2. `dim_harmonic_01_eq_genus` gives an injective `Fin g → Harmonic01Forms`.
    3. `dolbeault_has_genus_injective_family` transports this to `DolbeaultH01`.
    4. Remaining gap: close the finrank equality (upper-bound / finite-dimensional closure). -/
theorem h1_trivial_eq_genus (CRS : CompactRiemannSurface) :
    h1_dolbeault_trivial CRS = CRS.genus := by
  have hvanish :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        (dbar_real_hd f).IsHarmonic →
          dbar_real_hd f = 0 :=
    exact_harmonic01_vanishes CRS
  obtain ⟨f, hf⟩ :=
    dolbeault_hodge_linear_bijective_of_exact_harmonic01_vanishes CRS hvanish
  have hfin_harm :
      Module.finrank ℂ (Harmonic01Forms CRS.toRiemannSurface) = CRS.genus :=
    finrank_harmonic01_eq_genus CRS
  exact h1_trivial_eq_genus_of_linearMap_bijective CRS f hf hfin_harm

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

theorem dbar_twisted_smul (A : Form_01 RS) (c : ℂ) (f : RealSmoothFunction RS) :
    dbar_twisted A (c • f) = c • dbar_twisted A f := by
  simpa [RealSmoothFunction.smul_def] using dbar_twisted_const_mul (RS := RS) A c f

/-- Additive homomorphism `f ↦ ∂̄_A f`. -/
noncomputable def dbarTwistedAddHom (RS : RiemannSurface) (A : Form_01 RS) :
    RealSmoothFunction RS →+ Form_01 RS where
  toFun := dbar_twisted A
  map_zero' := dbar_twisted_zero (RS := RS) A
  map_add' := dbar_twisted_add (RS := RS) A

/-- Linear map `f ↦ ∂̄_A f` over `ℂ`. -/
noncomputable def dbarTwistedLinearMap (RS : RiemannSurface) (A : Form_01 RS) :
    RealSmoothFunction RS →ₗ[ℂ] Form_01 RS where
  toFun := dbar_twisted A
  map_add' := dbar_twisted_add (RS := RS) A
  map_smul' := dbar_twisted_smul (RS := RS) A

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
    exact ⟨c • f, by rw [dbar_twisted_smul, hf]⟩

/-- Additive content of `twistedDbarImage`: it is the range of `dbarTwistedAddHom`. -/
theorem twistedDbarImage_toAddSubgroup_eq_range (RS : RiemannSurface) (A : Form_01 RS) :
    (twistedDbarImage RS A).toAddSubgroup = (dbarTwistedAddHom (RS := RS) A).range := by
  ext ω
  constructor
  · intro hω
    rcases hω with ⟨f, rfl⟩
    exact ⟨f, rfl⟩
  · intro hω
    rcases hω with ⟨f, rfl⟩
    exact ⟨f, rfl⟩

/-- Linear content of `twistedDbarImage`: it is the range of `dbarTwistedLinearMap`. -/
theorem twistedDbarImage_eq_range_linearMap (RS : RiemannSurface) (A : Form_01 RS) :
    twistedDbarImage RS A = (dbarTwistedLinearMap (RS := RS) A).range := by
  ext ω
  constructor
  · intro hω
    rcases hω with ⟨f, rfl⟩
    exact ⟨f, rfl⟩
  · intro hω
    rcases hω with ⟨f, rfl⟩
    exact ⟨f, rfl⟩

/-- Twisted Dolbeault cohomology H^{0,1}(O(D)) = Ω^{0,1} / im(∂̄_A).

    For A = 0, this is the ordinary Dolbeault cohomology `DolbeaultH01`.
    For general A (encoding a line bundle O(D)), this gives H^{0,1}(O(D)). -/
noncomputable def TwistedDolbeaultH01 (RS : RiemannSurface) (A : Form_01 RS) :=
  Form_01 RS ⧸ twistedDbarImage RS A

/-- Normal form of twisted Dolbeault quotient using the twisted linear-map image. -/
theorem TwistedDolbeaultH01_eq_quotient_linearRange (RS : RiemannSurface) (A : Form_01 RS) :
    TwistedDolbeaultH01 RS A =
      (Form_01 RS ⧸ (dbarTwistedLinearMap (RS := RS) A).range) := by
  simp [TwistedDolbeaultH01, twistedDbarImage_eq_range_linearMap]

noncomputable instance twistedDolbeaultAddCommGroup (RS : RiemannSurface) (A : Form_01 RS) :
    AddCommGroup (TwistedDolbeaultH01 RS A) :=
  Submodule.Quotient.addCommGroup _

noncomputable instance twistedDolbeaultModule (RS : RiemannSurface) (A : Form_01 RS) :
    Module ℂ (TwistedDolbeaultH01 RS A) :=
  Submodule.Quotient.module _

end RiemannSurfaces.Analytic
