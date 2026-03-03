import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.HodgeDecomposition.Core

namespace RiemannSurfaces.Analytic

open Complex Topology
open scoped Manifold

variable {RS : RiemannSurface}

/-!
## Additive Operator Packaging

Reusable additive-map interfaces for exact/image submodule constructions.
-/

/-- Additive homomorphism `f ↦ ∂̄f` (local copy using `dbar_real_hd`). -/
noncomputable def dbarRealAddHom_hd (RS : RiemannSurface) :
    RealSmoothFunction RS →+ Form_01 RS where
  toFun := dbar_real_hd
  map_zero' := dbar_real_hd_zero (RS := RS)
  map_add' := dbar_real_hd_add (RS := RS)

-- ∂ on ℝ-smooth functions: linearity (from `dbar_real_hd` + conjugation)

theorem del_real_add (f g : RealSmoothFunction RS) :
    del_real (f + g) = del_real f + del_real g := by
  unfold del_real
  rw [RealSmoothFunction.conj_add, dbar_real_hd_add, Form_01.conj_add]

theorem del_real_zero : del_real (0 : RealSmoothFunction RS) = 0 := by
  unfold del_real
  rw [RealSmoothFunction.conj_zero, dbar_real_hd_zero, Form_01.conj_zero]

theorem del_real_const_mul (c : ℂ) (f : RealSmoothFunction RS) :
    del_real (RealSmoothFunction.const c * f) = c • del_real f := by
  unfold del_real
  have hconst_conj :
      (RealSmoothFunction.const c : RealSmoothFunction RS).conj =
        RealSmoothFunction.const (starRingEnd ℂ c) := by
    ext p
    simp [RealSmoothFunction.const, RealSmoothFunction.conj_toFun]
  rw [RealSmoothFunction.conj_mul, hconst_conj, dbar_real_hd_const_mul, Form_01.conj_smul]
  simp

theorem del_real_smul (c : ℂ) (f : RealSmoothFunction RS) :
    del_real (c • f) = c • del_real f := by
  simpa [RealSmoothFunction.smul_def] using del_real_const_mul (RS := RS) c f

/-- Additive homomorphism `f ↦ (∂f, ∂̄f)` into complex-valued 1-form pairs. -/
noncomputable def exactForms1AddHom (RS : RiemannSurface) :
    RealSmoothFunction RS →+ (Form_10 RS × Form_01 RS) where
  toFun := fun f => (del_real f, dbar_real_hd f)
  map_zero' := by
    ext <;> simp [del_real_zero, dbar_real_hd_zero]
  map_add' := by
    intro f g
    ext <;> simp [del_real_add, dbar_real_hd_add]

/-- Linear map package of `f ↦ ∂̄f` over `ℂ`. -/
noncomputable def dbarRealLinearMap_hd (RS : RiemannSurface) :
    RealSmoothFunction RS →ₗ[ℂ] Form_01 RS where
  toFun := dbar_real_hd
  map_add' := dbar_real_hd_add (RS := RS)
  map_smul' := dbar_real_hd_smul (RS := RS)

/-- Linear map package of `f ↦ (∂f, ∂̄f)` over `ℂ`. -/
noncomputable def exactForms1LinearMap (RS : RiemannSurface) :
    RealSmoothFunction RS →ₗ[ℂ] (Form_10 RS × Form_01 RS) where
  toFun := fun f => (del_real f, dbar_real_hd f)
  map_add' := by
    intro f g
    ext <;> simp [del_real_add, dbar_real_hd_add]
  map_smul' := by
    intro c f
    ext <;> simp [del_real_smul, dbar_real_hd_smul]

/-- Closed ℂ-valued 1-forms on a Riemann surface.
    A 1-form (α, β) ∈ Ω^{1,0} ⊕ Ω^{0,1} is closed iff dω = ∂̄α + ∂β = 0 in Ω^{1,1}. -/
def closedForms1 (RS : RiemannSurface) : Submodule ℂ (Form_10 RS × Form_01 RS) where
  carrier := { ω | dbar_10 ω.1 + del_01 ω.2 = 0 }
  add_mem' := by
    intro a b ha hb
    show dbar_10 (a.1 + b.1) + del_01 (a.2 + b.2) = 0
    rw [dbar_10_add, del_01_add]
    have : (dbar_10 a.1 + dbar_10 b.1) + (del_01 a.2 + del_01 b.2) =
        (dbar_10 a.1 + del_01 a.2) + (dbar_10 b.1 + del_01 b.2) := by abel
    rw [this, ha, hb, add_zero]
  zero_mem' := by
    have hdbar0 : dbar_10 (0 : Form_10 RS) = 0 := by
      have : (0 : Form_10 RS) = (0 : ℂ) • (0 : Form_10 RS) := by simp
      rw [this, dbar_10_smul, zero_smul]
    have hdel0 : del_01 (0 : Form_01 RS) = 0 := by
      have : (0 : Form_01 RS) = (0 : ℂ) • (0 : Form_01 RS) := by simp
      rw [this, del_01_smul, zero_smul]
    show dbar_10 0 + del_01 0 = 0
    rw [hdbar0, hdel0, add_zero]
  smul_mem' := by
    intro c ω hω
    show dbar_10 (c • ω.1) + del_01 (c • ω.2) = 0
    rw [dbar_10_smul, del_01_smul, ← smul_add, hω, smul_zero]

/-- Exact 1-forms: df = (∂f, ∂̄f) for ℝ-smooth f.
    These form a submodule since d is ℂ-linear on functions. -/
def exactForms1 (RS : RiemannSurface) : Submodule ℂ (Form_10 RS × Form_01 RS) where
  carrier := { ω | ∃ f : RealSmoothFunction RS, ω.1 = del_real f ∧ ω.2 = dbar_real_hd f }
  add_mem' := by
    intro a b ⟨f, hf1, hf2⟩ ⟨g, hg1, hg2⟩
    refine ⟨f + g, ?_, ?_⟩
    · show a.1 + b.1 = del_real (f + g)
      rw [del_real_add, ← hf1, ← hg1]
    · show a.2 + b.2 = dbar_real_hd (f + g)
      rw [dbar_real_hd_add, ← hf2, ← hg2]
  zero_mem' := ⟨0, by show (0 : Form_10 RS) = del_real 0; rw [del_real_zero],
    by show (0 : Form_01 RS) = dbar_real_hd 0; rw [dbar_real_hd_zero]⟩
  smul_mem' := by
    intro c ω ⟨f, hf1, hf2⟩
    refine ⟨c • f, ?_, ?_⟩
    · show c • ω.1 = del_real (c • f)
      rw [del_real_smul, ← hf1]
    · show c • ω.2 = dbar_real_hd (c • f)
      rw [dbar_real_hd_smul, ← hf2]

/-- Additive content of `exactForms1`: it is exactly the range of `exactForms1AddHom`. -/
theorem exactForms1_toAddSubgroup_eq_range (RS : RiemannSurface) :
    (exactForms1 RS).toAddSubgroup = (exactForms1AddHom (RS := RS)).range := by
  ext ω
  constructor
  · intro hω
    rcases hω with ⟨f, hf1, hf2⟩
    exact ⟨f, Prod.ext hf1.symm hf2.symm⟩
  · intro hω
    rcases hω with ⟨f, hf⟩
    exact ⟨f, (congrArg Prod.fst hf).symm, (congrArg Prod.snd hf).symm⟩

/-- Linear content of `exactForms1`: it is exactly the range of `exactForms1LinearMap`. -/
theorem exactForms1_eq_range_linearMap (RS : RiemannSurface) :
    exactForms1 RS = (exactForms1LinearMap (RS := RS)).range := by
  ext ω
  constructor
  · intro hω
    rcases hω with ⟨f, hf1, hf2⟩
    exact ⟨f, Prod.ext hf1.symm hf2.symm⟩
  · intro hω
    rcases hω with ⟨f, hf⟩
    exact ⟨f, (congrArg Prod.fst hf).symm, (congrArg Prod.snd hf).symm⟩

/-- De Rham cohomology H¹_dR(X, ℂ) = closed 1-forms / exact 1-forms.

    A 1-form ω = α dz + β dz̄ is closed iff ∂̄α + ∂β = 0.
    It is exact iff (α, β) = (∂f, ∂̄f) for some ℝ-smooth f.

    For a compact Riemann surface of genus g, dim H¹_dR = 2g.
    By the Hodge theorem, H¹_dR ≅ H^{1,0} ⊕ H^{0,1} (harmonic representatives). -/
noncomputable def DeRhamH1 (CRS : CompactRiemannSurface) : Type _ :=
  (↥(closedForms1 CRS.toRiemannSurface)) ⧸
    (Submodule.comap (closedForms1 CRS.toRiemannSurface).subtype
      (exactForms1 CRS.toRiemannSurface)).toAddSubgroup

/-- Exact closed 1-forms viewed inside `closedForms1`, as an additive subgroup. -/
noncomputable def exactClosedForms1AddSubgroup (CRS : CompactRiemannSurface) :
    AddSubgroup ↥(closedForms1 CRS.toRiemannSurface) :=
  (Submodule.comap (closedForms1 CRS.toRiemannSurface).subtype
    (exactForms1 CRS.toRiemannSurface)).toAddSubgroup

/-- Equality criterion for de Rham classes. -/
theorem deRham_mk_eq_mk_iff (CRS : CompactRiemannSurface)
    (ω₁ ω₂ : ↥(closedForms1 CRS.toRiemannSurface)) :
    (QuotientAddGroup.mk ω₁ : DeRhamH1 CRS) = QuotientAddGroup.mk ω₂ ↔
      -ω₁ + ω₂ ∈ exactClosedForms1AddSubgroup CRS := by
  simpa [DeRhamH1, exactClosedForms1AddSubgroup] using
    (QuotientAddGroup.eq (a := ω₁) (b := ω₂)
      (s := (exactClosedForms1AddSubgroup CRS)))

/-- Zero criterion for de Rham classes. -/
theorem deRham_mk_eq_zero_iff (CRS : CompactRiemannSurface)
    (ω : ↥(closedForms1 CRS.toRiemannSurface)) :
    (QuotientAddGroup.mk ω : DeRhamH1 CRS) = 0 ↔
      ω ∈ exactClosedForms1AddSubgroup CRS := by
  simpa [DeRhamH1, exactClosedForms1AddSubgroup] using
    (QuotientAddGroup.eq_zero_iff
      (N := exactClosedForms1AddSubgroup CRS) ω)

/-- Membership in `exactClosedForms1AddSubgroup` means the underlying closed pair
is exact as a `(∂f, ∂̄f)` pair. -/
theorem mem_exactClosedForms1AddSubgroup_iff_exists (CRS : CompactRiemannSurface)
    (ω : ↥(closedForms1 CRS.toRiemannSurface)) :
    ω ∈ exactClosedForms1AddSubgroup CRS ↔
      ∃ f : RealSmoothFunction CRS.toRiemannSurface,
        (ω : Form_10 CRS.toRiemannSurface × Form_01 CRS.toRiemannSurface).1 = del_real f ∧
        (ω : Form_10 CRS.toRiemannSurface × Form_01 CRS.toRiemannSurface).2 = dbar_real_hd f := by
  constructor <;> intro hω
  · exact hω
  · exact hω

end RiemannSurfaces.Analytic
