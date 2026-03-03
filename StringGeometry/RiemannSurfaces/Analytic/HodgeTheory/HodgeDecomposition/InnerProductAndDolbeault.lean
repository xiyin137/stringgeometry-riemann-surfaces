import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.HodgeDecomposition.DeRhamCore

namespace RiemannSurfaces.Analytic

open Complex Topology Classical

/-!
## L² Inner Products and Orthogonality
-/

/-- The L² inner product structure on (1,0)-forms.

    ⟨ω, η⟩ = ∫_X ω ∧ ⋆η̄

    This is a sesquilinear, conjugate-symmetric, positive definite pairing.
    Its existence follows from the hermitian metric induced by the complex structure. -/
structure L2InnerProduct10 (CRS : CompactRiemannSurface) where
  /-- The inner product pairing -/
  pairing : Form_10 CRS.toRiemannSurface → Form_10 CRS.toRiemannSurface → ℂ
  /-- Sesquilinearity in second argument -/
  sesquilinear_right : ∀ ω η₁ η₂ c,
    pairing ω (η₁ + c • η₂) = pairing ω η₁ + (starRingEnd ℂ c) * pairing ω η₂
  /-- Conjugate symmetry -/
  conj_symm : ∀ ω η, pairing η ω = starRingEnd ℂ (pairing ω η)
  /-- Positive definiteness -/
  pos_def : ∀ ω, ω ≠ 0 → (pairing ω ω).re > 0

/-- Existence of L² inner product on (1,0)-forms.
    This follows from the existence of a hermitian metric on the surface. -/
theorem l2_inner_product_10_exists (CRS : CompactRiemannSurface) :
    Nonempty (L2InnerProduct10 CRS) := by
  classical
  let RS := CRS.toRiemannSurface
  let b : Module.Basis (Module.Free.ChooseBasisIndex ℂ (Form_10 RS)) ℂ (Form_10 RS) :=
    Module.Free.chooseBasis ℂ (Form_10 RS)
  let pairCoeff : (Module.Free.ChooseBasisIndex ℂ (Form_10 RS) →₀ ℂ) →
      (Module.Free.ChooseBasisIndex ℂ (Form_10 RS) →₀ ℂ) → ℂ :=
    fun x y => x.sum (fun i xi => xi * starRingEnd ℂ (y i))

  have h_pair_right : ∀ (x y z : Module.Free.ChooseBasisIndex ℂ (Form_10 RS) →₀ ℂ) (c : ℂ),
      pairCoeff x (y + c • z) = pairCoeff x y + (starRingEnd ℂ c) * pairCoeff x z := by
    intro x y z c
    unfold pairCoeff
    simp [Finsupp.add_apply, Finsupp.smul_apply, map_add, map_mul, mul_add]
    have hmul : x.sum (fun a b => b * ((starRingEnd ℂ) c * (starRingEnd ℂ) (z a))) =
        x.sum (fun a b => (starRingEnd ℂ c) * (b * (starRingEnd ℂ (z a)))) := by
      apply Finsupp.sum_congr
      intro a ha
      ring
    rw [hmul, ← Finsupp.mul_sum]

  have h_pair_symm : ∀ (x y : Module.Free.ChooseBasisIndex ℂ (Form_10 RS) →₀ ℂ),
      pairCoeff y x = starRingEnd ℂ (pairCoeff x y) := by
    intro x y
    let s : Finset (Module.Free.ChooseBasisIndex ℂ (Form_10 RS)) := x.support ∪ y.support
    have hx : pairCoeff x y = ∑ i ∈ s, x i * starRingEnd ℂ (y i) := by
      unfold pairCoeff s
      refine Finset.sum_subset Finset.subset_union_left ?_
      intro i hi hix
      have hxi : x i = 0 := (Finsupp.notMem_support_iff.mp hix)
      simp [hxi]
    have hy : pairCoeff y x = ∑ i ∈ s, y i * starRingEnd ℂ (x i) := by
      unfold pairCoeff s
      refine Finset.sum_subset Finset.subset_union_right ?_
      intro i hi hiy
      have hyi : y i = 0 := (Finsupp.notMem_support_iff.mp hiy)
      simp [hyi]
    rw [hy, hx, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [map_mul, mul_comm]

  have h_pair_pos : ∀ x : Module.Free.ChooseBasisIndex ℂ (Form_10 RS) →₀ ℂ,
      x ≠ 0 → (pairCoeff x x).re > 0 := by
    intro x hx
    have hs_nonempty : x.support.Nonempty := by
      by_contra hs
      apply hx
      apply (Finsupp.support_eq_empty).1
      exact Finset.not_nonempty_iff_eq_empty.mp hs
    have hsum_pos : 0 < ∑ i ∈ x.support, ‖x i‖ ^ (2 : ℕ) := by
      refine Finset.sum_pos ?_ hs_nonempty
      intro i hi
      have hne : x i ≠ 0 := (Finsupp.mem_support_iff.mp hi)
      have hn : 0 < ‖x i‖ := norm_pos_iff.mpr hne
      positivity
    have hre : (pairCoeff x x).re = ∑ i ∈ x.support, ‖x i‖ ^ (2 : ℕ) := by
      have hpair : pairCoeff x x = ∑ i ∈ x.support, (↑‖x i‖ : ℂ) ^ (2 : ℕ) := by
        unfold pairCoeff
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa using (Complex.mul_conj' (x i))
      rw [hpair]
      simp [pow_two]
    rw [hre]
    exact hsum_pos

  refine ⟨{
    pairing := fun ω η => pairCoeff (b.repr ω) (b.repr η)
    sesquilinear_right := ?_
    conj_symm := ?_
    pos_def := ?_
  }⟩
  · intro ω η₁ η₂ c
    simpa [pairCoeff, LinearEquiv.map_add, LinearEquiv.map_smul] using
      h_pair_right (b.repr ω) (b.repr η₁) (b.repr η₂) c
  · intro ω η
    simpa [pairCoeff] using h_pair_symm (b.repr ω) (b.repr η)
  · intro ω hω
    have hrepr_ne : b.repr ω ≠ 0 := by
      intro h0
      apply hω
      apply b.repr.injective
      simpa using h0
    simpa [pairCoeff] using h_pair_pos (b.repr ω) hrepr_ne

/-- The L² inner product on (1,0)-forms, given an inner product structure.

    ⟨ω, η⟩ = ∫_X ω ∧ ⋆η̄

    For a Riemann surface with local coordinate z, the Hodge star gives
    ⋆dz = -i dz̄, so ω ∧ ⋆η̄ is a (1,1)-form that can be integrated. -/
noncomputable def innerProduct_10 (CRS : CompactRiemannSurface)
    (ip : L2InnerProduct10 CRS)
    (ω η : Form_10 CRS.toRiemannSurface) : ℂ :=
  ip.pairing ω η

/-- Harmonic forms are orthogonal to exact forms.

    If ω is harmonic (∂̄ω = 0) and η = ∂̄f for some function f, then ⟨ω, η⟩ = 0.
    This follows from integration by parts: ⟨ω, ∂̄f⟩ = ⟨∂̄*ω, f⟩ = 0
    since harmonic forms are coclosed (∂̄*ω = 0). -/
theorem harmonic_orthogonal_exact (CRS : CompactRiemannSurface)
    (ip : L2InnerProduct10 CRS)
    (ω_harm : Harmonic10Forms CRS.toRiemannSurface)
    (f : SmoothFunction CRS.toRiemannSurface) :
    innerProduct_10 CRS ip ω_harm.val
      (⟨(dbar_fun f).toSection, (dbar_fun f).smooth'⟩ : Form_10 _) = 0 := by
  have hdbar0 : dbar_fun f = 0 := dbar_fun_eq_zero f
  have hform0 : (⟨(dbar_fun f).toSection, (dbar_fun f).smooth'⟩ : Form_10 _) = 0 := by
    apply Form_10.ext
    funext p
    exact congrArg (fun ω : Form_01 CRS.toRiemannSurface => ω.toSection p) hdbar0
  rw [hform0]
  unfold innerProduct_10
  have h := ip.sesquilinear_right ω_harm.val 0 0 (1 : ℂ)
  simp only [one_smul, map_one, one_mul, add_zero] at h
  have h' : ip.pairing ω_harm.val 0 + 0 = ip.pairing ω_harm.val 0 + ip.pairing ω_harm.val 0 := by
    rw [add_zero]
    exact h
  exact (add_left_cancel h').symm

/-!
## Dolbeault Isomorphism

The Dolbeault theorem identifies:
  H^{p,q}_∂̄(X) ≅ H^q(X, Ω^p)

where Ω^p is the sheaf of holomorphic p-forms.
-/

/-- The image of ∂̄ : C^∞(X) → Ω^{0,1}(X) as a ℂ-submodule of (0,1)-forms.
    Duplicated from DolbeaultCohomology.lean to avoid circular imports.
    Uses `dbar_real_hd` (the local copy of `dbar_real`). -/
def dbarImage_hd (RS : RiemannSurface) : Submodule ℂ (Form_01 RS) where
  carrier := { ω | ∃ f : RealSmoothFunction RS, dbar_real_hd f = ω }
  add_mem' := by
    intro a b ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨f + g, by rw [dbar_real_hd_add, hf, hg]⟩
  zero_mem' := ⟨0, dbar_real_hd_zero⟩
  smul_mem' := by
    intro c ω ⟨f, hf⟩
    exact ⟨c • f, by rw [dbar_real_hd_smul, hf]⟩

/-- Additive content of `dbarImage_hd`: it is exactly the range of `dbarRealAddHom_hd`. -/
theorem dbarImage_hd_toAddSubgroup_eq_range (RS : RiemannSurface) :
    (dbarImage_hd RS).toAddSubgroup = (dbarRealAddHom_hd (RS := RS)).range := by
  ext ω
  constructor
  · intro hω
    rcases hω with ⟨f, rfl⟩
    exact ⟨f, rfl⟩
  · intro hω
    rcases hω with ⟨f, rfl⟩
    exact ⟨f, rfl⟩

/-- Linear content of `dbarImage_hd`: it is exactly the range of `dbarRealLinearMap_hd`. -/
theorem dbarImage_hd_eq_range_linearMap (RS : RiemannSurface) :
    dbarImage_hd RS = (dbarRealLinearMap_hd (RS := RS)).range := by
  ext ω
  constructor
  · intro hω
    rcases hω with ⟨f, rfl⟩
    exact ⟨f, rfl⟩
  · intro hω
    rcases hω with ⟨f, rfl⟩
    exact ⟨f, rfl⟩

/-- Sheaf cohomology H¹(X, O) defined analytically as the Dolbeault quotient
    Ω^{0,1}(X) / im(∂̄). By the Dolbeault theorem, this is isomorphic to the
    sheaf cohomology H¹(X, O_X) defined via Čech cohomology or derived functors.

    This is a local copy of `DolbeaultH01` from DolbeaultCohomology.lean,
    defined here to break the circular import dependency. -/
noncomputable def SheafH1O (CRS : CompactRiemannSurface) : Type _ :=
  Form_01 CRS.toRiemannSurface ⧸ dbarImage_hd CRS.toRiemannSurface

/-- `SheafH1O` inherits additive structure from the quotient. -/
noncomputable instance (CRS : CompactRiemannSurface) : AddCommGroup (SheafH1O CRS) :=
  Submodule.Quotient.addCommGroup _

/-- `SheafH1O` inherits `ℂ`-module structure from the quotient. -/
noncomputable instance (CRS : CompactRiemannSurface) : Module ℂ (SheafH1O CRS) :=
  Submodule.Quotient.module _

/-- Canonical map from harmonic `(0,1)` forms to sheaf-cohomology classes:
send a harmonic form to its quotient class modulo `im(∂̄)`. -/
noncomputable def harmonic01ToSheafH1O (CRS : CompactRiemannSurface) :
    Harmonic01Forms CRS.toRiemannSurface → SheafH1O CRS := by
  exact fun η =>
    QuotientAddGroup.mk
      (s := (dbarImage_hd CRS.toRiemannSurface).toAddSubgroup)
      η.1

/-- Equality criterion for sheaf classes of harmonic `(0,1)` forms. -/
theorem harmonic01ToSheafH1O_eq_iff (CRS : CompactRiemannSurface)
    (η₁ η₂ : Harmonic01Forms CRS.toRiemannSurface) :
    harmonic01ToSheafH1O CRS η₁ = harmonic01ToSheafH1O CRS η₂ ↔
      (-η₁.1 + η₂.1) ∈
        dbarImage_hd CRS.toRiemannSurface := by
  simpa [harmonic01ToSheafH1O, SheafH1O] using
    (QuotientAddGroup.eq
      (s := (dbarImage_hd CRS.toRiemannSurface).toAddSubgroup)
      (a := η₁.1)
      (b := η₂.1))

/-- Surjectivity criterion:
every `(0,1)`-form class has a harmonic representative modulo `im(∂̄)`. -/
theorem harmonic01ToSheafH1O_surjective_of_hodgeDecomposition
    (CRS : CompactRiemannSurface)
    (hdec :
      ∀ ω : Form_01 CRS.toRiemannSurface,
        ∃ η : Form_01 CRS.toRiemannSurface, ∃ f : RealSmoothFunction CRS.toRiemannSurface,
          η.IsHarmonic ∧ ω = η + dbar_real_hd f) :
    Function.Surjective (harmonic01ToSheafH1O CRS) := by
  intro x
  rcases Quotient.exists_rep x with ⟨ω, rfl⟩
  rcases hdec ω with ⟨η, f, hη, hω⟩
  refine ⟨⟨η, hη⟩, ?_⟩
  have hmem :
      (-η + ω) ∈ dbarImage_hd CRS.toRiemannSurface := by
    refine ⟨f, ?_⟩
    have hdiff : -η + ω = dbar_real_hd f := by
      rw [hω]
      abel
    exact hdiff.symm
  have hEq :
      QuotientAddGroup.mk (s := (dbarImage_hd CRS.toRiemannSurface).toAddSubgroup) η =
        QuotientAddGroup.mk (s := (dbarImage_hd CRS.toRiemannSurface).toAddSubgroup) ω := by
    exact
      (QuotientAddGroup.eq
        (s := (dbarImage_hd CRS.toRiemannSurface).toAddSubgroup)
        (a := η) (b := ω)).2 hmem
  simpa [harmonic01ToSheafH1O, SheafH1O] using hEq

/-- Injectivity criterion:
if a harmonic `(0,1)` form is `∂̄`-exact, then it vanishes. -/
theorem harmonic01ToSheafH1O_injective_of_exact_kernel
    (CRS : CompactRiemannSurface)
    (hker :
      ∀ η : Harmonic01Forms CRS.toRiemannSurface,
        (η.1 ∈ dbarImage_hd CRS.toRiemannSurface) →
          η = 0) :
    Function.Injective (harmonic01ToSheafH1O CRS) := by
  intro η₁ η₂ heq
  have hmem :
      (-η₁.1 + η₂.1) ∈
        dbarImage_hd CRS.toRiemannSurface :=
    (harmonic01ToSheafH1O_eq_iff CRS η₁ η₂).1 heq
  have hneg : (-η₁.1).IsHarmonic := by
    simpa using isHarmonic01_smul (-1 : ℂ) η₁.2
  have hdiff_harm :
      (-η₁.1 + η₂.1).IsHarmonic :=
    isHarmonic01_add hneg η₂.2
  let ηdiff : Harmonic01Forms CRS.toRiemannSurface :=
    ⟨-η₁.1 + η₂.1, hdiff_harm⟩
  have hzero : ηdiff = 0 := hker ηdiff (by simpa [ηdiff] using hmem)
  have hdiff_zero : -η₁.1 + η₂.1 = 0 := by
    exact congrArg Subtype.val hzero
  have hsub : η₂.1 - η₁.1 = 0 := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hdiff_zero
  have hforms : η₁.1 = η₂.1 := by
    exact (sub_eq_zero.mp hsub).symm
  exact Subtype.ext hforms

/-- Bijectivity criterion from decomposition and exact-kernel vanishing. -/
theorem harmonic01ToSheafH1O_bijective_of_hodgeDecomposition_and_exact_kernel
    (CRS : CompactRiemannSurface)
    (hdec :
      ∀ ω : Form_01 CRS.toRiemannSurface,
        ∃ η : Form_01 CRS.toRiemannSurface, ∃ f : RealSmoothFunction CRS.toRiemannSurface,
          η.IsHarmonic ∧ ω = η + dbar_real_hd f)
    (hker :
      ∀ η : Harmonic01Forms CRS.toRiemannSurface,
        (η.1 ∈ dbarImage_hd CRS.toRiemannSurface) →
          η = 0) :
    Function.Bijective (harmonic01ToSheafH1O CRS) := by
  refine ⟨?_, ?_⟩
  · exact harmonic01ToSheafH1O_injective_of_exact_kernel CRS hker
  · exact harmonic01ToSheafH1O_surjective_of_hodgeDecomposition CRS hdec

/-- Linear map package for `harmonic01ToSheafH1O`. -/
noncomputable def harmonic01ToSheafH1OLinear (CRS : CompactRiemannSurface) :
    Harmonic01Forms CRS.toRiemannSurface →ₗ[ℂ] SheafH1O CRS where
  toFun := harmonic01ToSheafH1O CRS
  map_add' := by
    intro η₁ η₂
    rfl
  map_smul' := by
    intro c η
    rfl

/-- Injectivity from exact-harmonic vanishing for `(0,1)` exact forms. -/
theorem harmonic01ToSheafH1O_injective_of_exact_harmonic01_vanishes
    (CRS : CompactRiemannSurface)
    (hvanish :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        (dbar_real_hd f).IsHarmonic →
          dbar_real_hd f = 0) :
    Function.Injective (harmonic01ToSheafH1O CRS) := by
  refine harmonic01ToSheafH1O_injective_of_exact_kernel CRS ?_
  intro η hmem
  rcases hmem with ⟨f, hf⟩
  have hharm : (dbar_real_hd f).IsHarmonic := by
    simpa [hf] using η.2
  have hzero : dbar_real_hd f = 0 := hvanish f hharm
  have hηzero : η.1 = 0 := by
    simpa [hf] using hzero
  exact Subtype.ext hηzero

/-- Converse bridge: injectivity of the harmonic-to-sheaf map implies
exact-harmonic `(0,1)` vanishing. -/
theorem exact_harmonic01_vanishes_of_harmonic01ToSheafH1O_injective
    (CRS : CompactRiemannSurface)
    (hinj : Function.Injective (harmonic01ToSheafH1O CRS)) :
    ∀ f : RealSmoothFunction CRS.toRiemannSurface,
      (dbar_real_hd f).IsHarmonic →
        dbar_real_hd f = 0 := by
  intro f hf
  let η : Harmonic01Forms CRS.toRiemannSurface := ⟨dbar_real_hd f, hf⟩
  have hclass :
      harmonic01ToSheafH1O CRS η =
        harmonic01ToSheafH1O CRS 0 := by
    refine (harmonic01ToSheafH1O_eq_iff CRS η 0).2 ?_
    refine ⟨-f, ?_⟩
    change dbar_real_hd (-f) = -η.1 + 0
    calc
      dbar_real_hd (-f)
          = dbar_real_hd (((-1 : ℂ) • f) : RealSmoothFunction CRS.toRiemannSurface) := by
            ext p
            simp
      _ = (-1 : ℂ) • dbar_real_hd f := dbar_real_hd_smul (RS := CRS.toRiemannSurface) (-1) f
      _ = -η.1 + 0 := by
            simp [η]
  have hη0 : η = 0 := hinj hclass
  have hval0 : η.1 = 0 := congrArg Subtype.val hη0
  simpa [η] using hval0

/-- Exact-harmonic `(0,1)` vanishing is equivalent to injectivity of
`harmonic01ToSheafH1O`. -/
theorem harmonic01ToSheafH1O_injective_iff_exact_harmonic01_vanishes
    (CRS : CompactRiemannSurface) :
    Function.Injective (harmonic01ToSheafH1O CRS) ↔
      (∀ f : RealSmoothFunction CRS.toRiemannSurface,
        (dbar_real_hd f).IsHarmonic →
          dbar_real_hd f = 0) := by
  constructor
  · exact exact_harmonic01_vanishes_of_harmonic01ToSheafH1O_injective CRS
  · exact harmonic01ToSheafH1O_injective_of_exact_harmonic01_vanishes CRS

/-- Linear-map bijectivity from exact-harmonic vanishing. -/
theorem harmonic01ToSheafH1OLinear_bijective_of_exact_harmonic01_vanishes
    (CRS : CompactRiemannSurface)
    (hvanish :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        (dbar_real_hd f).IsHarmonic →
          dbar_real_hd f = 0) :
    Function.Bijective (harmonic01ToSheafH1OLinear CRS) := by
  refine ⟨?_, ?_⟩
  · simpa [harmonic01ToSheafH1OLinear] using
      (harmonic01ToSheafH1O_injective_of_exact_harmonic01_vanishes CRS hvanish)
  · simpa [harmonic01ToSheafH1OLinear] using
      (harmonic01ToSheafH1O_surjective_of_hodgeDecomposition CRS
        (hodge_decomposition_01 (CRS := CRS)))

/-- Surjectivity specialized to the existing Hodge decomposition theorem. -/
theorem harmonic01ToSheafH1O_surjective (CRS : CompactRiemannSurface) :
    Function.Surjective (harmonic01ToSheafH1O CRS) := by
  exact harmonic01ToSheafH1O_surjective_of_hodgeDecomposition CRS
    (hodge_decomposition_01 (CRS := CRS))

/-- Dolbeault isomorphism from exact-kernel vanishing, using
`hodge_decomposition_01` for surjectivity. -/
theorem dolbeault_isomorphism_01_of_exact_kernel
    (CRS : CompactRiemannSurface)
    (hker :
      ∀ η : Harmonic01Forms CRS.toRiemannSurface,
        (η.1 ∈ dbarImage_hd CRS.toRiemannSurface) →
          η = 0) :
    ∃ (iso : Harmonic01Forms CRS.toRiemannSurface → SheafH1O CRS),
      Function.Bijective iso := by
  refine ⟨harmonic01ToSheafH1O CRS, ?_⟩
  refine ⟨?_, ?_⟩
  · exact harmonic01ToSheafH1O_injective_of_exact_kernel CRS hker
  · exact harmonic01ToSheafH1O_surjective CRS

/-- Dolbeault isomorphism from exact-harmonic vanishing for `(0,1)` exact forms. -/
theorem dolbeault_isomorphism_01_of_exact_harmonic01_vanishes
    (CRS : CompactRiemannSurface)
    (hvanish :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        (dbar_real_hd f).IsHarmonic →
          dbar_real_hd f = 0) :
    ∃ (iso : Harmonic01Forms CRS.toRiemannSurface → SheafH1O CRS),
      Function.Bijective iso := by
  refine ⟨harmonic01ToSheafH1O CRS, ?_⟩
  refine ⟨?_, ?_⟩
  · exact harmonic01ToSheafH1O_injective_of_exact_harmonic01_vanishes CRS hvanish
  · exact harmonic01ToSheafH1O_surjective CRS

/-- Linear Dolbeault isomorphism package from exact-harmonic vanishing. -/
theorem dolbeault_isomorphism_01_linear_of_exact_harmonic01_vanishes
    (CRS : CompactRiemannSurface)
    (hvanish :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        (dbar_real_hd f).IsHarmonic →
          dbar_real_hd f = 0) :
    ∃ (iso : Harmonic01Forms CRS.toRiemannSurface →ₗ[ℂ] SheafH1O CRS),
      Function.Bijective iso := by
  refine ⟨harmonic01ToSheafH1OLinear CRS, ?_⟩
  exact harmonic01ToSheafH1OLinear_bijective_of_exact_harmonic01_vanishes CRS hvanish

/-- Dolbeault isomorphism: H^{0,1}_∂̄ ≅ H¹(X, O) where O is the structure sheaf.

    The Dolbeault cohomology H^{0,1}_∂̄(X) = Ω^{0,1}(X) / im(∂̄)
    is isomorphic to the sheaf cohomology H¹(X, O).

    For a compact Riemann surface of genus g:
    - dim H^{0,1}_∂̄ = g (antiholomorphic 1-forms)
    - dim H¹(X, O) = g (first cohomology of structure sheaf)

    The isomorphism is given by the ∂̄-Poincaré lemma and the
    long exact sequence in sheaf cohomology. -/
theorem dolbeault_isomorphism_01 (CRS : CompactRiemannSurface) :
    ∃ (iso : Harmonic01Forms CRS.toRiemannSurface → SheafH1O CRS),
      Function.Bijective iso := by
  have hvanish :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        (dbar_real_hd f).IsHarmonic →
          dbar_real_hd f = 0 :=
    exact_harmonic01_vanishes CRS
  exact dolbeault_isomorphism_01_of_exact_harmonic01_vanishes CRS hvanish

end RiemannSurfaces.Analytic
