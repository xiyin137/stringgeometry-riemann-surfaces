import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.HodgeDecomposition.ExactPair

/-!
# Hodge-De Rham Bridge

Bridge infrastructure from harmonic pieces to de Rham classes.
-/

namespace RiemannSurfaces.Analytic

/-- A harmonic `(1,0)`/`(0,1)` pair is closed as a 1-form. -/
theorem harmonicPair_mem_closedForms1 (RS : RiemannSurface)
    (ω10 : Form_10 RS) (ω01 : Form_01 RS)
    (h10 : ω10.IsHarmonic) (h01 : ω01.IsHarmonic) :
    ((ω10, ω01) : Form_10 RS × Form_01 RS) ∈ closedForms1 RS := by
  show dbar_10 ω10 + del_01 ω01 = 0
  rw [h10, del_01_eq_zero_of_isHarmonic01 h01, add_zero]

/-- Closed representative associated to a harmonic `(1,0)`/`(0,1)` pair. -/
def harmonicPairClosedRep (RS : RiemannSurface)
    (h : Harmonic10Forms RS × Harmonic01Forms RS) :
    ↥(closedForms1 RS) :=
  ⟨((h.1.1, h.2.1) : Form_10 RS × Form_01 RS),
    harmonicPair_mem_closedForms1 RS h.1.1 h.2.1 h.1.2 h.2.2⟩

/-- Canonical map from harmonic pieces to de Rham classes:
`H^{1,0} × H^{0,1} → H^1_dR`, sending a harmonic pair to its de Rham class. -/
noncomputable def harmonicPairToDeRham (CRS : CompactRiemannSurface) :
    (Harmonic10Forms CRS.toRiemannSurface × Harmonic01Forms CRS.toRiemannSurface) →
      DeRhamH1 CRS := by
  exact fun h => QuotientAddGroup.mk (harmonicPairClosedRep CRS.toRiemannSurface h)

/-- Equality criterion for de Rham images of harmonic pairs. -/
theorem harmonicPairToDeRham_eq_iff (CRS : CompactRiemannSurface)
    (h₁ h₂ : Harmonic10Forms CRS.toRiemannSurface × Harmonic01Forms CRS.toRiemannSurface) :
    harmonicPairToDeRham CRS h₁ = harmonicPairToDeRham CRS h₂ ↔
      -harmonicPairClosedRep CRS.toRiemannSurface h₁ +
        harmonicPairClosedRep CRS.toRiemannSurface h₂ ∈ exactClosedForms1AddSubgroup CRS := by
  simpa [harmonicPairToDeRham] using
    (deRham_mk_eq_mk_iff CRS
      (harmonicPairClosedRep CRS.toRiemannSurface h₁)
      (harmonicPairClosedRep CRS.toRiemannSurface h₂))

/-- Closed representative of the difference between two harmonic pairs. -/
noncomputable def harmonicPairDifference (CRS : CompactRiemannSurface)
    (h₁ h₂ : Harmonic10Forms CRS.toRiemannSurface × Harmonic01Forms CRS.toRiemannSurface) :
    ↥(closedForms1 CRS.toRiemannSurface) :=
  -harmonicPairClosedRep CRS.toRiemannSurface h₁ +
    harmonicPairClosedRep CRS.toRiemannSurface h₂

/-- Surjectivity criterion for the harmonic-to-de Rham map:
every closed class has a cohomologous harmonic-pair representative. -/
theorem harmonicPairToDeRham_surjective_of_cohomologous_harmonicPair
    (CRS : CompactRiemannSurface)
    (hcoh :
      ∀ ω : ↥(closedForms1 CRS.toRiemannSurface),
        ∃ h : Harmonic10Forms CRS.toRiemannSurface × Harmonic01Forms CRS.toRiemannSurface,
          -harmonicPairClosedRep CRS.toRiemannSurface h + ω ∈ exactClosedForms1AddSubgroup CRS) :
    Function.Surjective (harmonicPairToDeRham CRS) := by
  intro x
  rcases Quotient.exists_rep x with ⟨ω, rfl⟩
  rcases hcoh ω with ⟨h, hh⟩
  refine ⟨h, ?_⟩
  simpa [harmonicPairToDeRham] using
    (deRham_mk_eq_mk_iff CRS
      (harmonicPairClosedRep CRS.toRiemannSurface h) ω).2 hh

/-- Surjectivity from componentwise Hodge decomposition plus a common-potential bridge.

The bridge hypothesis packages the deep compatibility step:
if a closed pair has separately exact `(1,0)` and `(0,1)` components, then those
components come from one global potential `f` as `(∂f, ∂̄f)`. -/
theorem harmonicPairToDeRham_surjective_of_hodgeDecomposition_and_commonPotential
    (CRS : CompactRiemannSurface)
    (hdec10 :
      ∀ ω10 : Form_10 CRS.toRiemannSurface,
        ∃ η10 : Form_10 CRS.toRiemannSurface, ∃ f10 : RealSmoothFunction CRS.toRiemannSurface,
          η10.IsHarmonic ∧ ω10 = η10 + del_real f10)
    (hdec01 :
      ∀ ω01 : Form_01 CRS.toRiemannSurface,
        ∃ η01 : Form_01 CRS.toRiemannSurface, ∃ f01 : RealSmoothFunction CRS.toRiemannSurface,
          η01.IsHarmonic ∧ ω01 = η01 + dbar_real_hd f01)
    (hcommon :
      ∀ (ω10 : Form_10 CRS.toRiemannSurface) (ω01 : Form_01 CRS.toRiemannSurface)
        (f10 f01 : RealSmoothFunction CRS.toRiemannSurface),
        dbar_10 ω10 + del_01 ω01 = 0 →
        ω10 = del_real f10 →
        ω01 = dbar_real_hd f01 →
        ∃ f : RealSmoothFunction CRS.toRiemannSurface,
          ω10 = del_real f ∧ ω01 = dbar_real_hd f) :
    Function.Surjective (harmonicPairToDeRham CRS) := by
  refine harmonicPairToDeRham_surjective_of_cohomologous_harmonicPair CRS ?_
  intro ω
  let ω10 : Form_10 CRS.toRiemannSurface := (ω : Form_10 CRS.toRiemannSurface × Form_01 CRS.toRiemannSurface).1
  let ω01 : Form_01 CRS.toRiemannSurface := (ω : Form_10 CRS.toRiemannSurface × Form_01 CRS.toRiemannSurface).2
  rcases hdec10 ω10 with ⟨η10, f10, hη10, hω10⟩
  rcases hdec01 ω01 with ⟨η01, f01, hη01, hω01⟩
  let hpair : Harmonic10Forms CRS.toRiemannSurface × Harmonic01Forms CRS.toRiemannSurface :=
    (⟨η10, hη10⟩, ⟨η01, hη01⟩)
  have hω_mem :
      ((ω10, ω01) : Form_10 CRS.toRiemannSurface × Form_01 CRS.toRiemannSurface) ∈
        closedForms1 CRS.toRiemannSurface := by
    exact ω.2
  have hη_mem :
      ((η10, η01) : Form_10 CRS.toRiemannSurface × Form_01 CRS.toRiemannSurface) ∈
        closedForms1 CRS.toRiemannSurface :=
    harmonicPair_mem_closedForms1 CRS.toRiemannSurface η10 η01 hη10 hη01
  have hdiff_closed :
      dbar_10 (-η10 + ω10) + del_01 (-η01 + ω01) = 0 := by
    have hdiff_mem :
        ((-η10 + ω10, -η01 + ω01) :
          Form_10 CRS.toRiemannSurface × Form_01 CRS.toRiemannSurface) ∈
          closedForms1 CRS.toRiemannSurface := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (closedForms1 CRS.toRiemannSurface).add_mem
          ((closedForms1 CRS.toRiemannSurface).neg_mem hη_mem) hω_mem
    exact hdiff_mem
  have hcomp10 : -η10 + ω10 = del_real f10 := by
    rw [hω10]
    abel
  have hcomp01 : -η01 + ω01 = dbar_real_hd f01 := by
    rw [hω01]
    abel
  rcases hcommon (-η10 + ω10) (-η01 + ω01) f10 f01 hdiff_closed hcomp10 hcomp01 with
    ⟨f, hf10, hf01⟩
  refine ⟨hpair, ?_⟩
  refine (mem_exactClosedForms1AddSubgroup_iff_exists CRS
    (-harmonicPairClosedRep CRS.toRiemannSurface hpair + ω)).2 ?_
  refine ⟨f, ?_, ?_⟩
  · change -η10 + ω10 = del_real f
    simpa using hf10
  · change -η01 + ω01 = dbar_real_hd f
    simpa using hf01

/-- Surjectivity from componentwise Hodge decomposition plus two analytic bridge inputs:
`∂̄∂ + ∂∂̄ = 0` on smooth potentials and exact-harmonic `(0,1)` vanishing.

This factors the common-potential step through
`ExactPair.exactPair_commonPotential_of_closed_of_mixed_and_exact_harmonic01_vanishes`. -/
theorem harmonicPairToDeRham_surjective_of_hodgeDecomposition_and_mixed_and_exact_harmonic01_vanishes
    (CRS : CompactRiemannSurface)
    (hdec10 :
      ∀ ω10 : Form_10 CRS.toRiemannSurface,
        ∃ η10 : Form_10 CRS.toRiemannSurface, ∃ f10 : RealSmoothFunction CRS.toRiemannSurface,
          η10.IsHarmonic ∧ ω10 = η10 + del_real f10)
    (hdec01 :
      ∀ ω01 : Form_01 CRS.toRiemannSurface,
        ∃ η01 : Form_01 CRS.toRiemannSurface, ∃ f01 : RealSmoothFunction CRS.toRiemannSurface,
          η01.IsHarmonic ∧ ω01 = η01 + dbar_real_hd f01)
    (hmixed :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        dbar_10 (del_real f) + del_01 (dbar_real_hd f) = 0)
    (hvanish01 :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        (dbar_real_hd f).IsHarmonic →
          dbar_real_hd f = 0) :
    Function.Surjective (harmonicPairToDeRham CRS) := by
  refine harmonicPairToDeRham_surjective_of_hodgeDecomposition_and_commonPotential
    CRS hdec10 hdec01 ?_
  intro ω10 ω01 f10 f01 hclosed hω10 hω01
  exact exactPair_commonPotential_of_closed_of_mixed_and_exact_harmonic01_vanishes
    (RS := CRS.toRiemannSurface) hvanish01 hmixed ω10 ω01 f10 f01 hclosed hω10 hω01

/-- Common-potential bridge from mixed identity and exact-harmonic `(0,1)` vanishing. -/
theorem closed_exactPair_commonPotential_of_mixed_and_exact_harmonic01_vanishes
    (CRS : CompactRiemannSurface)
    (hmixed :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        dbar_10 (del_real f) + del_01 (dbar_real_hd f) = 0)
    (hvanish01 :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        (dbar_real_hd f).IsHarmonic →
          dbar_real_hd f = 0) :
    ∀ (ω10 : Form_10 CRS.toRiemannSurface) (ω01 : Form_01 CRS.toRiemannSurface)
      (f10 f01 : RealSmoothFunction CRS.toRiemannSurface),
      dbar_10 ω10 + del_01 ω01 = 0 →
      ω10 = del_real f10 →
      ω01 = dbar_real_hd f01 →
      ∃ f : RealSmoothFunction CRS.toRiemannSurface,
        ω10 = del_real f ∧ ω01 = dbar_real_hd f := by
  intro ω10 ω01 f10 f01 hclosed hω10 hω01
  exact exactPair_commonPotential_of_closed_of_mixed_and_exact_harmonic01_vanishes
    (RS := CRS.toRiemannSurface) hvanish01 hmixed ω10 ω01 f10 f01 hclosed hω10 hω01

/-- Injectivity criterion for the harmonic-to-de Rham map:
if two harmonic pairs differ by an exact closed form, they are equal. -/
theorem harmonicPairToDeRham_injective_of_exact_kernel
    (CRS : CompactRiemannSurface)
    (hker :
      ∀ h₁ h₂ : Harmonic10Forms CRS.toRiemannSurface × Harmonic01Forms CRS.toRiemannSurface,
        harmonicPairDifference CRS h₁ h₂ ∈ exactClosedForms1AddSubgroup CRS →
          h₁ = h₂) :
    Function.Injective (harmonicPairToDeRham CRS) := by
  intro h₁ h₂ heq
  exact hker h₁ h₂ (by
    simpa [harmonicPairDifference] using ((harmonicPairToDeRham_eq_iff CRS h₁ h₂).1 heq))

/-- Bijectivity criterion combining the cohomologous-representative and exact-kernel hypotheses. -/
theorem harmonicPairToDeRham_bijective_of_cohomologous_harmonicPair_of_exact_kernel
    (CRS : CompactRiemannSurface)
    (hcoh :
      ∀ ω : ↥(closedForms1 CRS.toRiemannSurface),
        ∃ h : Harmonic10Forms CRS.toRiemannSurface × Harmonic01Forms CRS.toRiemannSurface,
          -harmonicPairClosedRep CRS.toRiemannSurface h + ω ∈ exactClosedForms1AddSubgroup CRS)
    (hker :
      ∀ h₁ h₂ : Harmonic10Forms CRS.toRiemannSurface × Harmonic01Forms CRS.toRiemannSurface,
        harmonicPairDifference CRS h₁ h₂ ∈ exactClosedForms1AddSubgroup CRS →
          h₁ = h₂) :
    Function.Bijective (harmonicPairToDeRham CRS) := by
  refine ⟨?_, ?_⟩
  · exact harmonicPairToDeRham_injective_of_exact_kernel CRS hker
  · exact harmonicPairToDeRham_surjective_of_cohomologous_harmonicPair CRS hcoh

/-- Reformulation of the exact-kernel condition using explicit `(∂f, ∂̄f)` data. -/
theorem harmonicPairToDeRham_injective_of_exact_kernel_exists
    (CRS : CompactRiemannSurface)
    (hker :
      ∀ h₁ h₂ : Harmonic10Forms CRS.toRiemannSurface × Harmonic01Forms CRS.toRiemannSurface,
        (∃ f : RealSmoothFunction CRS.toRiemannSurface,
          (harmonicPairDifference CRS h₁ h₂).1.1 = del_real f ∧
          (harmonicPairDifference CRS h₁ h₂).1.2 = dbar_real_hd f) →
          h₁ = h₂) :
    Function.Injective (harmonicPairToDeRham CRS) := by
  refine harmonicPairToDeRham_injective_of_exact_kernel CRS ?_
  intro h₁ h₂ hmem
  apply hker h₁ h₂
  exact (mem_exactClosedForms1AddSubgroup_iff_exists CRS
    (harmonicPairDifference CRS h₁ h₂)).1 hmem

/-- Injectivity from vanishing of exact harmonic pairs:
if `(∂f, ∂̄f)` is harmonic, then it is zero. -/
theorem harmonicPairToDeRham_injective_of_exact_harmonicPair_vanishes
    (CRS : CompactRiemannSurface)
    (hvanish :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        (del_real f).IsHarmonic →
        (dbar_real_hd f).IsHarmonic →
          del_real f = 0 ∧ dbar_real_hd f = 0) :
    Function.Injective (harmonicPairToDeRham CRS) := by
  refine harmonicPairToDeRham_injective_of_exact_kernel_exists CRS ?_
  intro h₁ h₂ hmem
  rcases hmem with ⟨f, hf10, hf01⟩
  have hdiff10_harm : ((harmonicPairDifference CRS h₁ h₂).1.1).IsHarmonic := by
    change (-h₁.1.1 + h₂.1.1).IsHarmonic
    have hsub : (h₂.1.1 - h₁.1.1).IsHarmonic := isHarmonic_sub h₂.1.2 h₁.1.2
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsub
  have hdiff01_harm : ((harmonicPairDifference CRS h₁ h₂).1.2).IsHarmonic := by
    change (-h₁.2.1 + h₂.2.1).IsHarmonic
    have hneg : (-h₁.2.1).IsHarmonic := by
      simpa using isHarmonic01_smul (-1 : ℂ) h₁.2.2
    exact isHarmonic01_add hneg h₂.2.2
  have hdel_harm : (del_real f).IsHarmonic := by
    simpa [hf10] using hdiff10_harm
  have hdbar_harm : (dbar_real_hd f).IsHarmonic := by
    simpa [hf01] using hdiff01_harm
  obtain ⟨hdel_zero, hdbar_zero⟩ := hvanish f hdel_harm hdbar_harm
  have hdiff10_zero : ((harmonicPairDifference CRS h₁ h₂).1.1) = 0 := by
    simpa [hf10] using hdel_zero
  have hdiff01_zero : ((harmonicPairDifference CRS h₁ h₂).1.2) = 0 := by
    simpa [hf01] using hdbar_zero
  have h10eq : h₁.1.1 = h₂.1.1 := by
    have hsub : h₂.1.1 - h₁.1.1 = 0 := by
      simpa [harmonicPairDifference, harmonicPairClosedRep, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm] using hdiff10_zero
    exact (sub_eq_zero.mp hsub).symm
  have h01eq : h₁.2.1 = h₂.2.1 := by
    have hsub : h₂.2.1 - h₁.2.1 = 0 := by
      simpa [harmonicPairDifference, harmonicPairClosedRep, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm] using hdiff01_zero
    exact (sub_eq_zero.mp hsub).symm
  apply Prod.ext
  · apply Subtype.ext
    exact h10eq
  · apply Subtype.ext
    exact h01eq

/-- Exact-harmonic pair vanishing from exact-harmonic `(0,1)` vanishing. -/
theorem exact_harmonicPair_vanishes_of_exact_harmonic01_vanishes
    (CRS : CompactRiemannSurface)
    (hvanish01 :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        (dbar_real_hd f).IsHarmonic →
          dbar_real_hd f = 0) :
    ∀ f : RealSmoothFunction CRS.toRiemannSurface,
      (del_real f).IsHarmonic →
      (dbar_real_hd f).IsHarmonic →
        del_real f = 0 ∧ dbar_real_hd f = 0 := by
  intro f hdel hdbar
  have hdbar0 : dbar_real_hd f = 0 := hvanish01 f hdbar
  have hconj_harm : (dbar_real_hd f.conj).IsHarmonic := by
    refine ⟨del_real f, hdel, ?_⟩
    show dbar_real_hd f.conj = (del_real f).conj
    unfold del_real
    exact (Form_01.conj_conj (dbar_real_hd f.conj)).symm
  have hconj0 : dbar_real_hd f.conj = 0 := hvanish01 f.conj hconj_harm
  have hdel0 : del_real f = 0 := by
    unfold del_real
    simp [hconj0]
  exact ⟨hdel0, hdbar0⟩

/-- Injectivity from exact-harmonic `(0,1)` vanishing. -/
theorem harmonicPairToDeRham_injective_of_exact_harmonic01_vanishes
    (CRS : CompactRiemannSurface)
    (hvanish01 :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        (dbar_real_hd f).IsHarmonic →
          dbar_real_hd f = 0) :
    Function.Injective (harmonicPairToDeRham CRS) := by
  refine harmonicPairToDeRham_injective_of_exact_harmonicPair_vanishes CRS ?_
  exact exact_harmonicPair_vanishes_of_exact_harmonic01_vanishes CRS hvanish01

/-- Combined bijectivity criterion from decomposition + compatibility + vanishing.

This is the direct reusable package for proving Hodge-de Rham bijectivity of
`harmonicPairToDeRham` once the two deep analytic bridges are available. -/
theorem harmonicPairToDeRham_bijective_of_hodgeDecomposition_and_commonPotential_and_exact_harmonicPair_vanishes
    (CRS : CompactRiemannSurface)
    (hcommon :
      ∀ (ω10 : Form_10 CRS.toRiemannSurface) (ω01 : Form_01 CRS.toRiemannSurface)
        (f10 f01 : RealSmoothFunction CRS.toRiemannSurface),
        dbar_10 ω10 + del_01 ω01 = 0 →
        ω10 = del_real f10 →
        ω01 = dbar_real_hd f01 →
        ∃ f : RealSmoothFunction CRS.toRiemannSurface,
          ω10 = del_real f ∧ ω01 = dbar_real_hd f)
    (hvanish :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        (del_real f).IsHarmonic →
        (dbar_real_hd f).IsHarmonic →
          del_real f = 0 ∧ dbar_real_hd f = 0) :
    Function.Bijective (harmonicPairToDeRham CRS) := by
  refine ⟨?_, ?_⟩
  · exact harmonicPairToDeRham_injective_of_exact_harmonicPair_vanishes CRS hvanish
  · exact harmonicPairToDeRham_surjective_of_hodgeDecomposition_and_commonPotential CRS
      (hodge_decomposition_10 (CRS := CRS))
      (hodge_decomposition_01 (CRS := CRS))
      hcommon

/-- Combined bijectivity criterion with exact-harmonic `(0,1)` vanishing. -/
theorem harmonicPairToDeRham_bijective_of_hodgeDecomposition_and_commonPotential_and_exact_harmonic01_vanishes
    (CRS : CompactRiemannSurface)
    (hcommon :
      ∀ (ω10 : Form_10 CRS.toRiemannSurface) (ω01 : Form_01 CRS.toRiemannSurface)
        (f10 f01 : RealSmoothFunction CRS.toRiemannSurface),
        dbar_10 ω10 + del_01 ω01 = 0 →
        ω10 = del_real f10 →
        ω01 = dbar_real_hd f01 →
        ∃ f : RealSmoothFunction CRS.toRiemannSurface,
          ω10 = del_real f ∧ ω01 = dbar_real_hd f)
    (hvanish01 :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        (dbar_real_hd f).IsHarmonic →
          dbar_real_hd f = 0) :
    Function.Bijective (harmonicPairToDeRham CRS) := by
  refine ⟨?_, ?_⟩
  · exact harmonicPairToDeRham_injective_of_exact_harmonic01_vanishes CRS hvanish01
  · exact harmonicPairToDeRham_surjective_of_hodgeDecomposition_and_commonPotential CRS
      (hodge_decomposition_10 (CRS := CRS))
      (hodge_decomposition_01 (CRS := CRS))
      hcommon

/-- Combined bijectivity criterion from decomposition + mixed identity +
exact-harmonic `(0,1)` vanishing. -/
theorem harmonicPairToDeRham_bijective_of_hodgeDecomposition_and_mixed_and_exact_harmonic01_vanishes
    (CRS : CompactRiemannSurface)
    (hmixed :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        dbar_10 (del_real f) + del_01 (dbar_real_hd f) = 0)
    (hvanish01 :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        (dbar_real_hd f).IsHarmonic →
          dbar_real_hd f = 0) :
    Function.Bijective (harmonicPairToDeRham CRS) := by
  refine ⟨?_, ?_⟩
  · exact harmonicPairToDeRham_injective_of_exact_harmonic01_vanishes CRS hvanish01
  · exact harmonicPairToDeRham_surjective_of_hodgeDecomposition_and_mixed_and_exact_harmonic01_vanishes
      CRS
      (hodge_decomposition_10 (CRS := CRS))
      (hodge_decomposition_01 (CRS := CRS))
      hmixed hvanish01

/-- Existential packaging of the combined criterion at the level of
`hodge_isomorphism` statement shape. -/
theorem hodge_isomorphism_of_commonPotential_and_exact_harmonicPair_vanishes
    (CRS : CompactRiemannSurface)
    (hcommon :
      ∀ (ω10 : Form_10 CRS.toRiemannSurface) (ω01 : Form_01 CRS.toRiemannSurface)
        (f10 f01 : RealSmoothFunction CRS.toRiemannSurface),
        dbar_10 ω10 + del_01 ω01 = 0 →
        ω10 = del_real f10 →
        ω01 = dbar_real_hd f01 →
        ∃ f : RealSmoothFunction CRS.toRiemannSurface,
          ω10 = del_real f ∧ ω01 = dbar_real_hd f)
    (hvanish :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        (del_real f).IsHarmonic →
        (dbar_real_hd f).IsHarmonic →
          del_real f = 0 ∧ dbar_real_hd f = 0) :
    ∃ (harmonic_to_deRham :
        (Harmonic10Forms CRS.toRiemannSurface × Harmonic01Forms CRS.toRiemannSurface) →
        DeRhamH1 CRS),
      Function.Bijective harmonic_to_deRham := by
  refine ⟨harmonicPairToDeRham CRS, ?_⟩
  exact
    harmonicPairToDeRham_bijective_of_hodgeDecomposition_and_commonPotential_and_exact_harmonicPair_vanishes
      CRS hcommon hvanish

/-- Existential packaging with exact-harmonic `(0,1)` vanishing. -/
theorem hodge_isomorphism_of_commonPotential_and_exact_harmonic01_vanishes
    (CRS : CompactRiemannSurface)
    (hcommon :
      ∀ (ω10 : Form_10 CRS.toRiemannSurface) (ω01 : Form_01 CRS.toRiemannSurface)
        (f10 f01 : RealSmoothFunction CRS.toRiemannSurface),
        dbar_10 ω10 + del_01 ω01 = 0 →
        ω10 = del_real f10 →
        ω01 = dbar_real_hd f01 →
        ∃ f : RealSmoothFunction CRS.toRiemannSurface,
          ω10 = del_real f ∧ ω01 = dbar_real_hd f)
    (hvanish01 :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        (dbar_real_hd f).IsHarmonic →
          dbar_real_hd f = 0) :
    ∃ (harmonic_to_deRham :
        (Harmonic10Forms CRS.toRiemannSurface × Harmonic01Forms CRS.toRiemannSurface) →
        DeRhamH1 CRS),
      Function.Bijective harmonic_to_deRham := by
  refine ⟨harmonicPairToDeRham CRS, ?_⟩
  exact
    harmonicPairToDeRham_bijective_of_hodgeDecomposition_and_commonPotential_and_exact_harmonic01_vanishes
      CRS hcommon hvanish01

/-- Existential packaging with mixed identity + exact-harmonic `(0,1)` vanishing. -/
theorem hodge_isomorphism_of_mixed_and_exact_harmonic01_vanishes
    (CRS : CompactRiemannSurface)
    (hmixed :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        dbar_10 (del_real f) + del_01 (dbar_real_hd f) = 0)
    (hvanish01 :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        (dbar_real_hd f).IsHarmonic →
          dbar_real_hd f = 0) :
    ∃ (harmonic_to_deRham :
        (Harmonic10Forms CRS.toRiemannSurface × Harmonic01Forms CRS.toRiemannSurface) →
        DeRhamH1 CRS),
      Function.Bijective harmonic_to_deRham := by
  refine ⟨harmonicPairToDeRham CRS, ?_⟩
  exact
    harmonicPairToDeRham_bijective_of_hodgeDecomposition_and_mixed_and_exact_harmonic01_vanishes
      CRS hmixed hvanish01

/-- Surjectivity from decomposition + chart-local selector stabilization +
exact-harmonic `(0,1)` vanishing. -/
theorem harmonicPairToDeRham_surjective_of_hodgeDecomposition_and_chartAtLocallyConstant_and_exact_harmonic01_vanishes
    (CRS : CompactRiemannSurface)
    (hchart : Infrastructure.ChartAtLocallyConstant CRS.toRiemannSurface)
    (hvanish01 :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        (dbar_real_hd f).IsHarmonic →
          dbar_real_hd f = 0) :
    Function.Surjective (harmonicPairToDeRham CRS) := by
  refine harmonicPairToDeRham_surjective_of_hodgeDecomposition_and_commonPotential CRS
    (hodge_decomposition_10 (CRS := CRS))
    (hodge_decomposition_01 (CRS := CRS))
    ?_
  intro ω10 ω01 f10 f01 hclosed hω10 hω01
  exact
    exactPair_commonPotential_of_closed_of_chartAtLocallyConstant_and_exact_harmonic01_vanishes
      (RS := CRS.toRiemannSurface) hchart hvanish01 ω10 ω01 f10 f01 hclosed hω10 hω01

/-- Bijectivity from decomposition + chart-local selector stabilization +
exact-harmonic `(0,1)` vanishing. -/
theorem harmonicPairToDeRham_bijective_of_hodgeDecomposition_and_chartAtLocallyConstant_and_exact_harmonic01_vanishes
    (CRS : CompactRiemannSurface)
    (hchart : Infrastructure.ChartAtLocallyConstant CRS.toRiemannSurface)
    (hvanish01 :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        (dbar_real_hd f).IsHarmonic →
          dbar_real_hd f = 0) :
    Function.Bijective (harmonicPairToDeRham CRS) := by
  refine ⟨?_, ?_⟩
  · exact harmonicPairToDeRham_injective_of_exact_harmonic01_vanishes CRS hvanish01
  · exact
      harmonicPairToDeRham_surjective_of_hodgeDecomposition_and_chartAtLocallyConstant_and_exact_harmonic01_vanishes
        CRS hchart hvanish01

/-- Existential packaging from chart-local selector stabilization +
exact-harmonic `(0,1)` vanishing. -/
theorem hodge_isomorphism_of_chartAtLocallyConstant_and_exact_harmonic01_vanishes
    (CRS : CompactRiemannSurface)
    (hchart : Infrastructure.ChartAtLocallyConstant CRS.toRiemannSurface)
    (hvanish01 :
      ∀ f : RealSmoothFunction CRS.toRiemannSurface,
        (dbar_real_hd f).IsHarmonic →
          dbar_real_hd f = 0) :
    ∃ (harmonic_to_deRham :
        (Harmonic10Forms CRS.toRiemannSurface × Harmonic01Forms CRS.toRiemannSurface) →
        DeRhamH1 CRS),
      Function.Bijective harmonic_to_deRham := by
  refine ⟨harmonicPairToDeRham CRS, ?_⟩
  exact
    harmonicPairToDeRham_bijective_of_hodgeDecomposition_and_chartAtLocallyConstant_and_exact_harmonic01_vanishes
      CRS hchart hvanish01

/-- Hodge theorem: Harmonic forms represent de Rham cohomology.
    H^1_dR(X) ≅ H^1_harm(X) for compact X. -/
theorem hodge_isomorphism (CRS : CompactRiemannSurface) :
    ∃ (harmonic_to_deRham :
        (Harmonic10Forms CRS.toRiemannSurface × Harmonic01Forms CRS.toRiemannSurface) →
        DeRhamH1 CRS),
      Function.Bijective harmonic_to_deRham := by
  exact
    hodge_isomorphism_of_commonPotential_and_exact_harmonic01_vanishes CRS
      (closed_exactPair_commonPotential CRS)
      (exact_harmonic01_vanishes CRS)

/-- Equivalence package extracted from `hodge_isomorphism`. -/
noncomputable def hodgeIsomorphismEquiv (CRS : CompactRiemannSurface) :
    (Harmonic10Forms CRS.toRiemannSurface × Harmonic01Forms CRS.toRiemannSurface) ≃
      DeRhamH1 CRS := by
  classical
  exact Equiv.ofBijective
    (Classical.choose (hodge_isomorphism CRS))
    (Classical.choose_spec (hodge_isomorphism CRS))

end RiemannSurfaces.Analytic
