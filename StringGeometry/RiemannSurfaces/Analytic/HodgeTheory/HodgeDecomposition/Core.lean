import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.Dolbeault
import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.Infrastructure.ChartSelection
import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.Infrastructure.TransitionFactor
import StringGeometry.RiemannSurfaces.Analytic.Helpers.ChartTransition

/-!
# Hodge Decomposition on Riemann Surfaces

Core analytic Hodge infrastructure used in the Riemann-Roch chain:
- `hodgeStar_*`, Laplacian and harmonic-form interfaces,
- `(1,0)` / `(0,1)` harmonic subtype + submodule packaging,
- `dbar_real_hd` / `del_real` infrastructure,
- de Rham-side helpers used by later Hodge/Dolbeault bridges.

The file focuses on reusable formal interfaces and intermediate bridges; deep
global statements remain theorem-level obligations where indicated.
-/

namespace RiemannSurfaces.Analytic

open Complex Topology
open scoped Manifold

variable {RS : RiemannSurface}

/-!
## The Hodge Star Operator

On a Riemann surface with the standard Kähler metric, the Hodge star satisfies:
  ⋆: Ω^{p,q} → Ω^{1-p,1-q}
-/

/-- The Hodge star on (1,0)-forms: ⋆(f dz) = -i f dz̄ (with standard normalization).
    This reflects the conformal structure of the Riemann surface. -/
noncomputable def hodgeStar_10 (ω : Form_10 RS) : Form_01 RS :=
  (-Complex.I) • (ω.conj)

/-- The Hodge star on (0,1)-forms: ⋆(g dz̄) = i g dz -/
noncomputable def hodgeStar_01 (ω : Form_01 RS) : Form_10 RS :=
  Complex.I • (ω.conj)

/-- ⋆⋆ = (-1)^{p(n-p)} on p-forms. For 1-forms on a 2-real-dimensional surface: ⋆⋆ = -1 -/
theorem hodgeStar_10_hodgeStar_01 (ω : Form_10 RS) :
    hodgeStar_01 (hodgeStar_10 ω) = -ω := by
  simp only [hodgeStar_10, hodgeStar_01]
  -- ⋆⋆ω = i • ((-i • ω.conj).conj) = i • (-i.conj • ω.conj.conj) = i • (i • ω) = -ω
  rw [Form_01.conj_smul, Form_10.conj_conj]
  -- Now have: I • (starRingEnd ℂ (-I) • ω)
  -- starRingEnd ℂ (-I) = I (conjugate of -I is I)
  simp only [map_neg, Complex.conj_I]
  -- Now have: I • (-(-I) • ω) = I • (I • ω)
  rw [neg_neg]
  -- Combine nested smul: I • (I • ω) = (I * I) • ω
  rw [smul_smul]
  -- I * I = -1
  simp only [Complex.I_mul_I, neg_smul, one_smul]

theorem hodgeStar_01_hodgeStar_10 (ω : Form_01 RS) :
    hodgeStar_10 (hodgeStar_01 ω) = -ω := by
  simp only [hodgeStar_10, hodgeStar_01]
  -- ⋆⋆ω = (-i) • ((i • ω.conj).conj) = (-i) • (i.conj • ω.conj.conj) = (-i) • ((-i) • ω) = -ω
  rw [Form_10.conj_smul, Form_01.conj_conj]
  -- Now have: (-I) • (starRingEnd ℂ I • ω)
  -- starRingEnd ℂ I = -I (conjugate of I is -I)
  simp only [Complex.conj_I]
  -- Now have: (-I) • ((-I) • ω)
  -- Combine nested smul: (-I) • ((-I) • ω) = ((-I) * (-I)) • ω
  rw [smul_smul]
  -- (-I) * (-I) = I² = -1
  simp only [neg_mul_neg, Complex.I_mul_I, neg_smul, one_smul]

/-- For MDifferentiable functions on a Riemann surface with 𝓘(ℂ, ℂ) model,
    the chart expression is ℂ-differentiable at every point in the chart target.

    This is the key infrastructure lemma: MDifferentiable f means f ∘ (chartAt q)⁻¹ is
    ℂ-differentiable at chartAt q for every q. We want to show that for a fixed chart e,
    f ∘ e.symm is ℂ-differentiable at every point z ∈ e.target.

    The proof uses:
    1. For z ∈ e.target, let q = e.symm z, so q ∈ e.source
    2. f is MDifferentiableAt at q
    3. Let e' = chartAt ℂ q (could differ from e)
    4. Then f ∘ e'.symm is DifferentiableAt at e' q
    5. On the overlap, e' ∘ e.symm is holomorphic (chart compatibility)
    6. f ∘ e.symm = (f ∘ e'.symm) ∘ (e' ∘ e.symm) locally
    7. Composition of holomorphic functions is holomorphic -/
theorem mdifferentiable_chart_diffAt {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ, ℂ) ⊤ M] {f : M → ℂ} (hmDiff : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f)
    (e : OpenPartialHomeomorph M ℂ) (he : e ∈ atlas ℂ M) (z : ℂ) (hz : z ∈ e.target) :
    DifferentiableAt ℂ (f ∘ e.symm) z := by
  -- q = e.symm z is in e.source
  let q := e.symm z
  have hq_source : q ∈ e.source := e.map_target hz

  -- f is MDifferentiableAt at q
  have hmdiff_q : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f q := hmDiff q

  -- The canonical chart at q
  let e' := chartAt ℂ q
  have hq_e'_source : q ∈ e'.source := mem_chart_source ℂ q

  -- Target chart simplifies (target is ℂ)
  have htarget : extChartAt 𝓘(ℂ, ℂ) (f q) = PartialEquiv.refl ℂ := by
    simpa using (extChartAt_model_space_eq_id (𝕜 := ℂ) (E := ℂ) (x := f q))
  have hrange : Set.range (𝓘(ℂ, ℂ) : ℂ → ℂ) = Set.univ := by simp

  -- Use mdifferentiableAt_iff_of_mem_source
  have hfq_source : f q ∈ (chartAt ℂ (f q)).source := mem_chart_source ℂ (f q)
  rw [mdifferentiableAt_iff_of_mem_source hq_e'_source hfq_source] at hmdiff_q

  -- Extract: f ∘ e'.symm is DifferentiableWithinAt at e' q
  simp only [hrange, htarget, PartialEquiv.refl_coe] at hmdiff_q
  have hdiff_e' : DifferentiableAt ℂ (f ∘ e'.symm) (e' q) := by
    have hfun_eq : id ∘ f ∘ (extChartAt 𝓘(ℂ, ℂ) q).symm = f ∘ e'.symm := by
      ext w
      simp only [Function.comp_apply, id_eq, extChartAt, OpenPartialHomeomorph.extend_coe_symm,
        modelWithCornersSelf_coe_symm, e']
    rw [hfun_eq] at hmdiff_q
    exact hmdiff_q.2.differentiableAt Filter.univ_mem

  -- Now we need to relate f ∘ e.symm to f ∘ e'.symm
  -- On the overlap: f ∘ e.symm = (f ∘ e'.symm) ∘ (e' ∘ e.symm)

  -- e' ∘ e.symm is the transition map, which is holomorphic on its domain
  -- Since both e and e' are in the atlas, e' ∘ e.symm is smooth (actually holomorphic for Riemann surfaces)

  -- The point z satisfies: e.symm z = q ∈ e'.source (since q ∈ e.source and e' = chartAt q)
  have hq_e'_source' : e.symm z ∈ e'.source := hq_e'_source

  -- On a neighborhood of z, e' ∘ e.symm is well-defined and holomorphic
  -- and f ∘ e.symm = (f ∘ e'.symm) ∘ (e' ∘ e.symm)

  -- Chart transition is differentiable (holomorphic for Riemann surfaces)
  have htrans_diff : DifferentiableAt ℂ (e' ∘ e.symm) z := by
    -- e.symm is continuous, e' is a chart, on the overlap the transition is smooth
    -- For 𝓘(ℂ, ℂ) (holomorphic atlas), transitions are holomorphic
    have he' : e' ∈ atlas ℂ M := chart_mem_atlas ℂ q
    -- The transition e' ∘ e.symm is smooth on e.target ∩ e'.symm.source (the overlap in ℂ)
    -- For a Riemann surface atlas, this is actually holomorphic
    -- Use StructureGroupoid.compatible to get membership in contDiffGroupoid
    have hmem : e.symm ≫ₕ e' ∈ contDiffGroupoid ⊤ 𝓘(ℂ, ℂ) :=
      StructureGroupoid.compatible (contDiffGroupoid ⊤ 𝓘(ℂ, ℂ)) he he'
    -- Extract ContDiffOn from membership in contDiffGroupoid
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hmem
    -- hmem.1 : contDiffPregroupoid property for e.symm ≫ₕ e'
    -- For 𝓘(ℂ, ℂ), this simplifies to ContDiffOn ℂ ⊤ (e.symm ≫ₕ e') (e.symm ≫ₕ e').source
    have hcd_source : ContDiffOn ℂ ⊤ (𝓘(ℂ, ℂ) ∘ (e.symm ≫ₕ e') ∘ 𝓘(ℂ, ℂ).symm)
        (𝓘(ℂ, ℂ).symm ⁻¹' (e.symm ≫ₕ e').source ∩ Set.range 𝓘(ℂ, ℂ)) := hmem.1
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
        Set.range_id, Set.inter_univ] at hcd_source
    -- hcd_source : ContDiffOn ℂ ⊤ (e.symm ≫ₕ e') (e.symm ≫ₕ e').source
    -- The source is e.symm.source ∩ e.symm ⁻¹' e'.source = e.target ∩ e.symm ⁻¹' e'.source
    have hsymm_source : e.symm.source = e.target := rfl
    have hdom : z ∈ e.target ∩ e.symm ⁻¹' e'.source := by
      constructor
      · exact hz
      · simp only [Set.mem_preimage]
        exact hq_e'_source'
    -- The domain of e.symm ≫ₕ e' is exactly e.target ∩ e.symm ⁻¹' e'.source
    have hsource_eq : (e.symm ≫ₕ e').source = e.target ∩ e.symm ⁻¹' e'.source := by
      simp only [OpenPartialHomeomorph.trans_source, hsymm_source]
    -- ContDiffOn ⊤ implies DifferentiableOn, which gives DifferentiableWithinAt
    have hcd : ContDiffWithinAt ℂ ⊤ (e.symm ≫ₕ e') (e.target ∩ e.symm ⁻¹' e'.source) z := by
      rw [← hsource_eq]
      exact hcd_source z (by rw [hsource_eq]; exact hdom)
    -- Convert to DifferentiableAt using that the domain is open
    have hopen : IsOpen (e.target ∩ e.symm ⁻¹' e'.source) := by
      rw [← hsource_eq]
      exact (e.symm ≫ₕ e').open_source
    have hdw : DifferentiableWithinAt ℂ (e.symm ≫ₕ e') (e.target ∩ e.symm ⁻¹' e'.source) z :=
      hcd.differentiableWithinAt (WithTop.top_ne_zero)
    -- Convert DifferentiableWithinAt to DifferentiableAt using that z is in the interior
    have hda := DifferentiableWithinAt.differentiableAt hdw (IsOpen.mem_nhds hopen hdom)
    -- Finally, (e.symm ≫ₕ e') = e' ∘ e.symm on the domain
    have hcomp : e' ∘ e.symm =ᶠ[nhds z] (e.symm ≫ₕ e') := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      use e.target ∩ e.symm ⁻¹' e'.source, IsOpen.mem_nhds hopen hdom
      intro w _
      rfl
    exact hda.congr_of_eventuallyEq hcomp.symm

  -- Now compose: f ∘ e.symm = (f ∘ e'.symm) ∘ (e' ∘ e.symm)
  have hcomp_eq : f ∘ e.symm =ᶠ[nhds z] (f ∘ e'.symm) ∘ (e' ∘ e.symm) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    -- On e.target ∩ e.symm⁻¹(e'.source), we have e'.symm (e' (e.symm w)) = e.symm w
    have hsymm_source' : e.symm.source = e.target := rfl
    have hsource_eq : (e.symm ≫ₕ e').source = e.target ∩ e.symm ⁻¹' e'.source := by
      simp only [OpenPartialHomeomorph.trans_source, hsymm_source']
    have hopen : IsOpen (e.target ∩ e.symm ⁻¹' e'.source) := by
      rw [← hsource_eq]
      exact (e.symm ≫ₕ e').open_source
    use e.target ∩ e.symm ⁻¹' e'.source
    constructor
    · apply IsOpen.mem_nhds hopen
      exact ⟨hz, hq_e'_source'⟩
    · intro w ⟨_, hw_preimage⟩
      simp only [Function.comp_apply]
      -- e'.symm (e' (e.symm w)) = e.symm w when e.symm w ∈ e'.source
      have hw_e'_source : e.symm w ∈ e'.source := hw_preimage
      rw [e'.left_inv hw_e'_source]

  -- Composition of differentiable functions is differentiable
  -- First show the composed function is differentiable
  have hcomp_diff : DifferentiableAt ℂ (fun w => f (e'.symm (e' (e.symm w)))) z := by
    have h1 : DifferentiableAt ℂ (e' ∘ e.symm) z := htrans_diff
    have h2 : DifferentiableAt ℂ (f ∘ e'.symm) ((e' ∘ e.symm) z) := by
      have heq : (e' ∘ e.symm) z = e' q := rfl
      rw [heq]
      exact hdiff_e'
    exact h2.comp z h1

  -- Now use that on the overlap, e'.symm (e' (e.symm w)) = e.symm w
  exact hcomp_diff.congr_of_eventuallyEq hcomp_eq

/-!
## The Laplacian

On a Riemann surface, the Laplacian decomposes as Δ = Δ_∂ + Δ_∂̄ where
  Δ_∂̄ = ∂̄⋆∂̄ + ∂̄∂̄⋆

For functions, this simplifies considerably because ∂̄² = 0.
-/

/-- The ∂̄-Laplacian on functions: Δ_∂̄ f = ⋆∂̄⋆∂̄f.
    On a Riemann surface, this equals 2∂∂̄. -/
noncomputable def laplacian_dbar_fun (f : SmoothFunction RS) : SmoothFunction RS := by
  letI := RS.topology
  letI := RS.chartedSpace
  -- Δ_∂̄ f = ⋆∂̄(⋆∂̄f) - but ∂̄f is a (0,1)-form, ⋆∂̄f is a (1,0)-form
  -- ∂̄(⋆∂̄f) would be a (1,1)-form, and ⋆ of that is a function
  -- For simplicity, we define via the coordinate expression
  refine ⟨fun p => ?_, ?_⟩
  · let e := @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p
    -- Δf = 4 ∂²f/∂z∂z̄ in local coordinates
    exact 4 * wirtingerDeriv_z (wirtingerDeriv_zbar (f.toFun ∘ e.symm)) (e p)
  · -- SmoothFunction is ℂ-smooth (holomorphic), so wirtingerDerivBar vanishes on chart targets.
    -- wirtingerDeriv of a locally-zero function is zero. Hence the section ≡ 0.
    haveI : IsManifold 𝓘(ℂ, ℂ) ⊤ RS.carrier := RS.isManifold
    have hmDiff : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f.toFun :=
      f.smooth'.mdifferentiable (by decide : (⊤ : WithTop ℕ∞) ≠ 0)
    convert contMDiff_const (c := (0 : ℂ)) using 1
    funext p
    simp only [wirtingerDeriv_z]
    -- Show wirtingerDerivBar (f ∘ e.symm) is zero on the open chart target
    let e := @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p
    have he_atlas : e ∈ atlas ℂ RS.carrier := chart_mem_atlas ℂ p
    have hp_source : p ∈ e.source := mem_chart_source ℂ p
    have hep_target : e p ∈ e.target := e.map_source hp_source
    -- wirtingerDerivBar (f ∘ e.symm) is zero on e.target (open set)
    have hbar_zero : ∀ z ∈ e.target,
        Infrastructure.wirtingerDerivBar (f.toFun ∘ e.symm) z = 0 := by
      intro z hz
      have hdiff := mdifferentiable_chart_diffAt hmDiff e he_atlas z hz
      exact (Infrastructure.holomorphic_iff_wirtingerDerivBar_zero.mp hdiff).2
    -- wirtingerDerivBar (f ∘ e.symm) =ᶠ[nhds (e p)] 0
    have hbar_eq : Infrastructure.wirtingerDerivBar (f.toFun ∘ e.symm) =ᶠ[nhds (e p)]
        fun _ => 0 := by
      apply Filter.eventuallyEq_iff_exists_mem.mpr
      exact ⟨e.target, e.open_target.mem_nhds hep_target, fun z hz => hbar_zero z hz⟩
    -- fderiv of a locally-zero function is zero
    have hfderiv_zero : fderiv ℝ (Infrastructure.wirtingerDerivBar (f.toFun ∘ e.symm)) (e p) =
        fderiv ℝ (fun _ => (0 : ℂ)) (e p) :=
      Filter.EventuallyEq.fderiv_eq hbar_eq
    -- wirtingerDeriv uses fderiv, so it's zero
    -- Bridge wirtingerDeriv_zbar = Infrastructure.wirtingerDerivBar, then unfold wirtingerDeriv
    have hwz_eq : wirtingerDeriv_zbar (f.toFun ∘ ↑e.symm) =
        Infrastructure.wirtingerDerivBar (f.toFun ∘ ↑e.symm) := rfl
    rw [hwz_eq]
    unfold Infrastructure.wirtingerDeriv
    rw [hfderiv_zero]
    simp

/-- A function is harmonic iff Δf = 0 -/
def SmoothFunction.IsHarmonic (f : SmoothFunction RS) : Prop :=
  laplacian_dbar_fun f = 0

/-- Holomorphic functions are harmonic -/
theorem holomorphic_implies_harmonic (f : SmoothFunction RS) (hf : f.IsHolomorphic) :
    f.IsHarmonic := by
  -- If ∂̄f = 0, then Δf = 4∂∂̄f = 4∂(0) = 0
  letI := RS.topology
  letI := RS.chartedSpace
  unfold SmoothFunction.IsHarmonic laplacian_dbar_fun
  congr 1
  funext p

  -- Get the chart at p
  let e := @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p
  have he : e ∈ atlas ℂ RS.carrier := chart_mem_atlas ℂ p

  -- Extract MDifferentiability from IsHolomorphic
  have hmDiff : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f.toFun :=
    (isHolomorphic_iff_mDifferentiable f).mp hf

  haveI : IsManifold 𝓘(ℂ, ℂ) ⊤ RS.carrier := RS.isManifold
  have hp_source : p ∈ e.source := mem_chart_source ℂ p
  have heP_target : e p ∈ e.target := e.map_source hp_source

  -- Key: wirtingerDerivBar (f ∘ e.symm) = 0 on e.target
  have hwbar_all : ∀ z ∈ e.target, wirtingerDeriv_zbar (f.toFun ∘ e.symm) z = 0 := by
    intro z hz
    -- By mdifferentiable_chart_diffAt, f ∘ e.symm is ℂ-differentiable at z
    have hdiff_z : DifferentiableAt ℂ (f.toFun ∘ e.symm) z :=
      mdifferentiable_chart_diffAt hmDiff e he z hz
    -- ℂ-differentiable implies wirtingerDerivBar = 0
    simp only [wirtingerDeriv_zbar]
    exact (Infrastructure.holomorphic_iff_wirtingerDerivBar_zero.mp hdiff_z).2

  -- wirtingerDerivBar (f ∘ e.symm) equals the zero function on the open set e.target
  -- Hence fderiv of this function at any point in e.target is zero
  -- Hence wirtingerDeriv at e p is zero

  have htarget_open : IsOpen e.target := e.open_target

  -- The function wirtingerDerivBar (f ∘ e.symm) is locally constant (= 0)
  -- fderiv of a locally constant function is zero
  have hfderiv_zero : fderiv ℝ (fun z => wirtingerDeriv_zbar (f.toFun ∘ e.symm) z) (e p) = 0 := by
    -- Use that f is locally zero on e.target
    have hlocal_zero : (fun z => wirtingerDeriv_zbar (f.toFun ∘ e.symm) z) =ᶠ[nhds (e p)] 0 := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      use e.target, IsOpen.mem_nhds htarget_open heP_target
      intro z hz
      exact hwbar_all z hz
    -- fderiv of a function that is locally constant zero is zero
    have hfderiv_const : fderiv ℝ (fun _ : ℂ => (0 : ℂ)) (e p) = 0 := fderiv_const_apply 0
    rw [hlocal_zero.fderiv_eq]
    exact hfderiv_const

  -- Now compute wirtingerDeriv
  simp only [wirtingerDeriv_z]
  unfold Infrastructure.wirtingerDeriv
  rw [hfderiv_zero]
  simp

/-!
## Harmonic 1-Forms
-/

/-- A (1,0)-form is harmonic iff it's holomorphic (∂̄ω = 0) -/
def Form_10.IsHarmonic (ω : Form_10 RS) : Prop :=
  dbar_10 ω = 0

/-- A (0,1)-form is harmonic iff it's antiholomorphic (∂ω = 0) -/
def Form_01.IsHarmonic (ω : Form_01 RS) : Prop :=
  -- ∂ω would be a (1,1)-form
  -- In our framework, this is equivalent to ω being the conjugate of a holomorphic form
  ∃ η : Form_10 RS, η.IsHarmonic ∧ ω = η.conj

/-- Holomorphic 1-forms are harmonic -/
theorem holomorphic_form_is_harmonic (ω : Form_10 RS) (hω : ω.IsHolomorphic') :
    ω.IsHarmonic := hω

/-!
## Linearity of ∂̄ on (1,0)-forms

The operator ∂̄ : Ω^{1,0} → Ω^{1,1} is ℂ-linear. This follows from linearity
of the Wirtinger derivative wirtingerDerivBar.
-/

/-- Helper: Form_10 sections composed with chart inverse are ℝ-differentiable.
    This is needed for applying wirtingerDerivBar algebraic lemmas. -/
private theorem form10_chart_differentiableAt (ω : Form_10 RS) (p : RS.carrier) :
    letI := RS.topology; letI := RS.chartedSpace
    DifferentiableAt ℝ (ω.toSection ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) := by
  letI := RS.topology; letI := RS.chartedSpace
  haveI : IsManifold 𝓘(ℂ, ℂ) ⊤ RS.carrier := RS.isManifold
  haveI : IsManifold 𝓘(ℝ, ℂ) ⊤ RS.carrier := isManifold_real_of_complex
  exact Infrastructure.differentiableAt_chart_comp_smoothOrder ω.smooth' p

/-- ∂̄ is additive: dbar_10 (ω₁ + ω₂) = dbar_10 ω₁ + dbar_10 ω₂ -/
theorem dbar_10_add (ω₁ ω₂ : Form_10 RS) :
    dbar_10 (ω₁ + ω₂) = dbar_10 ω₁ + dbar_10 ω₂ := by
  letI := RS.topology; letI := RS.chartedSpace
  apply Form_11.ext; funext p
  simp only [Form_11.add_toSection]
  -- At point p, the value of dbar_10 (ω₁ + ω₂) is
  -- -(wirtingerDerivBar ((ω₁ + ω₂).toSection ∘ e.symm) (e p))
  show -(Infrastructure.wirtingerDerivBar ((ω₁ + ω₂).toSection ∘
    (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm)
    ((@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p) p)) =
    -(Infrastructure.wirtingerDerivBar (ω₁.toSection ∘
      (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm)
      ((@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p) p)) +
    -(Infrastructure.wirtingerDerivBar (ω₂.toSection ∘
      (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm)
      ((@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p) p))
  -- (ω₁ + ω₂).toSection ∘ e.symm = (ω₁.toSection ∘ e.symm) + (ω₂.toSection ∘ e.symm)
  have hfun_eq : (ω₁ + ω₂).toSection ∘
      (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm =
      (ω₁.toSection ∘ (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm) +
      (ω₂.toSection ∘ (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm) := by
    ext z; simp only [Function.comp_apply, Form_10.add_toSection, Pi.add_apply]
  rw [hfun_eq]
  have h1 := form10_chart_differentiableAt ω₁ p
  have h2 := form10_chart_differentiableAt ω₂ p
  rw [Infrastructure.wirtingerDerivBar_add h1 h2]
  ring

/-- ∂̄ is ℂ-linear in scalar multiplication: dbar_10 (c • ω) = c • dbar_10 ω -/
theorem dbar_10_smul (c : ℂ) (ω : Form_10 RS) :
    dbar_10 (c • ω) = c • dbar_10 ω := by
  letI := RS.topology; letI := RS.chartedSpace
  apply Form_11.ext; funext p
  simp only [Form_11.smul_toSection]
  show -(Infrastructure.wirtingerDerivBar ((c • ω).toSection ∘
    (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm)
    ((@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p) p)) =
    c * -(Infrastructure.wirtingerDerivBar (ω.toSection ∘
      (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm)
      ((@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p) p))
  have hfun_eq : (c • ω).toSection ∘
      (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm =
      c • (ω.toSection ∘ (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm) := by
    ext z; simp only [Function.comp_apply, Form_10.smul_toSection, Pi.smul_apply, smul_eq_mul]
  rw [hfun_eq]
  have h := form10_chart_differentiableAt ω p
  rw [Infrastructure.wirtingerDerivBar_const_smul c h]
  ring

/-- Harmonic (1,0)-forms are closed under addition. -/
theorem isHarmonic_add {ω₁ ω₂ : Form_10 RS} (h₁ : ω₁.IsHarmonic) (h₂ : ω₂.IsHarmonic) :
    (ω₁ + ω₂).IsHarmonic := by
  unfold Form_10.IsHarmonic at *
  rw [dbar_10_add, h₁, h₂, add_zero]

/-- Harmonic (1,0)-forms are closed under scalar multiplication. -/
theorem isHarmonic_smul {ω : Form_10 RS} (c : ℂ) (h : ω.IsHarmonic) :
    (c • ω).IsHarmonic := by
  unfold Form_10.IsHarmonic at *
  rw [dbar_10_smul, h, smul_zero]

/-- Zero form is harmonic. -/
theorem isHarmonic_zero : (0 : Form_10 RS).IsHarmonic := by
  unfold Form_10.IsHarmonic
  rw [show (0 : Form_10 RS) = (0 : ℂ) • (0 : Form_10 RS) by simp]
  rw [dbar_10_smul, zero_smul]

/-- Negation preserves harmonicity. -/
theorem isHarmonic_neg {ω : Form_10 RS} (h : ω.IsHarmonic) : (-ω).IsHarmonic := by
  rw [show (-ω : Form_10 RS) = (-1 : ℂ) • ω by ext p; simp]
  exact isHarmonic_smul (-1) h

/-- Subtraction preserves harmonicity. -/
theorem isHarmonic_sub {ω₁ ω₂ : Form_10 RS} (h₁ : ω₁.IsHarmonic) (h₂ : ω₂.IsHarmonic) :
    (ω₁ - ω₂).IsHarmonic := by
  rw [sub_eq_add_neg]
  exact isHarmonic_add h₁ (isHarmonic_neg h₂)

/-- Harmonic (0,1)-forms are closed under addition. -/
theorem isHarmonic01_add {ω₁ ω₂ : Form_01 RS} (h₁ : ω₁.IsHarmonic) (h₂ : ω₂.IsHarmonic) :
    (ω₁ + ω₂).IsHarmonic := by
  rcases h₁ with ⟨η₁, hη₁, rfl⟩
  rcases h₂ with ⟨η₂, hη₂, rfl⟩
  refine ⟨η₁ + η₂, isHarmonic_add hη₁ hη₂, ?_⟩
  exact (Form_10.conj_add η₁ η₂).symm

/-- Zero (0,1)-form is harmonic. -/
theorem isHarmonic01_zero : (0 : Form_01 RS).IsHarmonic := by
  refine ⟨0, isHarmonic_zero, ?_⟩
  rw [Form_10.conj_zero]

/-- Harmonic (0,1)-forms are closed under scalar multiplication. -/
theorem isHarmonic01_smul {ω : Form_01 RS} (c : ℂ) (h : ω.IsHarmonic) :
    (c • ω).IsHarmonic := by
  rcases h with ⟨η, hη, rfl⟩
  refine ⟨(starRingEnd ℂ c) • η, isHarmonic_smul (starRingEnd ℂ c) hη, ?_⟩
  calc
    c • η.conj = starRingEnd ℂ (starRingEnd ℂ c) • η.conj := by simp
    _ = ((starRingEnd ℂ c) • η).conj := by rw [Form_10.conj_smul]

/-!
## The Space of Harmonic Forms

For a compact Riemann surface of genus g:
- dim H^{1,0}(X) = g (holomorphic 1-forms)
- dim H^{0,1}(X) = g (antiholomorphic 1-forms)
- dim H^1(X) = 2g (harmonic 1-forms)
-/

/-- Harmonic (1,0)-forms form a ℂ-submodule of all (1,0)-forms.
    This is the kernel of the ∂̄-operator, which is ℂ-linear. -/
def harmonicSubmodule10 (RS : RiemannSurface) : Submodule ℂ (Form_10 RS) where
  carrier := { ω | ω.IsHarmonic }
  add_mem' := fun ha hb => isHarmonic_add ha hb
  zero_mem' := isHarmonic_zero
  smul_mem' := fun c _ hω => isHarmonic_smul c hω

/-- Harmonic (0,1)-forms form a ℂ-submodule of all (0,1)-forms. -/
def harmonicSubmodule01 (RS : RiemannSurface) : Submodule ℂ (Form_01 RS) where
  carrier := { ω | ω.IsHarmonic }
  add_mem' := fun ha hb => isHarmonic01_add ha hb
  zero_mem' := isHarmonic01_zero
  smul_mem' := fun c _ hω => isHarmonic01_smul c hω

/-- Real scalar restriction on the carrier of `harmonicSubmodule10`. -/
noncomputable instance (RS : RiemannSurface) : Module ℝ (harmonicSubmodule10 RS) :=
  Module.compHom (harmonicSubmodule10 RS) (Complex.ofRealHom : ℝ →+* ℂ)

/-- Real scalar restriction on the carrier of `harmonicSubmodule01`. -/
noncomputable instance (RS : RiemannSurface) : Module ℝ (harmonicSubmodule01 RS) :=
  Module.compHom (harmonicSubmodule01 RS) (Complex.ofRealHom : ℝ →+* ℂ)

/-- The type of harmonic (1,0)-forms (holomorphic 1-forms) -/
def Harmonic10Forms (RS : RiemannSurface) := { ω : Form_10 RS // ω.IsHarmonic }

/-- The type of harmonic (0,1)-forms (antiholomorphic 1-forms) -/
def Harmonic01Forms (RS : RiemannSurface) := { ω : Form_01 RS // ω.IsHarmonic }

/-- Harmonic10Forms is equivalent to the harmonicSubmodule10 carrier. -/
def Harmonic10Forms.equivSubmodule (RS : RiemannSurface) :
    Harmonic10Forms RS ≃ harmonicSubmodule10 RS :=
  Equiv.subtypeEquivRight (fun _ => Iff.rfl)

/-- Harmonic01Forms is equivalent to the harmonicSubmodule01 carrier. -/
def Harmonic01Forms.equivSubmodule (RS : RiemannSurface) :
    Harmonic01Forms RS ≃ harmonicSubmodule01 RS :=
  Equiv.subtypeEquivRight (fun _ => Iff.rfl)

/-- Transport additive-group structure from the harmonic submodule to `Harmonic10Forms`. -/
noncomputable instance (RS : RiemannSurface) : AddCommGroup (Harmonic10Forms RS) :=
  (Harmonic10Forms.equivSubmodule RS).addCommGroup

/-- Transport `ℂ`-module structure from the harmonic submodule to `Harmonic10Forms`. -/
noncomputable instance (RS : RiemannSurface) : Module ℂ (Harmonic10Forms RS) :=
  Equiv.module ℂ (Harmonic10Forms.equivSubmodule RS)

/-- Real scalar restriction on `Harmonic10Forms`. -/
noncomputable instance (RS : RiemannSurface) : Module ℝ (Harmonic10Forms RS) :=
  Module.compHom (Harmonic10Forms RS) (Complex.ofRealHom : ℝ →+* ℂ)

/-- Linear equivalence between `Harmonic10Forms` and the harmonic submodule carrier. -/
noncomputable def Harmonic10Forms.linearEquivSubmodule (RS : RiemannSurface) :
    Harmonic10Forms RS ≃ₗ[ℂ] harmonicSubmodule10 RS :=
  Equiv.linearEquiv ℂ (Harmonic10Forms.equivSubmodule RS)

/-- Finrank transport for `Harmonic10Forms` through the subtype/submodule linear equivalence. -/
theorem Harmonic10Forms.finrank_eq_submodule_finrank (RS : RiemannSurface) :
    Module.finrank ℂ (Harmonic10Forms RS) = Module.finrank ℂ (harmonicSubmodule10 RS) := by
  simpa using LinearEquiv.finrank_eq (Harmonic10Forms.linearEquivSubmodule RS)

/-- Transport additive-group structure from the harmonic submodule to `Harmonic01Forms`. -/
noncomputable instance (RS : RiemannSurface) : AddCommGroup (Harmonic01Forms RS) :=
  (Harmonic01Forms.equivSubmodule RS).addCommGroup

/-- Transport `ℂ`-module structure from the harmonic submodule to `Harmonic01Forms`. -/
noncomputable instance (RS : RiemannSurface) : Module ℂ (Harmonic01Forms RS) :=
  Equiv.module ℂ (Harmonic01Forms.equivSubmodule RS)

/-- Real scalar restriction on `Harmonic01Forms`. -/
noncomputable instance (RS : RiemannSurface) : Module ℝ (Harmonic01Forms RS) :=
  Module.compHom (Harmonic01Forms RS) (Complex.ofRealHom : ℝ →+* ℂ)

/-- Linear equivalence between `Harmonic01Forms` and the harmonic submodule carrier. -/
noncomputable def Harmonic01Forms.linearEquivSubmodule (RS : RiemannSurface) :
    Harmonic01Forms RS ≃ₗ[ℂ] harmonicSubmodule01 RS :=
  Equiv.linearEquiv ℂ (Harmonic01Forms.equivSubmodule RS)

/-- Finrank transport for `Harmonic01Forms` through the subtype/submodule linear equivalence. -/
theorem Harmonic01Forms.finrank_eq_submodule_finrank (RS : RiemannSurface) :
    Module.finrank ℂ (Harmonic01Forms RS) = Module.finrank ℂ (harmonicSubmodule01 RS) := by
  simpa using LinearEquiv.finrank_eq (Harmonic01Forms.linearEquivSubmodule RS)

/-- Conjugation gives an isomorphism H^{1,0} ≅ H^{0,1} -/
noncomputable def conjugate_harmonic_iso (RS : RiemannSurface) :
    Harmonic10Forms RS → Harmonic01Forms RS := fun ⟨ω, hω⟩ =>
  ⟨ω.conj, ⟨ω, hω, rfl⟩⟩

theorem conjugate_harmonic_iso_bijective (RS : RiemannSurface) :
    Function.Bijective (conjugate_harmonic_iso RS) := by
  constructor
  · -- Injective
    intro ⟨ω₁, h₁⟩ ⟨ω₂, h₂⟩ heq
    simp only [conjugate_harmonic_iso] at heq
    have heq' : ω₁.conj = ω₂.conj := Subtype.ext_iff.mp heq
    have := congr_arg Form_01.conj heq'
    simp only [Form_10.conj_conj] at this
    exact Subtype.ext this
  · -- Surjective
    intro ⟨ω, hω⟩
    obtain ⟨η, hη, rfl⟩ := hω
    exact ⟨⟨η, hη⟩, rfl⟩

/-- Conjugation as an explicit equivalence `H^{1,0} ≃ H^{0,1}`. -/
noncomputable def conjugate_harmonic_equiv (RS : RiemannSurface) :
    Harmonic10Forms RS ≃ Harmonic01Forms RS :=
  Equiv.ofBijective (conjugate_harmonic_iso RS) (conjugate_harmonic_iso_bijective RS)

/-- Conjugation equivalence transported to harmonic submodule carriers. -/
noncomputable def conjugate_harmonic_submodule_equiv (RS : RiemannSurface) :
    harmonicSubmodule10 RS ≃ harmonicSubmodule01 RS :=
  (Harmonic10Forms.equivSubmodule RS).symm.trans
    ((conjugate_harmonic_equiv RS).trans (Harmonic01Forms.equivSubmodule RS))

/-- Conjugation as an `ℝ`-linear equivalence on harmonic submodule carriers. -/
noncomputable def conjugate_harmonic_submodule_realLinearEquiv (RS : RiemannSurface) :
    harmonicSubmodule10 RS ≃ₗ[ℝ] harmonicSubmodule01 RS where
  toFun := fun ω => ⟨ω.1.conj, ⟨ω.1, ω.2, rfl⟩⟩
  invFun := fun ω =>
    ⟨ω.1.conj, by
      rcases ω.2 with ⟨η, hη, hω⟩
      simpa [hω, Form_10.conj_conj] using hη⟩
  left_inv := by
    intro ω
    apply Subtype.ext
    exact Form_10.conj_conj ω.1
  right_inv := by
    intro ω
    apply Subtype.ext
    exact Form_01.conj_conj ω.1
  map_add' := by
    intro ω₁ ω₂
    apply Subtype.ext
    exact Form_10.conj_add ω₁.1 ω₂.1
  map_smul' := by
    intro r ω
    apply Subtype.ext
    simpa using (Form_10.conj_smul (r : ℂ) ω.1)

theorem dbar_fun_eq_zero (f : SmoothFunction RS) : dbar_fun f = 0 := by
  have hhol : f.IsHolomorphic := by
    rw [isHolomorphic_iff_mDifferentiable]
    letI := RS.topology
    letI := RS.chartedSpace
    haveI := RS.isManifold
    exact f.smooth'.mdifferentiable (by decide : (⊤ : WithTop ℕ∞) ≠ 0)
  simpa [SmoothFunction.IsHolomorphic] using hhol

/-!
## Hodge Decomposition Theorem

The main theorem: every (p,q)-form decomposes uniquely as
  ω = ω_harm + ∂̄α + ∂̄⋆β

where ω_harm is harmonic.
-/

/-!
## De Rham Cohomology Infrastructure

H¹_dR(X, ℂ) = closed 1-forms / exact 1-forms.

On a Riemann surface (complex dim 1), a 1-form decomposes as ω = α + β where
α ∈ Ω^{1,0} and β ∈ Ω^{0,1}. The exterior derivative is:
  dω = ∂̄α + ∂β ∈ Ω^{1,1}
(since ∂α ∈ Ω^{2,0} = 0 and ∂̄β ∈ Ω^{0,2} = 0 on a surface).

Exact 1-forms are df = (∂f, ∂̄f) for ℝ-smooth f.
-/

/-- The ∂ operator on (0,1)-forms: ∂(g dz̄) = (∂g/∂z) dz ∧ dz̄.
    Mirror of `dbar_10` using `wirtingerDeriv_z` instead of `wirtingerDeriv_zbar`.
    No sign flip (unlike ∂̄ on (1,0)-forms) because dz ∧ dz̄ is the standard ordering. -/
noncomputable def del_01 (ω : Form_01 RS) : Form_11 RS := by
  letI := RS.topology
  letI := RS.chartedSpace
  exact Form_11.mk (fun p =>
    wirtingerDeriv_z (ω.toSection ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p))

/-- Smoothness infrastructure for `dbar_real_hd`. -/
private theorem realSmooth_comp_chart_symm_contDiffOn_hd
    (f : RealSmoothFunction RS) (p0 : RS.carrier) (n : ℕ∞) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContDiffOn ℝ (n : WithTop ℕ∞) (f.toFun ∘ (chartAt ℂ p0).symm) (chartAt ℂ p0).target := by
  simpa using RealSmoothFunction.contDiffOn_comp_chart_symm (f := f) (p0 := p0) (n := n)

private theorem wirtingerDerivBar_chart_comp_contDiffOn_hd
    (f : RealSmoothFunction RS) (p0 : RS.carrier) (n : ℕ∞) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContDiffOn ℝ (n : WithTop ℕ∞) (wirtingerDeriv_zbar (f.toFun ∘ (chartAt ℂ p0).symm))
      (chartAt ℂ p0).target := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hcomp :
      ContDiffOn ℝ ((n + 1 : ℕ∞) : WithTop ℕ∞) (f.toFun ∘ (chartAt ℂ p0).symm)
        (chartAt ℂ p0).target := by
    simpa using realSmooth_comp_chart_symm_contDiffOn_hd (RS := RS) f p0 (n + 1)
  simpa [wirtingerDeriv_zbar] using
    (Infrastructure.wirtingerDerivBar_contDiffOn
      (f := f.toFun ∘ (chartAt ℂ p0).symm)
      (s := (chartAt ℂ p0).target) (n := n)
      hcomp (chartAt ℂ p0).open_target)

private theorem realSmooth_comp_chart_symm_contDiffAt_hd_of_mem
    (f : RealSmoothFunction RS) (p0 : RS.carrier) (n : ℕ∞) :
    letI := RS.topology
    letI := RS.chartedSpace
    ∀ {z : ℂ}, z ∈ (chartAt ℂ p0).target →
      ContDiffAt ℝ (n : WithTop ℕ∞) (f.toFun ∘ (chartAt ℂ p0).symm) z := by
  letI := RS.topology
  letI := RS.chartedSpace
  intro z hz
  have hOn :
      ContDiffOn ℝ (n : WithTop ℕ∞) (f.toFun ∘ (chartAt ℂ p0).symm) (chartAt ℂ p0).target := by
    exact realSmooth_comp_chart_symm_contDiffOn_hd (RS := RS) f p0 n
  exact hOn.contDiffAt ((chartAt ℂ p0).open_target.mem_nhds hz)

private theorem realSmooth_comp_chart_symm_contDiffAt_hd
    (f : RealSmoothFunction RS) (p0 : RS.carrier) (n : ℕ∞) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContDiffAt ℝ (n : WithTop ℕ∞) (f.toFun ∘ (chartAt ℂ p0).symm) ((chartAt ℂ p0) p0) := by
  letI := RS.topology
  letI := RS.chartedSpace
  exact realSmooth_comp_chart_symm_contDiffAt_hd_of_mem (RS := RS) f p0 n
    (z := (chartAt ℂ p0) p0) (mem_chart_target ℂ p0)

private theorem wirtingerDerivBar_chart_comp_contDiffAt_hd_of_mem
    (f : RealSmoothFunction RS) (p0 : RS.carrier) (n : ℕ∞) :
    letI := RS.topology
    letI := RS.chartedSpace
    ∀ {z : ℂ}, z ∈ (chartAt ℂ p0).target →
      ContDiffAt ℝ (n : WithTop ℕ∞)
        (wirtingerDeriv_zbar (f.toFun ∘ (chartAt ℂ p0).symm)) z := by
  letI := RS.topology
  letI := RS.chartedSpace
  intro z hz
  have hOn :
      ContDiffOn ℝ (n : WithTop ℕ∞) (wirtingerDeriv_zbar (f.toFun ∘ (chartAt ℂ p0).symm))
        (chartAt ℂ p0).target := by
    exact wirtingerDerivBar_chart_comp_contDiffOn_hd (RS := RS) f p0 n
  exact hOn.contDiffAt ((chartAt ℂ p0).open_target.mem_nhds hz)

private theorem wirtingerDerivBar_chart_comp_contDiffAt_hd
    (f : RealSmoothFunction RS) (p0 : RS.carrier) (n : ℕ∞) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContDiffAt ℝ (n : WithTop ℕ∞)
      (wirtingerDeriv_zbar (f.toFun ∘ (chartAt ℂ p0).symm)) ((chartAt ℂ p0) p0) := by
  letI := RS.topology
  letI := RS.chartedSpace
  exact wirtingerDerivBar_chart_comp_contDiffAt_hd_of_mem (RS := RS) f p0 n
    (z := (chartAt ℂ p0) p0) (mem_chart_target ℂ p0)

/-- With a fixed chart center `p0`, the local `∂̄` coefficient expression is
`C^∞` on the chart source as a manifold map. -/
private theorem dbar_real_local_fixedChart_contMDiffOn_hd
    (f : RealSmoothFunction RS) (p0 : RS.carrier) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : RS.carrier =>
        wirtingerDeriv_zbar (f.toFun ∘ (chartAt ℂ p0).symm) ((chartAt ℂ p0) p))
      (chartAt ℂ p0).source := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI : IsManifold 𝓘(ℂ, ℂ) ⊤ RS.carrier := RS.isManifold
  haveI : IsManifold 𝓘(ℝ, ℂ) ⊤ RS.carrier := isManifold_real_of_complex
  have hfixed_contDiff :
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (wirtingerDeriv_zbar (f.toFun ∘ (chartAt ℂ p0).symm)) (chartAt ℂ p0).target := by
    simpa using wirtingerDerivBar_chart_comp_contDiffOn_hd (RS := RS) f p0 (n := (⊤ : ℕ∞))
  have hfixed_md :
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (wirtingerDeriv_zbar (f.toFun ∘ (chartAt ℂ p0).symm)) (chartAt ℂ p0).target := by
    exact hfixed_contDiff.contMDiffOn
  have hchart :
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (chartAt ℂ p0) (chartAt ℂ p0).source := by
    simpa using (contMDiffOn_chart (I := 𝓘(ℝ, ℂ)) (H := ℂ) (x := p0))
  refine hfixed_md.comp hchart ?_
  intro p hp
  exact (chartAt ℂ p0).map_source hp

/-- Pointwise version of `dbar_real_local_fixedChart_contMDiffOn_hd` at the chart center. -/
private theorem dbar_real_local_fixedChart_contMDiffAt_hd
    (f : RealSmoothFunction RS) (p0 : RS.carrier) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : RS.carrier =>
        wirtingerDeriv_zbar (f.toFun ∘ (chartAt ℂ p0).symm) ((chartAt ℂ p0) p))
      p0 := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hOn := dbar_real_local_fixedChart_contMDiffOn_hd (RS := RS) f p0
  exact hOn.contMDiffAt (chart_source_mem_nhds (H := ℂ) p0)

/-- Global section candidate used in `dbar_real_hd`. -/
private noncomputable def dbarRealSectionCandidate_hd (f : RealSmoothFunction RS) :
    RS.carrier → ℂ := by
  letI := RS.topology
  letI := RS.chartedSpace
  exact fun p =>
    let e := @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p
    wirtingerDeriv_zbar (f.toFun ∘ e.symm) (e p)

/-- Pointwise chart-change formula for the `dbarRealSectionCandidate_hd` coefficient. -/
private theorem dbarRealSectionCandidate_chartChange_hd
    (f : RealSmoothFunction RS) (p0 p : RS.carrier)
    (hp0 :
      letI := RS.topology
      letI := RS.chartedSpace
      p ∈ (chartAt ℂ p0).source) :
    letI := RS.topology
    letI := RS.chartedSpace
    dbarRealSectionCandidate_hd (RS := RS) f p =
      wirtingerDeriv_zbar (f.toFun ∘ (chartAt ℂ p0).symm) ((chartAt ℂ p0) p) *
        starRingEnd ℂ (deriv (chartTransition (RS := RS) p0 p) ((chartAt ℂ p) p)) := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hp : p ∈ (eChart (RS := RS) p).source := by
    simp [eChart]
  have hp0' : p ∈ (eChart (RS := RS) p0).source := by
    simpa [eChart] using hp0
  have hchange :=
    wirtingerDerivBar_extChart_symm_change_at_point_of_realSmooth
      (RS := RS) (f := f) (q := p0) (r := p) (p := p) hp hp0'
  simpa [dbarRealSectionCandidate_hd, wirtingerDeriv_zbar, eChart, chartTransition,
    Function.comp_apply, hp] using hchange

/-- Fixed-chart overlap formula for local `∂̄` coefficients, using chart-indexed
transition-factor infrastructure. -/
theorem dbarRealLocalCoeff_chartChange_fixedCharts_hd
    (f : RealSmoothFunction RS) (q r p : RS.carrier)
    (hp_r :
      letI := RS.topology
      letI := RS.chartedSpace
      p ∈ (eChart (RS := RS) r).source)
    (hp_q :
      letI := RS.topology
      letI := RS.chartedSpace
      p ∈ (eChart (RS := RS) q).source) :
    letI := RS.topology
    letI := RS.chartedSpace
    wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) r).symm) ((eChart (RS := RS) r) p) =
      wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) q).symm)
          (chartTransition (RS := RS) q r ((eChart (RS := RS) r) p)) *
        Infrastructure.chartTransitionFactorByCharts (RS := RS) q r p := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hchange :=
    wirtingerDerivBar_extChart_symm_change_at_point_of_realSmooth
      (RS := RS) (f := f) (q := q) (r := r) (p := p) hp_r hp_q
  simpa [Infrastructure.chartTransitionFactorByCharts,
    Infrastructure.chartTransitionFactorInCharts, wirtingerDeriv_zbar] using hchange

/-- Neighborhood-level fixed-chart overlap identity for local `∂̄` coefficients. -/
theorem dbarRealLocalCoeff_eventuallyEq_fixedCharts_hd
    (f : RealSmoothFunction RS) (q r p : RS.carrier)
    (hp_r :
      letI := RS.topology
      letI := RS.chartedSpace
      p ∈ (eChart (RS := RS) r).source)
    (hp_q :
      letI := RS.topology
      letI := RS.chartedSpace
      p ∈ (eChart (RS := RS) q).source) :
    letI := RS.topology
    letI := RS.chartedSpace
    (fun x : RS.carrier =>
      wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) r).symm) ((eChart (RS := RS) r) x))
      =ᶠ[nhds p]
    (fun x : RS.carrier =>
      wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) q).symm)
          (chartTransition (RS := RS) q r ((eChart (RS := RS) r) x)) *
        Infrastructure.chartTransitionFactorByCharts (RS := RS) q r x) := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hp_r_chart : p ∈ (chartAt ℂ r).source := by
    simpa [eChart] using hp_r
  have hp_q_chart : p ∈ (chartAt ℂ q).source := by
    simpa [eChart] using hp_q
  have hsrc_r_chart : (chartAt ℂ r).source ∈ nhds p :=
    (chartAt ℂ r).open_source.mem_nhds hp_r_chart
  have hsrc_q_chart : (chartAt ℂ q).source ∈ nhds p :=
    (chartAt ℂ q).open_source.mem_nhds hp_q_chart
  have hsrc_r : ∀ᶠ x in nhds p, x ∈ (eChart (RS := RS) r).source := by
    refine Filter.mem_of_superset hsrc_r_chart ?_
    intro x hx
    simpa [eChart] using hx
  have hsrc_q : ∀ᶠ x in nhds p, x ∈ (eChart (RS := RS) q).source := by
    refine Filter.mem_of_superset hsrc_q_chart ?_
    intro x hx
    simpa [eChart] using hx
  exact (hsrc_r.and hsrc_q).mono (fun x hx =>
    dbarRealLocalCoeff_chartChange_fixedCharts_hd (RS := RS) f q r x hx.1 hx.2)

/-- Same section candidate but computed in one fixed chart `chartAt p0`. -/
private noncomputable def dbarRealSectionInChart_hd
    (f : RealSmoothFunction RS) (p0 : RS.carrier) : RS.carrier → ℂ := by
  letI := RS.topology
  letI := RS.chartedSpace
  exact fun p =>
    let e0 := @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p0
    wirtingerDeriv_zbar (f.toFun ∘ e0.symm) (e0 p)

private theorem dbarRealSectionInChart_contMDiffAt_hd
    (f : RealSmoothFunction RS) (p0 : RS.carrier) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (dbarRealSectionInChart_hd (RS := RS) f p0) p0 := by
  letI := RS.topology
  letI := RS.chartedSpace
  simpa [dbarRealSectionInChart_hd] using
    dbar_real_local_fixedChart_contMDiffAt_hd (RS := RS) f p0

private theorem dbarRealSectionCandidate_contMDiffAt_of_eventuallyEq_chart_hd
    (f : RealSmoothFunction RS) (p0 : RS.carrier)
    (hchart :
      letI := RS.topology
      letI := RS.chartedSpace
      (fun p : RS.carrier => @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p)
        =ᶠ[nhds p0]
      (fun _ : RS.carrier => @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p0)) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (dbarRealSectionCandidate_hd (RS := RS) f) p0 := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hloc :
      dbarRealSectionCandidate_hd (RS := RS) f =ᶠ[nhds p0]
        dbarRealSectionInChart_hd (RS := RS) f p0 := by
    refine hchart.mono ?_
    intro p hp
    simp [dbarRealSectionCandidate_hd, dbarRealSectionInChart_hd, hp]
  exact (dbarRealSectionInChart_contMDiffAt_hd (RS := RS) f p0).congr_of_eventuallyEq hloc

/-- Fixed-chart coefficient factor appearing in local chart-change decomposition of `dbar`. -/
private noncomputable def dbarRealFixedPart_hd
    (f : RealSmoothFunction RS) (p0 : RS.carrier) : RS.carrier → ℂ := by
  letI := RS.topology
  letI := RS.chartedSpace
  exact fun p =>
    wirtingerDeriv_zbar (f.toFun ∘ (chartAt ℂ p0).symm) ((chartAt ℂ p0) p)

/-- Transition-Jacobian factor appearing in local chart-change decomposition of `dbar`. -/
private noncomputable def dbarRealTransitionFactor_hd
    (p0 : RS.carrier) : RS.carrier → ℂ := by
  exact Infrastructure.chartTransitionFactor (RS := RS) p0

/-- On chart overlaps, the right-hand side of the fixed-chart `∂̄` coefficient
change formula is smooth at the overlap point. -/
theorem dbarRealLocalCoeff_rhs_contMDiffAt_fixedCharts_hd
    (f : RealSmoothFunction RS) (q r p : RS.carrier)
    (hp_r :
      letI := RS.topology
      letI := RS.chartedSpace
      p ∈ (eChart (RS := RS) r).source)
    (hp_q :
      letI := RS.topology
      letI := RS.chartedSpace
      p ∈ (eChart (RS := RS) q).source) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
      (fun x : RS.carrier =>
        wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) q).symm)
            (chartTransition (RS := RS) q r ((eChart (RS := RS) r) x)) *
          Infrastructure.chartTransitionFactorByCharts (RS := RS) q r x) p := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hz_tgt : ((eChart (RS := RS) r) p) ∈ (eChart (RS := RS) r).target :=
    (eChart (RS := RS) r).map_source hp_r
  have hovlp : (eChart (RS := RS) r).symm ((eChart (RS := RS) r) p) ∈
      (eChart (RS := RS) q).source := by
    rw [(eChart (RS := RS) r).left_inv hp_r]
    exact hp_q
  have htrans_tgt :
      chartTransition (RS := RS) q r ((eChart (RS := RS) r) p) ∈ (chartAt ℂ q).target := by
    simpa [chartTransition, eChart, Function.comp_apply] using
      (eChart (RS := RS) q).map_source hovlp
  have hphiTop : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) q).symm))
      (chartTransition (RS := RS) q r ((eChart (RS := RS) r) p)) := by
    simpa [eChart] using
      (wirtingerDerivBar_chart_comp_contDiffAt_hd_of_mem
        (RS := RS) f q (n := (⊤ : ℕ∞))
        (z := chartTransition (RS := RS) q r ((eChart (RS := RS) r) p)) htrans_tgt)
  have hsmooth : smoothOrder ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    simp [smoothOrder]
  have hphi : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
      (wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) q).symm))
      (chartTransition (RS := RS) q r ((eChart (RS := RS) r) p)) :=
    (hphiTop.of_le hsmooth).contMDiffAt
  have htransComp : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
      (fun x : RS.carrier => chartTransition (RS := RS) q r ((eChart (RS := RS) r) x)) p :=
    Infrastructure.chartTransitionByCharts_contMDiffAt (RS := RS) q r p hp_r hp_q
  have hfirst : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
      (fun x : RS.carrier =>
        wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) q).symm)
          (chartTransition (RS := RS) q r ((eChart (RS := RS) r) x))) p := by
    simpa [Function.comp] using hphi.comp p htransComp
  have hfactor : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
      (Infrastructure.chartTransitionFactorByCharts (RS := RS) q r) p :=
    Infrastructure.chartTransitionFactorByCharts_contMDiffAt (RS := RS) q r p hp_r hp_q
  have hmulSmooth : ContDiff ℝ smoothOrder (fun z : ℂ × ℂ => z.1 * z.2) := by
    exact (contDiff_mul : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun z : ℂ × ℂ => z.1 * z.2)).of_le
      smoothOrder_le_top
  have hpair :
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ × ℂ) smoothOrder
        (fun x => ((fun y : RS.carrier =>
          wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) q).symm)
            (chartTransition (RS := RS) q r ((eChart (RS := RS) r) y))) x,
          Infrastructure.chartTransitionFactorByCharts (RS := RS) q r x)) p :=
    hfirst.prodMk_space hfactor
  have hmulMap :
      ContMDiffAt 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ) smoothOrder
        (fun z : ℂ × ℂ => z.1 * z.2)
        (((fun y : RS.carrier =>
          wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) q).symm)
            (chartTransition (RS := RS) q r ((eChart (RS := RS) r) y))) p,
          Infrastructure.chartTransitionFactorByCharts (RS := RS) q r p)) :=
    (hmulSmooth.contMDiff).contMDiffAt
  simpa [Function.comp] using hmulMap.comp p hpair

/-- Over chart overlaps, local `∂̄` coefficients in a fixed source chart inherit
pointwise smoothness from the fixed-chart change formula. -/
theorem dbarRealLocalCoeff_contMDiffAt_fixedCharts_hd
    (f : RealSmoothFunction RS) (q r p : RS.carrier)
    (hp_r :
      letI := RS.topology
      letI := RS.chartedSpace
      p ∈ (eChart (RS := RS) r).source)
    (hp_q :
      letI := RS.topology
      letI := RS.chartedSpace
      p ∈ (eChart (RS := RS) q).source) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
      (fun x : RS.carrier =>
        wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) r).symm) ((eChart (RS := RS) r) x)) p := by
  letI := RS.topology
  letI := RS.chartedSpace
  have heq :
      (fun x : RS.carrier =>
        wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) r).symm) ((eChart (RS := RS) r) x))
        =ᶠ[nhds p]
      (fun x : RS.carrier =>
        wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) q).symm)
            (chartTransition (RS := RS) q r ((eChart (RS := RS) r) x)) *
          Infrastructure.chartTransitionFactorByCharts (RS := RS) q r x) :=
    dbarRealLocalCoeff_eventuallyEq_fixedCharts_hd (RS := RS) f q r p hp_r hp_q
  have hrhs :
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
        (fun x : RS.carrier =>
          wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) q).symm)
              (chartTransition (RS := RS) q r ((eChart (RS := RS) r) x)) *
            Infrastructure.chartTransitionFactorByCharts (RS := RS) q r x) p :=
    dbarRealLocalCoeff_rhs_contMDiffAt_fixedCharts_hd (RS := RS) f q r p hp_r hp_q
  exact hrhs.congr_of_eventuallyEq heq

/-- Over chart overlaps, local fixed-chart `∂̄` coefficients are smooth in `WithinAt` form
for local-to-global assembly usage. -/
theorem dbarRealLocalCoeff_contMDiffWithinAt_fixedCharts_hd
    (f : RealSmoothFunction RS) (q r p : RS.carrier)
    (hp_r :
      letI := RS.topology
      letI := RS.chartedSpace
      p ∈ (eChart (RS := RS) r).source)
    (hp_q :
      letI := RS.topology
      letI := RS.chartedSpace
      p ∈ (eChart (RS := RS) q).source) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
      (fun x : RS.carrier =>
        wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) r).symm) ((eChart (RS := RS) r) x))
      ((eChart (RS := RS) r).source ∩ (eChart (RS := RS) q).source) p := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hAt :
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
        (fun x : RS.carrier =>
          wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) r).symm) ((eChart (RS := RS) r) x))
        p :=
    dbarRealLocalCoeff_contMDiffAt_fixedCharts_hd (RS := RS) f q r p hp_r hp_q
  exact hAt.contMDiffWithinAt

/-- Coordinate-level overlap regularity package for fixed-chart local `∂̄` coefficients:
`C^∞` within the chart-overlap set in source chart coordinates. -/
theorem dbarRealLocalCoeff_contDiffWithinAt_chartOverlap_fixedCharts_hd
    (f : RealSmoothFunction RS) (q r p : RS.carrier)
    (hp_r :
      letI := RS.topology
      letI := RS.chartedSpace
      p ∈ (eChart (RS := RS) r).source)
    (hp_q :
      letI := RS.topology
      letI := RS.chartedSpace
      p ∈ (eChart (RS := RS) q).source) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContDiffWithinAt ℝ smoothOrder
      (fun z : ℂ => wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) r).symm) z)
      ((eChart (RS := RS) r).target ∩
        (chartTransition (RS := RS) q r) ⁻¹' (eChart (RS := RS) q).target)
      ((eChart (RS := RS) r) p) := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hOnTop :
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) r).symm))
        (eChart (RS := RS) r).target := by
    simpa [eChart] using
      wirtingerDerivBar_chart_comp_contDiffOn_hd (RS := RS) f r (n := (⊤ : ℕ∞))
  have hsmooth : smoothOrder ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    simp [smoothOrder]
  have hOn :
      ContDiffOn ℝ smoothOrder
        (wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) r).symm))
        (eChart (RS := RS) r).target :=
    hOnTop.of_le hsmooth
  have hOnSub :
      ContDiffOn ℝ smoothOrder
        (wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) r).symm))
        ((eChart (RS := RS) r).target ∩
          (chartTransition (RS := RS) q r) ⁻¹' (eChart (RS := RS) q).target) := by
    refine hOn.mono ?_
    intro z hz
    exact hz.1
  have hmem :
      ((eChart (RS := RS) r) p) ∈
        ((eChart (RS := RS) r).target ∩
          (chartTransition (RS := RS) q r) ⁻¹' (eChart (RS := RS) q).target) := by
    refine ⟨(eChart (RS := RS) r).map_source hp_r, ?_⟩
    have hovlp : (eChart (RS := RS) r).symm ((eChart (RS := RS) r) p) ∈
        (eChart (RS := RS) q).source := by
      rw [(eChart (RS := RS) r).left_inv hp_r]
      exact hp_q
    simpa [chartTransition, Function.comp_apply] using
      (eChart (RS := RS) q).map_source hovlp
  exact hOnSub.contDiffWithinAt hmem

/-- Fixed-chart overlap nonvanishing of the chart-indexed transition factor. -/
private theorem dbarRealTransitionFactorByCharts_ne_zero_hd
    (q r p : RS.carrier)
    (hp_r :
      letI := RS.topology
      letI := RS.chartedSpace
      p ∈ (eChart (RS := RS) r).source)
    (hp_q :
      letI := RS.topology
      letI := RS.chartedSpace
      p ∈ (eChart (RS := RS) q).source) :
    letI := RS.topology
    letI := RS.chartedSpace
    Infrastructure.chartTransitionFactorByCharts (RS := RS) q r p ≠ 0 := by
  exact Infrastructure.chartTransitionFactorByCharts_ne_zero
    (RS := RS) q r p hp_r hp_q

/-- Fixed-chart overlap neighborhood nonvanishing of the chart-indexed transition factor. -/
private theorem dbarRealTransitionFactorByCharts_eventually_ne_zero_hd
    (q r p : RS.carrier)
    (hp_r :
      letI := RS.topology
      letI := RS.chartedSpace
      p ∈ (eChart (RS := RS) r).source)
    (hp_q :
      letI := RS.topology
      letI := RS.chartedSpace
      p ∈ (eChart (RS := RS) q).source) :
    letI := RS.topology
    letI := RS.chartedSpace
    ∀ᶠ x in nhds p, Infrastructure.chartTransitionFactorByCharts (RS := RS) q r x ≠ 0 := by
  exact Infrastructure.chartTransitionFactorByCharts_eventually_ne_zero
    (RS := RS) q r p hp_r hp_q

/-- Conditional local smoothness: if `chartAt` is eventually constant near `p0`,
the transition factor is smooth at `p0`. -/
private theorem dbarRealTransitionFactor_contMDiffAt_of_eventuallyEq_chart_hd
    (p0 : RS.carrier)
    (hchart :
      letI := RS.topology
      letI := RS.chartedSpace
      (fun p : RS.carrier => @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p)
        =ᶠ[nhds p0]
      (fun _ : RS.carrier => @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p0)) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
      (dbarRealTransitionFactor_hd (RS := RS) p0) p0 := by
  simpa [dbarRealTransitionFactor_hd] using
    Infrastructure.chartTransitionFactor_contMDiffAt_of_eventuallyEq_chart
      (RS := RS) (n := smoothOrder) p0 hchart

/-- Near `p0`, the chart-varying `dbar` coefficient equals fixed-chart part times transition factor. -/
private theorem dbarRealSectionCandidate_eventuallyEq_fixed_mul_transition_hd
    (f : RealSmoothFunction RS) (p0 : RS.carrier) :
    letI := RS.topology
    letI := RS.chartedSpace
    dbarRealSectionCandidate_hd (RS := RS) f =ᶠ[nhds p0]
      fun p =>
        dbarRealFixedPart_hd (RS := RS) f p0 p *
          dbarRealTransitionFactor_hd (RS := RS) p0 p := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hsrc : ∀ᶠ p in nhds p0, p ∈ (chartAt ℂ p0).source :=
    (chartAt ℂ p0).open_source.mem_nhds (mem_chart_source ℂ p0)
  refine hsrc.mono ?_
  intro p hp
  have hchange := dbarRealSectionCandidate_chartChange_hd (RS := RS) f p0 p hp
  simpa [dbarRealFixedPart_hd, dbarRealTransitionFactor_hd] using hchange

/-- Pointwise smoothness of the global `dbar` section candidate, assuming smoothness of the
transition-Jacobian factor at the center point. -/
private theorem dbarRealSectionCandidate_contMDiffAt_of_transitionFactor_contMDiffAt_hd
    (f : RealSmoothFunction RS) (p0 : RS.carrier)
    (htrans :
      letI := RS.topology
      letI := RS.chartedSpace
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
        (dbarRealTransitionFactor_hd (RS := RS) p0) p0) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
      (dbarRealSectionCandidate_hd (RS := RS) f) p0 := by
  letI := RS.topology
  letI := RS.chartedSpace
  set fixedPart := dbarRealFixedPart_hd (RS := RS) f p0
  set transFactor := dbarRealTransitionFactor_hd (RS := RS) p0
  have hloc :
      dbarRealSectionCandidate_hd (RS := RS) f =ᶠ[nhds p0]
        fun p => fixedPart p * transFactor p := by
    simpa [fixedPart, transFactor] using
      dbarRealSectionCandidate_eventuallyEq_fixed_mul_transition_hd (RS := RS) f p0
  have hfixedTop :
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) fixedPart p0 := by
    simpa [fixedPart, dbarRealFixedPart_hd] using
      dbar_real_local_fixedChart_contMDiffAt_hd (RS := RS) f p0
  have hfixed :
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder fixedPart p0 :=
    by simpa [smoothOrder] using hfixedTop
  have htrans' :
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder transFactor p0 := by
    simpa [transFactor] using htrans
  have hmulSmooth : ContDiff ℝ smoothOrder (fun z : ℂ × ℂ => z.1 * z.2) := by
    exact (contDiff_mul : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun z : ℂ × ℂ => z.1 * z.2)).of_le
      smoothOrder_le_top
  have hpair :
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ × ℂ) smoothOrder
        (fun p => (fixedPart p, transFactor p)) p0 :=
    hfixed.prodMk_space htrans'
  have hmulMap :
      ContMDiffAt 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ) smoothOrder
        (fun z : ℂ × ℂ => z.1 * z.2) ((fixedPart p0, transFactor p0)) :=
    (hmulSmooth.contMDiff).contMDiffAt
  have hmul :
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
        (fun p => fixedPart p * transFactor p) p0 := by
    simpa [Function.comp] using hmulMap.comp p0 hpair
  exact hmul.congr_of_eventuallyEq hloc

/-- Pointwise continuity of the global `dbar` section candidate, assuming continuity of the
transition-Jacobian factor at the center point. -/
private theorem dbarRealSectionCandidate_continuousAt_of_transitionFactor_continuousAt_hd
    (f : RealSmoothFunction RS) (p0 : RS.carrier)
    (htrans :
      letI := RS.topology
      letI := RS.chartedSpace
      ContinuousAt (dbarRealTransitionFactor_hd (RS := RS) p0) p0) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContinuousAt (dbarRealSectionCandidate_hd (RS := RS) f) p0 := by
  letI := RS.topology
  letI := RS.chartedSpace
  set fixedPart := dbarRealFixedPart_hd (RS := RS) f p0
  set transFactor := dbarRealTransitionFactor_hd (RS := RS) p0
  have hloc :
      dbarRealSectionCandidate_hd (RS := RS) f =ᶠ[nhds p0]
        fun p => fixedPart p * transFactor p := by
    simpa [fixedPart, transFactor] using
      dbarRealSectionCandidate_eventuallyEq_fixed_mul_transition_hd (RS := RS) f p0
  have hfixedTop :
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) fixedPart p0 := by
    simpa [fixedPart, dbarRealFixedPart_hd] using
      dbar_real_local_fixedChart_contMDiffAt_hd (RS := RS) f p0
  have hfixed : ContinuousAt fixedPart p0 := hfixedTop.continuousAt
  have htrans' : ContinuousAt transFactor p0 := by
    simpa [transFactor] using htrans
  have hmul : ContinuousAt (fun p => fixedPart p * transFactor p) p0 :=
    hfixed.mul htrans'
  exact hmul.congr_of_eventuallyEq hloc

/-- Local smoothness of the global `dbar` coefficient candidate, assuming local stabilization
of the selected chart map near the center point. -/
private theorem dbarRealSectionCandidate_contMDiffAt_of_chartAt_eventuallyEq_hd
    (f : RealSmoothFunction RS) (p0 : RS.carrier)
    (hchart :
      letI := RS.topology
      letI := RS.chartedSpace
      (fun p : RS.carrier => @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p)
        =ᶠ[nhds p0]
      (fun _ : RS.carrier => @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p0)) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
      (dbarRealSectionCandidate_hd (RS := RS) f) p0 := by
  letI := RS.topology
  letI := RS.chartedSpace
  have htrans :
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
        (dbarRealTransitionFactor_hd (RS := RS) p0) p0 :=
    dbarRealTransitionFactor_contMDiffAt_of_eventuallyEq_chart_hd (RS := RS) p0 hchart
  exact dbarRealSectionCandidate_contMDiffAt_of_transitionFactor_contMDiffAt_hd
    (RS := RS) f p0 htrans

/-- Chart-local smoothness of the `dbar` section candidate under local chart stabilization.
This is a `WithinAt` bridge for local-to-global assembly via chart neighborhoods. -/
theorem dbarRealSectionCandidate_contMDiffWithinAt_of_chartAt_eventuallyEq_hd
    (f : RealSmoothFunction RS) (p0 : RS.carrier)
    (hchart :
      letI := RS.topology
      letI := RS.chartedSpace
      (fun p : RS.carrier => @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p)
        =ᶠ[nhds p0]
      (fun _ : RS.carrier => @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p0)) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
      (dbarRealSectionCandidate_hd (RS := RS) f) (chartAt ℂ p0).source p0 := by
  letI := RS.topology
  letI := RS.chartedSpace
  exact
    (dbarRealSectionCandidate_contMDiffAt_of_chartAt_eventuallyEq_hd
      (RS := RS) f p0 hchart).contMDiffWithinAt

/-- Pointwise smoothness of the `dbar` section candidate under local chart-selection stability. -/
private theorem dbarRealSectionCandidate_contMDiffAt_of_chartAtLocallyConstant_hd
    (f : RealSmoothFunction RS) (p0 : RS.carrier)
    (hchart : Infrastructure.ChartAtLocallyConstant RS) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
      (dbarRealSectionCandidate_hd (RS := RS) f) p0 := by
  have htrans :
      letI := RS.topology
      letI := RS.chartedSpace
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
        (dbarRealTransitionFactor_hd (RS := RS) p0) p0 := by
    simpa [dbarRealTransitionFactor_hd] using
      Infrastructure.chartTransitionFactor_contMDiffAt_of_chartAtLocallyConstant
        (RS := RS) (n := smoothOrder) p0 hchart
  exact dbarRealSectionCandidate_contMDiffAt_of_transitionFactor_contMDiffAt_hd
    (RS := RS) f p0 htrans

/-- Chart-local smoothness of the `dbar` section candidate under
`ChartAtLocallyConstant`. -/
theorem dbarRealSectionCandidate_contMDiffWithinAt_of_chartAtLocallyConstant_hd
    (f : RealSmoothFunction RS) (p0 : RS.carrier)
    (hchart : Infrastructure.ChartAtLocallyConstant RS) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
      (dbarRealSectionCandidate_hd (RS := RS) f) (chartAt ℂ p0).source p0 := by
  letI := RS.topology
  letI := RS.chartedSpace
  exact
    (dbarRealSectionCandidate_contMDiffAt_of_chartAtLocallyConstant_hd
      (RS := RS) f p0 hchart).contMDiffWithinAt

/-- Global `ContMDiffOn` assembly of `dbarRealSectionCandidate_hd` under
pointwise local chart stabilization assumptions. -/
theorem dbarRealSectionCandidate_contMDiffOn_of_chartAt_eventuallyEq_hd
    (f : RealSmoothFunction RS)
    (hchart :
      letI := RS.topology
      letI := RS.chartedSpace
      ∀ p0 : RS.carrier,
        (fun p : RS.carrier => @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p)
          =ᶠ[nhds p0]
        (fun _ : RS.carrier => @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p0)) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
      (dbarRealSectionCandidate_hd (RS := RS) f) Set.univ := by
  letI := RS.topology
  letI := RS.chartedSpace
  intro p hp
  exact
    (dbarRealSectionCandidate_contMDiffAt_of_chartAt_eventuallyEq_hd
      (RS := RS) f p (hchart p)
    ).contMDiffWithinAt

/-- Global `ContMDiffOn` assembly of `dbarRealSectionCandidate_hd` under
`ChartAtLocallyConstant`. -/
theorem dbarRealSectionCandidate_contMDiffOn_of_chartAtLocallyConstant_hd
    (f : RealSmoothFunction RS)
    (hchart : Infrastructure.ChartAtLocallyConstant RS) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
      (dbarRealSectionCandidate_hd (RS := RS) f) Set.univ := by
  letI := RS.topology
  letI := RS.chartedSpace
  intro p hp
  exact
    (dbarRealSectionCandidate_contMDiffAt_of_chartAtLocallyConstant_hd
      (RS := RS) f p hchart
    ).contMDiffWithinAt

/-- Global smoothness of the chart-varying `dbar` coefficient candidate under
pointwise local stabilization of `chartAt`. -/
theorem dbar_real_hd_smooth_section_of_chartAt_eventuallyEq
    (f : RealSmoothFunction RS)
    (hchart :
      letI := RS.topology
      letI := RS.chartedSpace
      ∀ p0 : RS.carrier,
        (fun p : RS.carrier => @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p)
          =ᶠ[nhds p0]
        (fun _ : RS.carrier => @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p0)) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder (fun p : RS.carrier =>
      let e := @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p
      wirtingerDeriv_zbar (f.toFun ∘ e.symm) (e p)) := by
  letI := RS.topology
  letI := RS.chartedSpace
  simpa [dbarRealSectionCandidate_hd, contMDiffOn_univ] using
    dbarRealSectionCandidate_contMDiffOn_of_chartAt_eventuallyEq_hd
      (RS := RS) f hchart

/-- Global smoothness of `dbar_real_hd` under local chart-selection stability. -/
theorem dbar_real_hd_smooth_section_of_chartAtLocallyConstant
    (f : RealSmoothFunction RS)
    (hchart : Infrastructure.ChartAtLocallyConstant RS) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder (fun p : RS.carrier =>
      let e := @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p
      wirtingerDeriv_zbar (f.toFun ∘ e.symm) (e p)) := by
  letI := RS.topology
  letI := RS.chartedSpace
  simpa [dbarRealSectionCandidate_hd, contMDiffOn_univ] using
    dbarRealSectionCandidate_contMDiffOn_of_chartAtLocallyConstant_hd
      (RS := RS) f hchart

/-- Closed smoothness theorem for `dbar_real_hd` on the model surface `ComplexPlane`,
obtained from the chart-stabilized criterion. -/
theorem dbar_real_hd_smooth_section_complexPlane
    (f : RealSmoothFunction ComplexPlane) :
    letI := ComplexPlane.topology
    letI := ComplexPlane.chartedSpace
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder (fun p : ComplexPlane.carrier =>
      let e := @chartAt ℂ _ ComplexPlane.carrier ComplexPlane.topology ComplexPlane.chartedSpace p
      wirtingerDeriv_zbar (f.toFun ∘ e.symm) (e p)) := by
  exact dbar_real_hd_smooth_section_of_chartAtLocallyConstant
    (RS := ComplexPlane) f Infrastructure.chartAtLocallyConstant_complexPlane

/-!
Diagnostic obstruction (current selector model):
for `RiemannSphere` at center `0`, the transition-factor candidate is not even
continuous/smooth (`Infrastructure.not_contMDiffAt_chartTransitionFactor_riemannSphere_zero`).
This is about the selector-dependent transition-factor expression, not about
manifold smoothness of `RiemannSphere`.
-/

/-- On `RiemannSphere` at center `0`, the local transition-factor smoothness
statement fails for `smoothOrder` under the current explicit chart selector. -/
theorem dbarRealTransitionFactor_not_contMDiffAt_riemannSphere_zero_hd :
    letI := RiemannSphere.topology
    letI := RiemannSphere.chartedSpace
    ¬ ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
      (dbarRealTransitionFactor_hd (RS := RiemannSphere) (((0 : ℂ) : OnePoint ℂ)))
      (((0 : ℂ) : OnePoint ℂ)) := by
  letI := RiemannSphere.topology
  letI := RiemannSphere.chartedSpace
  simpa [dbarRealTransitionFactor_hd] using
    Infrastructure.not_contMDiffAt_chartTransitionFactor_riemannSphere_zero (n := smoothOrder)

/-- Global diagnostic consequence on `RiemannSphere`:
the moving-selector transition factor is not smooth at every point. -/
theorem dbarRealTransitionFactor_not_forall_contMDiffAt_riemannSphere_hd :
    letI := RiemannSphere.topology
    letI := RiemannSphere.chartedSpace
    ¬ ∀ p0 : RiemannSphere.carrier,
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
        (dbarRealTransitionFactor_hd (RS := RiemannSphere) p0) p0 := by
  letI := RiemannSphere.topology
  letI := RiemannSphere.chartedSpace
  intro hall
  exact dbarRealTransitionFactor_not_contMDiffAt_riemannSphere_zero_hd
    (hall (((0 : ℂ) : OnePoint ℂ)))

/-- Remaining hard local bridge: smoothness of the chart-transition Jacobian factor.
The issue is the moving chart choice `p ↦ chartAt ℂ p` inside the derivative point
of `chartTransition p0 p` (a selector-based transition helper, not a canonical
center-only map), which is not yet bridged to a chart-free smooth object.
The unconditional statement is obstructed on `RiemannSphere` at `0`
(`dbarRealTransitionFactor_not_contMDiffAt_riemannSphere_zero_hd`). -/
private theorem dbarRealTransitionFactor_contMDiffAt_hd (p0 : RS.carrier) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
      (dbarRealTransitionFactor_hd (RS := RS) p0) p0 := by
  sorry

/-- Pointwise smoothness of the global `dbar` section candidate. -/
private theorem dbarRealSectionCandidate_contMDiffAt_hd
    (f : RealSmoothFunction RS) (p0 : RS.carrier) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
      (dbarRealSectionCandidate_hd (RS := RS) f) p0 := by
  letI := RS.topology
  letI := RS.chartedSpace
  have htrans :
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
        (dbarRealTransitionFactor_hd (RS := RS) p0) p0 :=
    dbarRealTransitionFactor_contMDiffAt_hd (RS := RS) p0
  exact dbarRealSectionCandidate_contMDiffAt_of_transitionFactor_contMDiffAt_hd
    (RS := RS) f p0 htrans

theorem dbar_real_hd_smooth_section (f : RealSmoothFunction RS) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder (fun p : RS.carrier =>
      let e := @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p
      wirtingerDeriv_zbar (f.toFun ∘ e.symm) (e p)) := by
  letI := RS.topology
  letI := RS.chartedSpace
  intro p0
  simpa [dbarRealSectionCandidate_hd] using
    dbarRealSectionCandidate_contMDiffAt_hd (RS := RS) f p0

/-- The ∂̄ operator on ℝ-smooth functions: ∂̄f = (∂f/∂z̄) dz̄.
    Duplicated from DolbeaultCohomology.lean to avoid circular imports
    (DolbeaultCohomology imports HodgeDecomposition). -/
noncomputable def dbar_real_hd (f : RealSmoothFunction RS) : Form_01 RS where
  toSection := fun p =>
    letI := RS.topology
    letI := RS.chartedSpace
    let e := @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p
    wirtingerDeriv_zbar (f.toFun ∘ e.symm) (e p)
  smooth' := dbar_real_hd_smooth_section f

/-- The ∂ operator on ℝ-smooth functions, defined from ∂̄ by conjugation:
    ∂f = overline{ ∂̄(overline{f}) }.
    This keeps the definition rigorous without introducing a second chart-varying
    smoothness obligation parallel to `dbar_real_hd_smooth_section`. -/
noncomputable def del_real (f : RealSmoothFunction RS) : Form_10 RS :=
  (dbar_real_hd f.conj).conj

/-!
## Hodge decomposition statements (using ∂̄ on ℝ-smooth functions)

These are placed here so they can refer to `dbar_real_hd` and `del_real`.
-/

/-- Hodge decomposition for (0,1)-forms on a compact Riemann surface:
    Every (0,1)-form decomposes as ω = ω_harm + ∂̄f
    where ω_harm ∈ H^{0,1} and f is an ℝ-smooth function. -/
theorem hodge_decomposition_01 (CRS : CompactRiemannSurface) (ω : Form_01 CRS.toRiemannSurface) :
    ∃ (ω_harm : Form_01 CRS.toRiemannSurface) (f : RealSmoothFunction CRS.toRiemannSurface),
      ω_harm.IsHarmonic ∧ ω = ω_harm + dbar_real_hd f := by
  sorry

/-- Exact-harmonic `(0,1)` vanishing on compact Riemann surfaces:
if `∂̄f` is harmonic, then `∂̄f = 0`.

This packages the core analytic input (Hodge/elliptic theory) reused by
downstream Dolbeault/de Rham bridge statements. -/
theorem exact_harmonic01_vanishes (CRS : CompactRiemannSurface) :
    ∀ f : RealSmoothFunction CRS.toRiemannSurface,
      (dbar_real_hd f).IsHarmonic →
        dbar_real_hd f = 0 := by
  sorry

/-- Common-potential compatibility for closed componentwise-exact pairs.

If a closed pair `(ω10, ω01)` has separately exact components
`ω10 = ∂f10` and `ω01 = ∂̄f01`, then there is one potential `f` with
`ω10 = ∂f` and `ω01 = ∂̄f`. This is the analytic gauge-compatibility bridge
used by the de Rham/Hodge surjectivity package. -/
theorem closed_exactPair_commonPotential (CRS : CompactRiemannSurface) :
    ∀ (ω10 : Form_10 CRS.toRiemannSurface) (ω01 : Form_01 CRS.toRiemannSurface)
      (f10 f01 : RealSmoothFunction CRS.toRiemannSurface),
      dbar_10 ω10 + del_01 ω01 = 0 →
      ω10 = del_real f10 →
      ω01 = dbar_real_hd f01 →
      ∃ f : RealSmoothFunction CRS.toRiemannSurface,
        ω10 = del_real f ∧ ω01 = dbar_real_hd f := by
  sorry

/-- Hodge decomposition for (1,0)-forms:
    Every (1,0)-form decomposes as ω = ω_harm + ∂f
    where ω_harm ∈ H^{1,0}. -/
theorem hodge_decomposition_10 (CRS : CompactRiemannSurface) (ω : Form_10 CRS.toRiemannSurface) :
    ∃ (ω_harm : Form_10 CRS.toRiemannSurface) (f : RealSmoothFunction CRS.toRiemannSurface),
      ω_harm.IsHarmonic ∧ ω = ω_harm + del_real f := by
  obtain ⟨η, f, hηharm, hηdecomp⟩ := hodge_decomposition_01 CRS ω.conj
  obtain ⟨ωh, hωh_harm, hηeq⟩ := hηharm
  refine ⟨ωh, f.conj, hωh_harm, ?_⟩
  have hconj :
      ω = η.conj + (dbar_real_hd f).conj := by
    have hconj_raw := congrArg Form_01.conj hηdecomp
    simpa [Form_10.conj_conj, Form_01.conj_add] using hconj_raw
  have hηconj : η.conj = ωh := by
    rw [hηeq, Form_10.conj_conj]
  have hdel : (dbar_real_hd f).conj = del_real f.conj := by
    unfold del_real
    rw [RealSmoothFunction.conj_conj]
  calc
    ω = η.conj + (dbar_real_hd f).conj := hconj
    _ = ωh + del_real f.conj := by rw [hηconj, hdel]

/-!
## Linearity of del_01, del_real, dbar_real_hd

These operators are all defined via Wirtinger derivatives composed with charts.
Their linearity follows from linearity of the Wirtinger derivatives.
-/

/-- Helper: Form_01 sections composed with chart inverse are ℝ-differentiable. -/
private theorem form01_chart_differentiableAt (ω : Form_01 RS) (p : RS.carrier) :
    letI := RS.topology; letI := RS.chartedSpace
    DifferentiableAt ℝ (ω.toSection ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) := by
  letI := RS.topology; letI := RS.chartedSpace
  haveI : IsManifold 𝓘(ℂ, ℂ) ⊤ RS.carrier := RS.isManifold
  haveI : IsManifold 𝓘(ℝ, ℂ) ⊤ RS.carrier := isManifold_real_of_complex
  exact Infrastructure.differentiableAt_chart_comp_smoothOrder ω.smooth' p

/-- Helper: RealSmoothFunction values composed with chart inverse are ℝ-differentiable. -/
private theorem realSmooth_chart_differentiableAt_hd (f : RealSmoothFunction RS) (p : RS.carrier) :
    letI := RS.topology; letI := RS.chartedSpace
    DifferentiableAt ℝ (f.toFun ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) := by
  letI := RS.topology; letI := RS.chartedSpace
  haveI := RS.isManifold
  haveI : IsManifold 𝓘(ℝ, ℂ) ⊤ RS.carrier := isManifold_real_of_complex
  exact Infrastructure.differentiableAt_chart_comp_smoothOrder f.smooth' p

-- ∂ on (0,1)-forms: linearity

theorem del_01_add (ω₁ ω₂ : Form_01 RS) :
    del_01 (ω₁ + ω₂) = del_01 ω₁ + del_01 ω₂ := by
  letI := RS.topology; letI := RS.chartedSpace
  apply Form_11.ext; funext p
  simp only [Form_11.add_toSection]
  show Infrastructure.wirtingerDeriv ((ω₁ + ω₂).toSection ∘
    (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm)
    ((@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p) p) =
    Infrastructure.wirtingerDeriv (ω₁.toSection ∘
      (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm)
      ((@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p) p) +
    Infrastructure.wirtingerDeriv (ω₂.toSection ∘
      (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm)
      ((@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p) p)
  have hfun_eq : (ω₁ + ω₂).toSection ∘
      (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm =
      (ω₁.toSection ∘ (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm) +
      (ω₂.toSection ∘ (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm) := by
    ext z; simp only [Function.comp_apply, Form_01.add_toSection, Pi.add_apply]
  rw [hfun_eq]
  exact Infrastructure.wirtingerDeriv_add (form01_chart_differentiableAt ω₁ p)
    (form01_chart_differentiableAt ω₂ p)

theorem del_01_smul (c : ℂ) (ω : Form_01 RS) :
    del_01 (c • ω) = c • del_01 ω := by
  letI := RS.topology; letI := RS.chartedSpace
  apply Form_11.ext; funext p
  simp only [Form_11.smul_toSection]
  show Infrastructure.wirtingerDeriv ((c • ω).toSection ∘
    (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm)
    ((@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p) p) =
    c * Infrastructure.wirtingerDeriv (ω.toSection ∘
      (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm)
      ((@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p) p)
  have hfun_eq : (c • ω).toSection ∘
      (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm =
      c • (ω.toSection ∘ (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm) := by
    ext z; simp only [Function.comp_apply, Form_01.smul_toSection, Pi.smul_apply, smul_eq_mul]
  rw [hfun_eq]
  exact Infrastructure.wirtingerDeriv_const_smul c (form01_chart_differentiableAt ω p)

/-- Conjugation compatibility: `∂̄(ω̄) = -conj(∂ω)` for `(0,1)`-forms `ω`. -/
theorem dbar_10_conj (ω : Form_01 RS) :
    dbar_10 ω.conj = -(del_01 ω).conj := by
  letI := RS.topology; letI := RS.chartedSpace
  apply Form_11.ext
  funext p
  let e := @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p
  let g : ℂ → ℂ := ω.toSection ∘ e.symm
  have hdiffR : DifferentiableAt ℝ g (e p) := by
    simpa [g, e] using form01_chart_differentiableAt (RS := RS) ω p
  have hconj :
      Infrastructure.wirtingerDerivBar (starRingEnd ℂ ∘ g) (e p) =
        starRingEnd ℂ (Infrastructure.wirtingerDeriv g (e p)) :=
    Infrastructure.wirtingerDerivBar_comp_conj_real hdiffR
  have hcomp : ((ω.conj).toSection ∘ e.symm) = (starRingEnd ℂ ∘ g) := by
    ext z
    simp [g]
  change -(Infrastructure.wirtingerDerivBar ((ω.conj).toSection ∘ e.symm) (e p)) =
    (-((del_01 ω).conj)).toSection p
  rw [hcomp, hconj]
  simp [del_01, g, e, wirtingerDeriv_z]

/-- Conjugation compatibility: `∂(η̄) = -conj(∂̄η)` for `(1,0)`-forms `η`. -/
theorem del_01_conj (η : Form_10 RS) :
    del_01 η.conj = -(dbar_10 η).conj := by
  letI := RS.topology; letI := RS.chartedSpace
  apply Form_11.ext
  funext p
  let e := @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p
  let g : ℂ → ℂ := η.toSection ∘ e.symm
  have hdiffR : DifferentiableAt ℝ g (e p) := by
    simpa [g, e] using form10_chart_differentiableAt (RS := RS) η p
  have hconj :
      Infrastructure.wirtingerDeriv (starRingEnd ℂ ∘ g) (e p) =
        starRingEnd ℂ (Infrastructure.wirtingerDerivBar g (e p)) :=
    Infrastructure.wirtingerDeriv_comp_conj_real hdiffR
  have hcomp : ((η.conj).toSection ∘ e.symm) = (starRingEnd ℂ ∘ g) := by
    ext z
    simp [g]
  change Infrastructure.wirtingerDeriv ((η.conj).toSection ∘ e.symm) (e p) =
    (-((dbar_10 η).conj)).toSection p
  rw [hcomp, hconj]
  simp [dbar_10, g, e, wirtingerDeriv_zbar]

/-- Converse harmonicity criterion for `(0,1)`-forms:
`∂ω = 0` implies `ω` is harmonic. -/
theorem isHarmonic01_of_del_01_eq_zero {ω : Form_01 RS} (hω : del_01 ω = 0) :
    ω.IsHarmonic := by
  refine ⟨ω.conj, ?_, by simpa using (Form_01.conj_conj ω).symm⟩
  unfold Form_10.IsHarmonic
  simp [dbar_10_conj, hω]

/-- Harmonic `(0,1)`-forms satisfy `∂ω = 0`. -/
theorem del_01_eq_zero_of_isHarmonic01 {ω : Form_01 RS} (hω : ω.IsHarmonic) :
    del_01 ω = 0 := by
  rcases hω with ⟨η, hη, rfl⟩
  unfold Form_10.IsHarmonic at hη
  letI := RS.topology
  letI := RS.chartedSpace
  haveI : IsManifold 𝓘(ℂ, ℂ) ⊤ RS.carrier := RS.isManifold
  haveI : IsManifold 𝓘(ℝ, ℂ) ⊤ RS.carrier := isManifold_real_of_complex
  apply Form_11.ext
  funext p
  let e := @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p
  let g : ℂ → ℂ := η.toSection ∘ e.symm
  have hdiffR : DifferentiableAt ℝ g (e p) := by
    simpa [g, e] using Infrastructure.differentiableAt_chart_comp_smoothOrder η.smooth' p
  have hnegBar : -(wirtingerDeriv_zbar g (e p)) = 0 := by
    have hp := congrArg (fun τ : Form_11 RS => τ.toSection p) hη
    simpa [dbar_10, g, e] using hp
  have hbar0 : wirtingerDeriv_zbar g (e p) = 0 := by
    simpa using neg_eq_zero.mp hnegBar
  have hconj_swap :
      Infrastructure.wirtingerDeriv (starRingEnd ℂ ∘ g) (e p) =
        starRingEnd ℂ (wirtingerDeriv_zbar g (e p)) :=
    Infrastructure.wirtingerDeriv_comp_conj_real hdiffR
  have hbar0' : Infrastructure.wirtingerDerivBar g (e p) = 0 := by
    simpa [wirtingerDeriv_zbar] using hbar0
  have hconj :
      Infrastructure.wirtingerDeriv (starRingEnd ℂ ∘ g) (e p) = 0 := by
    have hswap' :
        Infrastructure.wirtingerDeriv (starRingEnd ℂ ∘ g) (e p) =
          starRingEnd ℂ (Infrastructure.wirtingerDerivBar g (e p)) := by
      simpa [wirtingerDeriv_zbar] using hconj_swap
    simpa [hbar0'] using hswap'
  change Infrastructure.wirtingerDeriv ((η.conj).toSection ∘ e.symm) (e p) = 0
  have hcomp : ((η.conj).toSection ∘ e.symm) = (starRingEnd ℂ ∘ g) := by
    ext z
    simp [g]
  rw [hcomp]
  exact hconj

/-- Characterization of harmonic `(0,1)`-forms by `∂`-closedness. -/
theorem isHarmonic01_iff_del_01_eq_zero (ω : Form_01 RS) :
    ω.IsHarmonic ↔ del_01 ω = 0 := by
  constructor
  · exact del_01_eq_zero_of_isHarmonic01
  · exact isHarmonic01_of_del_01_eq_zero

private theorem dbar_10_zero : dbar_10 (0 : Form_10 RS) = 0 := by
  have : (0 : Form_10 RS) = (0 : ℂ) • (0 : Form_10 RS) := by simp
  rw [this, dbar_10_smul, zero_smul]

private theorem del_01_zero : del_01 (0 : Form_01 RS) = 0 := by
  have : (0 : Form_01 RS) = (0 : ℂ) • (0 : Form_01 RS) := by simp
  rw [this, del_01_smul, zero_smul]

-- ∂̄ on ℝ-smooth functions (local copy): linearity

theorem dbar_real_hd_add (f g : RealSmoothFunction RS) :
    dbar_real_hd (f + g) = dbar_real_hd f + dbar_real_hd g := by
  letI := RS.topology; letI := RS.chartedSpace
  apply Form_01.ext; funext p
  simp only [Form_01.add_toSection]
  show Infrastructure.wirtingerDerivBar ((f + g).toFun ∘
    (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm)
    ((@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p) p) =
    Infrastructure.wirtingerDerivBar (f.toFun ∘
      (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm)
      ((@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p) p) +
    Infrastructure.wirtingerDerivBar (g.toFun ∘
      (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm)
      ((@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p) p)
  have hfun_eq : (f + g).toFun ∘
      (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm =
      (f.toFun ∘ (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm) +
      (g.toFun ∘ (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm) := by
    ext z; simp only [Function.comp_apply, RealSmoothFunction.add_toFun, Pi.add_apply]
  rw [hfun_eq]
  exact Infrastructure.wirtingerDerivBar_add (realSmooth_chart_differentiableAt_hd f p)
    (realSmooth_chart_differentiableAt_hd g p)

theorem dbar_real_hd_zero : dbar_real_hd (0 : RealSmoothFunction RS) = 0 := by
  letI := RS.topology; letI := RS.chartedSpace
  apply Form_01.ext; funext p
  simp only [Form_01.zero_toSection]
  show Infrastructure.wirtingerDerivBar ((0 : RealSmoothFunction RS).toFun ∘
    (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm)
    ((@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p) p) = 0
  have hfun_eq : (0 : RealSmoothFunction RS).toFun ∘
      (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm =
      fun _ => 0 := by
    ext z; simp only [Function.comp_apply, RealSmoothFunction.zero_toFun]
  rw [hfun_eq]
  exact Infrastructure.wirtingerDerivBar_const 0

theorem dbar_real_hd_const_mul (c : ℂ) (f : RealSmoothFunction RS) :
    dbar_real_hd (RealSmoothFunction.const c * f) = c • dbar_real_hd f := by
  letI := RS.topology; letI := RS.chartedSpace
  apply Form_01.ext; funext p
  simp only [Form_01.smul_toSection]
  show Infrastructure.wirtingerDerivBar ((RealSmoothFunction.const c * f).toFun ∘
    (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm)
    ((@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p) p) =
    c * Infrastructure.wirtingerDerivBar (f.toFun ∘
      (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm)
      ((@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p) p)
  have hfun_eq : (RealSmoothFunction.const c * f).toFun ∘
      (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm =
      c • (f.toFun ∘ (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm) := by
    ext z
    simp only [Function.comp_apply, RealSmoothFunction.mul_toFun, Pi.smul_apply,
      smul_eq_mul, RealSmoothFunction.const]
  rw [hfun_eq]
  exact Infrastructure.wirtingerDerivBar_const_smul c (realSmooth_chart_differentiableAt_hd f p)

theorem dbar_real_hd_smul (c : ℂ) (f : RealSmoothFunction RS) :
    dbar_real_hd (c • f) = c • dbar_real_hd f := by
  simpa [RealSmoothFunction.smul_def] using dbar_real_hd_const_mul (RS := RS) c f

/-- Mixed identity `∂̄∂f + ∂∂̄f = 0` under locally constant chart selection.

This theorem isolates the selector-dependent obstruction:
the proof uses local stabilization of `chartAt` to reduce both operators to a
fixed-chart local coefficient, then applies mixed-Wirtinger commutativity. -/
theorem dbar_10_del_real_add_del_01_dbar_real_hd_eq_zero_of_chartAtLocallyConstant
    (hchart : Infrastructure.ChartAtLocallyConstant RS)
    (f : RealSmoothFunction RS) :
    dbar_10 (del_real f) + del_01 (dbar_real_hd f) = 0 := by
  apply Form_11.ext
  funext p
  letI := RS.topology
  letI := RS.chartedSpace
  let e := @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p
  have he_source : p ∈ e.source := by
    simpa [e] using (mem_chart_source ℂ p)
  have he_target : e p ∈ e.target := by
    simpa [e] using (mem_chart_target ℂ p)
  have hchartp :
      (fun q : RS.carrier => @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace q)
        =ᶠ[nhds p]
      (fun _ : RS.carrier => @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p) := hchart p
  have hchartz :
      (fun z : ℂ => @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace (e.symm z))
        =ᶠ[nhds (e p)]
      (fun _ : ℂ => e) := by
    have hcont_symm : ContinuousAt e.symm (e p) := by
      simpa [e] using (e.continuousAt_symm he_target)
    have hsymm_eq : e.symm (e p) = p := by
      simpa [e] using (e.left_inv he_source)
    have hto_p : Filter.Tendsto e.symm (nhds (e p)) (nhds p) := by
      simpa [hsymm_eq] using hcont_symm.tendsto
    exact hchartp.comp_tendsto hto_p
  have hcdiffOn :
      ContDiffOn ℝ ((2 : ℕ∞) : WithTop ℕ∞) (f.toFun ∘ e.symm) e.target := by
    simpa [e] using
      (RealSmoothFunction.contDiffOn_comp_chart_symm (f := f) (p0 := p) (n := (2 : ℕ∞)))
  have hsec_fixed :
      ((dbar_real_hd f).toSection ∘ e.symm) =ᶠ[nhds (e p)]
        (fun z => wirtingerDeriv_zbar (f.toFun ∘ e.symm) z) := by
    filter_upwards [hchartz, e.open_target.mem_nhds he_target] with z hzchart hzt
    have hzid : e (e.symm z) = z := e.right_inv hzt
    simp [dbar_real_hd, hzchart, hzid]
  have hdel01_eq :
      Infrastructure.wirtingerDeriv (((dbar_real_hd f).toSection) ∘ e.symm) (e p) =
        Infrastructure.wirtingerDeriv (fun z => wirtingerDeriv_zbar (f.toFun ∘ e.symm) z) (e p) :=
    Infrastructure.wirtingerDeriv_congr_of_eventuallyEq hsec_fixed
  have hdel_fixed :
      ((del_real f).toSection ∘ e.symm) =ᶠ[nhds (e p)]
        (fun z => wirtingerDeriv_z (f.toFun ∘ e.symm) z) := by
    filter_upwards [hchartz, e.open_target.mem_nhds he_target] with z hzchart hzt
    have hzid : e (e.symm z) = z := e.right_inv hzt
    have hdiffAt : DifferentiableAt ℝ (f.toFun ∘ e.symm) z := by
      have hcdiffAt : ContDiffAt ℝ ((2 : ℕ∞) : WithTop ℕ∞) (f.toFun ∘ e.symm) z :=
        hcdiffOn.contDiffAt (e.open_target.mem_nhds hzt)
      exact hcdiffAt.differentiableAt (by simp)
    have hconj_bar :
        Infrastructure.wirtingerDerivBar (starRingEnd ℂ ∘ (f.toFun ∘ e.symm)) z =
          starRingEnd ℂ (Infrastructure.wirtingerDeriv (f.toFun ∘ e.symm) z) :=
      Infrastructure.wirtingerDerivBar_comp_conj_real hdiffAt
    have hcomp : f.conj.toFun ∘ e.symm = starRingEnd ℂ ∘ (f.toFun ∘ e.symm) := by
      ext w
      simp [RealSmoothFunction.conj_toFun]
    have hbar_conj :
        Infrastructure.wirtingerDerivBar (f.conj.toFun ∘ e.symm) z =
          starRingEnd ℂ (Infrastructure.wirtingerDeriv (f.toFun ∘ e.symm) z) := by
      rw [hcomp]
      exact hconj_bar
    have hstar_hbar :
        (starRingEnd ℂ) (wirtingerDeriv_zbar (f.conj.toFun ∘ e.symm) z) =
          wirtingerDeriv_z (f.toFun ∘ e.symm) z := by
      have hstar := congrArg (starRingEnd ℂ) hbar_conj
      simpa [wirtingerDeriv_zbar, wirtingerDeriv_z] using hstar
    simpa [del_real, dbar_real_hd, hzchart, hzid] using hstar_hbar
  have hdbar_eq :
      Infrastructure.wirtingerDerivBar (((del_real f).toSection) ∘ e.symm) (e p) =
        Infrastructure.wirtingerDerivBar (fun z => wirtingerDeriv_z (f.toFun ∘ e.symm) z) (e p) :=
    Infrastructure.wirtingerDerivBar_congr_of_eventuallyEq hdel_fixed
  have hcdiffAt :
      ContDiffAt ℝ ((2 : ℕ∞) : WithTop ℕ∞) (f.toFun ∘ e.symm) (e p) :=
    hcdiffOn.contDiffAt (e.open_target.mem_nhds he_target)
  have hmixed :
      Infrastructure.wirtingerDeriv (Infrastructure.wirtingerDerivBar (f.toFun ∘ e.symm)) (e p) =
      Infrastructure.wirtingerDerivBar (Infrastructure.wirtingerDeriv (f.toFun ∘ e.symm)) (e p) :=
    Infrastructure.laplacian_eq_four_wirtinger_mixed_at (f := f.toFun ∘ e.symm) (z := e p) hcdiffAt
  change -(Infrastructure.wirtingerDerivBar ((del_real f).toSection ∘ e.symm) (e p)) +
      Infrastructure.wirtingerDeriv ((dbar_real_hd f).toSection ∘ e.symm) (e p) = 0
  rw [hdbar_eq, hdel01_eq]
  simpa [wirtingerDeriv_zbar, wirtingerDeriv_z, hmixed] using sub_eq_zero.mpr hmixed

/-- Chart-stabilized mixed identity specialized to `ComplexPlane`. -/
theorem dbar_10_del_real_add_del_01_dbar_real_hd_eq_zero_complexPlane
    (f : RealSmoothFunction ComplexPlane) :
    dbar_10 (del_real f) + del_01 (dbar_real_hd f) = 0 := by
  exact dbar_10_del_real_add_del_01_dbar_real_hd_eq_zero_of_chartAtLocallyConstant
    (RS := ComplexPlane) Infrastructure.chartAtLocallyConstant_complexPlane f


end RiemannSurfaces.Analytic
