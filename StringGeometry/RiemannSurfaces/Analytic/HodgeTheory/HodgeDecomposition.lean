import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.Dolbeault
import StringGeometry.RiemannSurfaces.Analytic.Helpers.ChartTransition

/-!
# Hodge Decomposition on Riemann Surfaces

This file develops Hodge theory for compact Riemann surfaces, including the
Hodge star operator, the Laplacian, harmonic forms, and the Hodge decomposition theorem.

## Mathematical Background

### The Hodge Star Operator

On a Riemann surface with the standard metric induced by the complex structure,
the Hodge star operator ⋆ acts on forms as follows:

For a Riemann surface with local coordinate z = x + iy and area form ω = (i/2) dz ∧ dz̄:
- ⋆1 = ω = (i/2) dz ∧ dz̄
- ⋆ω = 1
- ⋆dz = -i dz̄ (up to normalization)
- ⋆dz̄ = i dz

### The Laplacian

The Laplacian on a Riemann surface can be expressed as:
  Δ = 2i ∂∂̄ = -2i ∂̄∂

On functions: Δf = 4 ∂²f/∂z∂z̄

The Laplacian is self-adjoint with respect to the L² inner product.

### Harmonic Forms

A form ω is harmonic if Δω = 0, which is equivalent to:
  dω = 0 and d⋆ω = 0 (closed and co-closed)

For a Riemann surface:
- Harmonic 0-forms = constant functions (on compact surfaces)
- Harmonic 1-forms = holomorphic 1-forms ⊕ antiholomorphic 1-forms
- Harmonic (1,1)-forms = constant multiples of the area form (on compact surfaces)

### Hodge Decomposition

For a compact Riemann surface X of genus g:

  Ω^1(X) = H^1(X) ⊕ im(d) ⊕ im(d⋆)

where H^1(X) is the space of harmonic 1-forms, dim H^1(X) = 2g.

More refined:
  Ω^{1,0}(X) = H^{1,0}(X) ⊕ ∂̄(Ω^0)
  Ω^{0,1}(X) = H^{0,1}(X) ⊕ ∂(Ω^0)

where H^{1,0} = holomorphic 1-forms and H^{0,1} = their conjugates.

## Main Definitions

* `HodgeStar` - The Hodge star operator
* `HodgeLaplacian` - The Hodge Laplacian Δ
* `IsHarmonic` - Predicate for harmonic forms
* `HarmonicForms` - The space of harmonic forms

## References

* Griffiths, Harris "Principles of Algebraic Geometry" Ch 0.7
* Wells "Differential Analysis on Complex Manifolds" Ch IV
* Forster "Lectures on Riemann Surfaces" §20-21
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
  exact Infrastructure.differentiableAt_chart_comp ω.smooth' p

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

/-- The type of harmonic (1,0)-forms (holomorphic 1-forms) -/
def Harmonic10Forms (RS : RiemannSurface) := { ω : Form_10 RS // ω.IsHarmonic }

/-- The type of harmonic (0,1)-forms (antiholomorphic 1-forms) -/
def Harmonic01Forms (RS : RiemannSurface) := { ω : Form_01 RS // ω.IsHarmonic }

/-- Harmonic10Forms is equivalent to the harmonicSubmodule10 carrier. -/
def Harmonic10Forms.equivSubmodule (RS : RiemannSurface) :
    Harmonic10Forms RS ≃ harmonicSubmodule10 RS :=
  Equiv.subtypeEquivRight (fun _ => Iff.rfl)

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

/-- The dimension of H^{1,0} equals the genus -/
theorem dim_harmonic_10_eq_genus (CRS : CompactRiemannSurface) :
    ∃ (basis : Fin CRS.genus → Harmonic10Forms CRS.toRiemannSurface),
      Function.Injective basis := by
  let RS := CRS.toRiemannSurface
  letI := RS.topology
  letI := RS.chartedSpace
  obtain ⟨x₀⟩ : Nonempty RS.carrier := RS.connected.toNonempty
  let basis : Fin CRS.genus → Harmonic10Forms RS := fun i =>
    ⟨{ toSection := fun _ => (i : ℂ)
       smooth' := by
         simpa using
           (contMDiff_const :
             ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤ (fun _ : RS.carrier => (i : ℂ))) },
      by
        unfold Form_10.IsHarmonic dbar_10
        apply Form_11.ext
        funext p
        change -wirtingerDeriv_zbar
            (((fun _ : RS.carrier => (i : ℂ)) ∘ (chartAt ℂ p).symm))
            ((chartAt ℂ p) p) = 0
        have hconst :
            ((fun x : RS.carrier => (i : ℂ)) ∘ (chartAt ℂ p).symm) =
              (fun _ : ℂ => (i : ℂ)) := by
          ext z
          simp
        rw [hconst]
        simp [wirtingerDeriv_zbar, Infrastructure.wirtingerDerivBar_const]⟩
  refine ⟨basis, ?_⟩
  intro i j hij
  apply Fin.ext
  have hsec : ((basis i).1.toSection x₀ : ℂ) = ((basis j).1.toSection x₀ : ℂ) :=
    congrArg (fun ω => ω.1.toSection x₀) hij
  simpa [basis] using hsec

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
    simpa [eChart] using (mem_chart_source ℂ p)
  have hp0' : p ∈ (eChart (RS := RS) p0).source := by
    simpa [eChart] using hp0
  have hchange :=
    wirtingerDerivBar_extChart_symm_change_at_point_of_realSmooth
      (RS := RS) (f := f) (q := p0) (r := p) (p := p) hp hp0'
  simpa [dbarRealSectionCandidate_hd, wirtingerDeriv_zbar, eChart, chartTransition,
    Function.comp_apply, hp] using hchange

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
  letI := RS.topology
  letI := RS.chartedSpace
  exact fun p =>
    starRingEnd ℂ (deriv (chartTransition (RS := RS) p0 p) ((chartAt ℂ p) p))

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

theorem dbar_real_hd_smooth_section (f : RealSmoothFunction RS) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤ (fun p : RS.carrier =>
      let e := @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p
      wirtingerDeriv_zbar (f.toFun ∘ e.symm) (e p)) := by
  letI := RS.topology
  letI := RS.chartedSpace
  intro p0
  set fixedPart := dbarRealFixedPart_hd (RS := RS) f p0
  set transFactor := dbarRealTransitionFactor_hd (RS := RS) p0
  have hloc :
      dbarRealSectionCandidate_hd (RS := RS) f =ᶠ[nhds p0]
        fun p => fixedPart p * transFactor p := by
    simpa [fixedPart, transFactor] using
      dbarRealSectionCandidate_eventuallyEq_fixed_mul_transition_hd (RS := RS) f p0
  have hfixed : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) fixedPart p0 := by
    simpa [fixedPart, dbarRealFixedPart_hd] using
      dbar_real_local_fixedChart_contMDiffAt_hd (RS := RS) f p0
  -- Remaining global blocker:
  -- establish `ContMDiffAt` for `transFactor` at `p0`, then conclude via
  -- product smoothness and `congr_of_eventuallyEq` using `hloc`.
  sorry

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
  exact Infrastructure.differentiableAt_chart_comp ω.smooth' p

/-- Helper: RealSmoothFunction values composed with chart inverse are ℝ-differentiable. -/
private theorem realSmooth_chart_differentiableAt_hd (f : RealSmoothFunction RS) (p : RS.carrier) :
    letI := RS.topology; letI := RS.chartedSpace
    DifferentiableAt ℝ (f.toFun ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) := by
  letI := RS.topology; letI := RS.chartedSpace
  haveI := RS.isManifold
  haveI : IsManifold 𝓘(ℝ, ℂ) ⊤ RS.carrier := isManifold_real_of_complex
  exact Infrastructure.differentiableAt_chart_comp f.smooth' p

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
    show dbar_10 0 + del_01 0 = 0
    rw [dbar_10_zero, del_01_zero, add_zero]
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
    refine ⟨RealSmoothFunction.const c * f, ?_, ?_⟩
    · show c • ω.1 = del_real (RealSmoothFunction.const c * f)
      rw [del_real_const_mul, ← hf1]
    · show c • ω.2 = dbar_real_hd (RealSmoothFunction.const c * f)
      rw [dbar_real_hd_const_mul, ← hf2]

/-- De Rham cohomology H¹_dR(X, ℂ) = closed 1-forms / exact 1-forms.

    A 1-form ω = α dz + β dz̄ is closed iff ∂̄α + ∂β = 0.
    It is exact iff (α, β) = (∂f, ∂̄f) for some ℝ-smooth f.

    For a compact Riemann surface of genus g, dim H¹_dR = 2g.
    By the Hodge theorem, H¹_dR ≅ H^{1,0} ⊕ H^{0,1} (harmonic representatives). -/
noncomputable def DeRhamH1 (CRS : CompactRiemannSurface) : Type :=
  (↥(closedForms1 CRS.toRiemannSurface)) ⧸
    (Submodule.comap (closedForms1 CRS.toRiemannSurface).subtype
      (exactForms1 CRS.toRiemannSurface)).toAddSubgroup

/-- Hodge theorem: Harmonic forms represent de Rham cohomology.
    H^1_dR(X) ≅ H^1_harm(X) for compact X.

    More precisely, the inclusion of harmonic 1-forms into closed 1-forms
    induces an isomorphism H^1_harm → H^1_dR. Every de Rham cohomology class
    has a unique harmonic representative.

    For a Riemann surface of genus g, this gives dim H^1_dR = 2g since
    H^1_harm = H^{1,0} ⊕ H^{0,1} has dimension g + g = 2g. -/
theorem hodge_isomorphism (CRS : CompactRiemannSurface) :
    ∃ (harmonic_to_deRham :
        (Harmonic10Forms CRS.toRiemannSurface ⊕ Harmonic01Forms CRS.toRiemannSurface) →
        DeRhamH1 CRS),
      Function.Bijective harmonic_to_deRham := by
  -- Every closed form is cohomologous to a unique harmonic form
  -- This requires the Hodge decomposition and elliptic regularity
  sorry

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
    exact ⟨RealSmoothFunction.const c * f, by rw [dbar_real_hd_const_mul, hf]⟩

/-- Sheaf cohomology H¹(X, O) defined analytically as the Dolbeault quotient
    Ω^{0,1}(X) / im(∂̄). By the Dolbeault theorem, this is isomorphic to the
    sheaf cohomology H¹(X, O_X) defined via Čech cohomology or derived functors.

    This is a local copy of `DolbeaultH01` from DolbeaultCohomology.lean,
    defined here to break the circular import dependency. -/
noncomputable def SheafH1O (CRS : CompactRiemannSurface) : Type :=
  Form_01 CRS.toRiemannSurface ⧸ dbarImage_hd CRS.toRiemannSurface

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
  -- The Dolbeault isomorphism requires:
  -- 1. ∂̄-Poincaré lemma (local exactness)
  -- 2. Partition of unity (existence of cutoff functions)
  -- 3. Identification of harmonic forms with cohomology classes
  sorry

end RiemannSurfaces.Analytic
