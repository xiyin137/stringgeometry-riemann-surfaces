import StringGeometry.RiemannSurfaces.Analytic.Helpers.ChartMeromorphic
import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.Infrastructure.WirtingerDerivatives
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

/-!
# Chart Transition Infrastructure for Riemann Surfaces

This file proves that the meromorphic order `chartOrderAt` is chart-independent:
the order computed using any chart containing a point gives the same result.

## Main Results

* `chartOrderAt_eq_in_chart` — Chart independence of meromorphic order
* `chartOrderAt_eq_zero_near` — Order is 0 in punctured nhd of any point with finite order
* `chartOrderSupport_finite_general` — Finiteness of zeros+poles on compact surfaces
-/

namespace RiemannSurfaces.Analytic

open Complex Topology Classical
open scoped Manifold Topology

variable {RS : RiemannSurface}

/-- Extended chart with explicit instances from RS, for use in theorem signatures. -/
noncomputable abbrev eChart (r : RS.carrier) :=
  @extChartAt ℂ ℂ RS.carrier ℂ _ _ _ _ RS.topology 𝓘(ℂ, ℂ) RS.chartedSpace r

/-!
## Meromorphic Order Near a Singularity
-/

/-- Near a finite-order meromorphic point, all nearby points have order 0. -/
theorem meromorphicOrderAt_eq_zero_near {h : ℂ → ℂ} {z₀ : ℂ}
    (hmer : MeromorphicAt h z₀)
    (hne : meromorphicOrderAt h z₀ ≠ ⊤) :
    ∀ᶠ z₁ in nhdsWithin z₀ {z₀}ᶜ,
      meromorphicOrderAt h z₁ = 0 := by
  obtain ⟨g, hg_ana, hg_ne, hg_eq⟩ := (meromorphicOrderAt_ne_top_iff hmer).mp hne
  set n := (meromorphicOrderAt h z₀).untop₀
  -- hg_eq : h =ᶠ[nhdsWithin z₀ {z₀}ᶜ] fun z ↦ (z - z₀) ^ n • g z
  -- Convert EventuallyEq to Eventually, then extract open neighborhood
  have hg_eq_ev : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, h z = (z - z₀) ^ n • g z := hg_eq
  rw [eventually_nhdsWithin_iff] at hg_eq_ev
  obtain ⟨U₁, hU₁, hU₁_open, hz₀_U₁⟩ := eventually_nhds_iff.mp hg_eq_ev
  obtain ⟨U₂, hU₂, hU₂_open, hz₀_U₂⟩ := eventually_nhds_iff.mp hg_ana.eventually_analyticAt
  obtain ⟨U₃, hU₃, hU₃_open, hz₀_U₃⟩ :=
    eventually_nhds_iff.mp (hg_ana.continuousAt.eventually_ne hg_ne)
  -- Prove eventually in nhdsWithin using the intersection of open sets
  rw [eventually_nhdsWithin_iff]
  apply eventually_nhds_iff.mpr
  refine ⟨U₁ ∩ U₂ ∩ U₃, fun z₁ ⟨⟨hz₁_1, hz₁_2⟩, hz₁_3⟩ hz₁_ne => ?_,
    (hU₁_open.inter hU₂_open).inter hU₃_open, ⟨⟨hz₀_U₁, hz₀_U₂⟩, hz₀_U₃⟩⟩
  -- z₁ ∈ U₁ ∩ U₂ ∩ U₃, z₁ ∈ {z₀}ᶜ (i.e., z₁ ≠ z₀)
  -- Step 1: h =ᶠ[nhdsWithin z₁ {z₁}ᶜ] (fun z => (z - z₀)^n • g z)
  -- U₁ \ {z₀} is open and contains z₁, so it's a neighborhood of z₁
  have h_eq_near : h =ᶠ[nhdsWithin z₁ {z₁}ᶜ] fun z => (z - z₀) ^ n • g z := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    have hU₁_z₁ : U₁ \ {z₀} ∈ nhds z₁ :=
      (hU₁_open.sdiff isClosed_singleton).mem_nhds ⟨hz₁_1, hz₁_ne⟩
    exact Filter.Eventually.mono hU₁_z₁ fun z ⟨hz_1, hz_ne⟩ => hU₁ z hz_1 hz_ne
  -- Step 2: Transfer meromorphic order via congr
  rw [meromorphicOrderAt_congr h_eq_near]
  -- Step 3: The function is analytic at z₁ with nonzero value
  have hφ_ana : AnalyticAt ℂ (fun z => (z - z₀) ^ n • g z) z₁ :=
    ((analyticAt_id.sub analyticAt_const).zpow (sub_ne_zero.mpr hz₁_ne)).smul (hU₂ z₁ hz₁_2)
  have hφ_ne : (fun z => (z - z₀) ^ n • g z) z₁ ≠ 0 :=
    smul_ne_zero (zpow_ne_zero n (sub_ne_zero.mpr hz₁_ne)) (hU₃ z₁ hz₁_3)
  -- Step 4: Analytic nonzero → meromorphic order 0
  rw [hφ_ana.meromorphicOrderAt_eq, hφ_ana.analyticOrderAt_eq_zero.mpr hφ_ne]
  simp

/-!
## Chart Transition Maps
-/

/-- Selector-based chart transition from the selected chart at `r` to the selected
chart at `q`, namely `(extChartAt q) ∘ (extChartAt r).symm`.
This is a local computational helper, not an intrinsic canonical map determined only
by center points. -/
noncomputable def chartTransition (q r : RS.carrier) : ℂ → ℂ :=
  letI := RS.topology
  letI := RS.chartedSpace
  (extChartAt 𝓘(ℂ, ℂ) q) ∘ (extChartAt 𝓘(ℂ, ℂ) r).symm

/-- Chart transition is analytic at points in the overlap. -/
theorem chartTransition_analyticAt (q r : RS.carrier) (z : ℂ)
    (hz_tgt : z ∈ (eChart r).target)
    (hovlp : (eChart r).symm z ∈ (eChart q).source) :
    AnalyticAt ℂ (chartTransition (RS := RS) q r) z := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  -- Convert eChart hypotheses to extChartAt (definitionally equal)
  change z ∈ (extChartAt 𝓘(ℂ, ℂ) r).target at hz_tgt
  change (extChartAt 𝓘(ℂ, ℂ) r).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) q).source at hovlp
  have hcd : ContDiffWithinAt ℂ ⊤
      (extChartAt 𝓘(ℂ, ℂ) q ∘ (extChartAt 𝓘(ℂ, ℂ) r).symm) (Set.range 𝓘(ℂ, ℂ)) z :=
    contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ, ℂ)) q r
      (y := z) (by
        simp only [PartialEquiv.trans_source, PartialEquiv.symm_source]
        exact ⟨hz_tgt, hovlp⟩)
  have hrange : Set.range 𝓘(ℂ, ℂ) = Set.univ :=
    ModelWithCorners.range_eq_univ 𝓘(ℂ, ℂ)
  rw [hrange, contDiffWithinAt_univ] at hcd
  exact hcd.analyticAt

/-- Near an overlap point, selector-based chart transitions compose as expected:
`(a ← b) ∘ (b ← c) = (a ← c)` locally. -/
theorem chartTransition_comp_eventuallyEq
    (a b c : RS.carrier) (z : ℂ)
    (hz_tgt : z ∈ (eChart c).target)
    (hovlp_bc : (eChart c).symm z ∈ (eChart b).source) :
    (fun w : ℂ => chartTransition (RS := RS) a b (chartTransition (RS := RS) b c w))
      =ᶠ[nhds z]
    chartTransition (RS := RS) a c := by
  letI := RS.topology
  letI := RS.chartedSpace
  change z ∈ (extChartAt 𝓘(ℂ, ℂ) c).target at hz_tgt
  change (extChartAt 𝓘(ℂ, ℂ) c).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) b).source at hovlp_bc
  have hsrc_b_nhds :
      (extChartAt 𝓘(ℂ, ℂ) b).source ∈
        nhds ((extChartAt 𝓘(ℂ, ℂ) c).symm z) :=
    (isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) b).mem_nhds hovlp_bc
  have hovlp_nhds :
      ∀ᶠ w in nhds z,
        (extChartAt 𝓘(ℂ, ℂ) c).symm w ∈ (extChartAt 𝓘(ℂ, ℂ) b).source := by
    have hcont_symm :
        ContinuousAt (fun w : ℂ => (extChartAt 𝓘(ℂ, ℂ) c).symm w) z := by
      simpa using
        (continuousAt_extChartAt_symm'' (I := 𝓘(ℂ, ℂ)) hz_tgt)
    exact hcont_symm.eventually hsrc_b_nhds
  refine hovlp_nhds.mono ?_
  intro w hw_ovlp
  change (extChartAt 𝓘(ℂ, ℂ) a)
      ((extChartAt 𝓘(ℂ, ℂ) b).symm
        ((extChartAt 𝓘(ℂ, ℂ) b) ((extChartAt 𝓘(ℂ, ℂ) c).symm w)))
    = (extChartAt 𝓘(ℂ, ℂ) a) ((extChartAt 𝓘(ℂ, ℂ) c).symm w)
  exact congrArg (extChartAt 𝓘(ℂ, ℂ) a) ((extChartAt 𝓘(ℂ, ℂ) b).left_inv hw_ovlp)

/-- Derivative cocycle for selector-based chart transitions at an overlap point. -/
theorem chartTransition_deriv_comp
    (a b c : RS.carrier) (z : ℂ)
    (hz_tgt : z ∈ (eChart c).target)
    (hovlp_bc : (eChart c).symm z ∈ (eChart b).source)
    (hovlp_ac : (eChart c).symm z ∈ (eChart a).source) :
    deriv (chartTransition (RS := RS) a c) z =
      deriv (chartTransition (RS := RS) a b) (chartTransition (RS := RS) b c z) *
        deriv (chartTransition (RS := RS) b c) z := by
  letI := RS.topology
  letI := RS.chartedSpace
  change z ∈ (extChartAt 𝓘(ℂ, ℂ) c).target at hz_tgt
  change (extChartAt 𝓘(ℂ, ℂ) c).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) b).source at hovlp_bc
  change (extChartAt 𝓘(ℂ, ℂ) c).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) a).source at hovlp_ac
  have hbc_ana : AnalyticAt ℂ (chartTransition (RS := RS) b c) z :=
    chartTransition_analyticAt (RS := RS) b c z hz_tgt hovlp_bc
  have hab_tgt :
      chartTransition (RS := RS) b c z ∈ (eChart (RS := RS) b).target := by
    simpa [chartTransition, Function.comp_apply] using
      (eChart (RS := RS) b).map_source hovlp_bc
  have hab_src :
      (eChart (RS := RS) b).symm (chartTransition (RS := RS) b c z) ∈
        (eChart (RS := RS) a).source := by
    have hleft :
        (extChartAt 𝓘(ℂ, ℂ) b).symm (chartTransition (RS := RS) b c z) =
          (extChartAt 𝓘(ℂ, ℂ) c).symm z := by
      change (extChartAt 𝓘(ℂ, ℂ) b).symm
          ((extChartAt 𝓘(ℂ, ℂ) b) ((extChartAt 𝓘(ℂ, ℂ) c).symm z)) =
        (extChartAt 𝓘(ℂ, ℂ) c).symm z
      exact (extChartAt 𝓘(ℂ, ℂ) b).left_inv hovlp_bc
    exact hleft ▸ hovlp_ac
  have hab_ana :
      AnalyticAt ℂ (chartTransition (RS := RS) a b)
        (chartTransition (RS := RS) b c z) :=
    chartTransition_analyticAt (RS := RS) a b
      (chartTransition (RS := RS) b c z) hab_tgt hab_src
  have hcomp :
      HasDerivAt
        (fun w : ℂ =>
          chartTransition (RS := RS) a b (chartTransition (RS := RS) b c w))
        (deriv (chartTransition (RS := RS) a b) (chartTransition (RS := RS) b c z) *
          deriv (chartTransition (RS := RS) b c) z)
        z :=
    (hab_ana.differentiableAt.hasDerivAt).comp z (hbc_ana.differentiableAt.hasDerivAt)
  have heq :
      (fun w : ℂ =>
        chartTransition (RS := RS) a b (chartTransition (RS := RS) b c w))
        =ᶠ[nhds z]
      chartTransition (RS := RS) a c :=
    chartTransition_comp_eventuallyEq (RS := RS) a b c z hz_tgt hovlp_bc
  exact (hcomp.congr_of_eventuallyEq heq.symm).deriv

/-- Chain rule for `∂̄` composed with a chart transition map. -/
theorem wirtingerDerivBar_comp_chartTransition (f : ℂ → ℂ) (q r : RS.carrier) (z : ℂ)
    (hz_tgt : z ∈ (eChart r).target)
    (hovlp : (eChart r).symm z ∈ (eChart q).source)
    (hf : DifferentiableAt ℝ f (chartTransition (RS := RS) q r z)) :
    Infrastructure.wirtingerDerivBar (f ∘ chartTransition (RS := RS) q r) z =
      Infrastructure.wirtingerDerivBar f (chartTransition (RS := RS) q r z) *
        starRingEnd ℂ (deriv (chartTransition (RS := RS) q r) z) := by
  exact Infrastructure.wirtingerDerivBar_comp_analyticAt hf
    (chartTransition_analyticAt q r z hz_tgt hovlp)

/-- Chain rule for `∂` composed with a chart transition map. -/
theorem wirtingerDeriv_comp_chartTransition (f : ℂ → ℂ) (q r : RS.carrier) (z : ℂ)
    (hz_tgt : z ∈ (eChart r).target)
    (hovlp : (eChart r).symm z ∈ (eChart q).source)
    (hf : DifferentiableAt ℝ f (chartTransition (RS := RS) q r z)) :
    Infrastructure.wirtingerDeriv (f ∘ chartTransition (RS := RS) q r) z =
      Infrastructure.wirtingerDeriv f (chartTransition (RS := RS) q r z) *
        deriv (chartTransition (RS := RS) q r) z := by
  exact Infrastructure.wirtingerDeriv_comp_analyticAt hf
    (chartTransition_analyticAt q r z hz_tgt hovlp)

/-- On overlapping charts, the two chart pullbacks are eventually equal near the overlap point
after composing with the chart transition. -/
theorem comp_extChart_symm_eventuallyEq_chartTransition
    (F : RS.carrier → ℂ) (q r : RS.carrier) (z : ℂ)
    (hz_tgt : z ∈ (eChart r).target)
    (hovlp : (eChart r).symm z ∈ (eChart q).source) :
    (F ∘ (eChart r).symm) =ᶠ[nhds z]
      ((F ∘ (eChart q).symm) ∘ chartTransition (RS := RS) q r) := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  change (F ∘ (extChartAt 𝓘(ℂ, ℂ) r).symm) =ᶠ[nhds z]
      ((F ∘ (extChartAt 𝓘(ℂ, ℂ) q).symm) ∘ chartTransition (RS := RS) q r)
  have htgt_nhds : ∀ᶠ u in nhds z, u ∈ (extChartAt 𝓘(ℂ, ℂ) r).target :=
    (isOpen_extChartAt_target (I := 𝓘(ℂ, ℂ)) r).mem_nhds hz_tgt
  have hsrc_q_nhds : (extChartAt 𝓘(ℂ, ℂ) q).source ∈ nhds ((extChartAt 𝓘(ℂ, ℂ) r).symm z) :=
    (isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) q).mem_nhds hovlp
  have hovlp_nhds : ∀ᶠ u in nhds z, (extChartAt 𝓘(ℂ, ℂ) r).symm u ∈ (extChartAt 𝓘(ℂ, ℂ) q).source :=
    (continuousAt_extChartAt_symm'' (I := 𝓘(ℂ, ℂ)) hz_tgt).eventually hsrc_q_nhds
  exact (htgt_nhds.and hovlp_nhds).mono (fun u hu => by
    rcases hu with ⟨hu_tgt, hu_ovlp⟩
    simp only [Function.comp_apply, chartTransition]
    congr 1
    exact ((extChartAt 𝓘(ℂ, ℂ) q).left_inv hu_ovlp).symm)

/-- Chart-change formula for `∂̄` of local pullbacks. -/
theorem wirtingerDerivBar_extChart_symm_change
    (F : RS.carrier → ℂ) (q r : RS.carrier) (z : ℂ)
    (hz_tgt : z ∈ (eChart r).target)
    (hovlp : (eChart r).symm z ∈ (eChart q).source)
    (hf : DifferentiableAt ℝ (F ∘ (eChart q).symm)
      (chartTransition (RS := RS) q r z)) :
    Infrastructure.wirtingerDerivBar (F ∘ (eChart r).symm) z =
      Infrastructure.wirtingerDerivBar (F ∘ (eChart q).symm)
          (chartTransition (RS := RS) q r z) *
        starRingEnd ℂ (deriv (chartTransition (RS := RS) q r) z) := by
  have heq := comp_extChart_symm_eventuallyEq_chartTransition (RS := RS) F q r z hz_tgt hovlp
  calc
    Infrastructure.wirtingerDerivBar (F ∘ (eChart r).symm) z
      = Infrastructure.wirtingerDerivBar
          (((F ∘ (eChart q).symm) ∘ chartTransition (RS := RS) q r)) z := by
          exact Infrastructure.wirtingerDerivBar_congr_of_eventuallyEq heq
    _ = Infrastructure.wirtingerDerivBar (F ∘ (eChart q).symm)
          (chartTransition (RS := RS) q r z) *
        starRingEnd ℂ (deriv (chartTransition (RS := RS) q r) z) := by
          exact wirtingerDerivBar_comp_chartTransition
            (f := F ∘ (eChart q).symm) q r z hz_tgt hovlp hf

/-- Chart-change formula for `∂` of local pullbacks. -/
theorem wirtingerDeriv_extChart_symm_change
    (F : RS.carrier → ℂ) (q r : RS.carrier) (z : ℂ)
    (hz_tgt : z ∈ (eChart r).target)
    (hovlp : (eChart r).symm z ∈ (eChart q).source)
    (hf : DifferentiableAt ℝ (F ∘ (eChart q).symm)
      (chartTransition (RS := RS) q r z)) :
    Infrastructure.wirtingerDeriv (F ∘ (eChart r).symm) z =
      Infrastructure.wirtingerDeriv (F ∘ (eChart q).symm)
          (chartTransition (RS := RS) q r z) *
        deriv (chartTransition (RS := RS) q r) z := by
  have heq := comp_extChart_symm_eventuallyEq_chartTransition (RS := RS) F q r z hz_tgt hovlp
  calc
    Infrastructure.wirtingerDeriv (F ∘ (eChart r).symm) z
      = Infrastructure.wirtingerDeriv
          (((F ∘ (eChart q).symm) ∘ chartTransition (RS := RS) q r)) z := by
          exact Infrastructure.wirtingerDeriv_congr_of_eventuallyEq heq
    _ = Infrastructure.wirtingerDeriv (F ∘ (eChart q).symm)
          (chartTransition (RS := RS) q r z) *
        deriv (chartTransition (RS := RS) q r) z := by
          exact wirtingerDeriv_comp_chartTransition
            (f := F ∘ (eChart q).symm) q r z hz_tgt hovlp hf

/-- Chart-change formula for `∂̄` of local pullbacks of an `ℝ`-smooth function,
with differentiability discharged by `RealSmoothFunction` infrastructure. -/
theorem wirtingerDerivBar_extChart_symm_change_of_realSmooth
    (f : RealSmoothFunction RS) (q r : RS.carrier) (z : ℂ)
    (hz_tgt : z ∈ (eChart r).target)
    (hovlp : (eChart r).symm z ∈ (eChart q).source) :
    Infrastructure.wirtingerDerivBar (f.toFun ∘ (eChart r).symm) z =
      Infrastructure.wirtingerDerivBar (f.toFun ∘ (eChart q).symm)
          (chartTransition (RS := RS) q r z) *
        starRingEnd ℂ (deriv (chartTransition (RS := RS) q r) z) := by
  letI := RS.topology
  letI := RS.chartedSpace
  have htrans_tgt : chartTransition (RS := RS) q r z ∈ (chartAt ℂ q).target := by
    simpa [chartTransition, eChart, Function.comp_apply] using (eChart q).map_source hovlp
  have hf :
      DifferentiableAt ℝ (f.toFun ∘ (eChart q).symm)
        (chartTransition (RS := RS) q r z) := by
    simpa using RealSmoothFunction.differentiableAt_comp_chart_symm
      (f := f) (p0 := q) htrans_tgt
  exact wirtingerDerivBar_extChart_symm_change
    (F := f.toFun) q r z hz_tgt hovlp hf

/-- Chart-change formula for `∂` of local pullbacks of an `ℝ`-smooth function,
with differentiability discharged by `RealSmoothFunction` infrastructure. -/
theorem wirtingerDeriv_extChart_symm_change_of_realSmooth
    (f : RealSmoothFunction RS) (q r : RS.carrier) (z : ℂ)
    (hz_tgt : z ∈ (eChart r).target)
    (hovlp : (eChart r).symm z ∈ (eChart q).source) :
    Infrastructure.wirtingerDeriv (f.toFun ∘ (eChart r).symm) z =
      Infrastructure.wirtingerDeriv (f.toFun ∘ (eChart q).symm)
          (chartTransition (RS := RS) q r z) *
        deriv (chartTransition (RS := RS) q r) z := by
  letI := RS.topology
  letI := RS.chartedSpace
  have htrans_tgt : chartTransition (RS := RS) q r z ∈ (chartAt ℂ q).target := by
    simpa [chartTransition, eChart, Function.comp_apply] using (eChart q).map_source hovlp
  have hf :
      DifferentiableAt ℝ (f.toFun ∘ (eChart q).symm)
        (chartTransition (RS := RS) q r z) := by
    simpa using RealSmoothFunction.differentiableAt_comp_chart_symm
      (f := f) (p0 := q) htrans_tgt
  exact wirtingerDeriv_extChart_symm_change
    (F := f.toFun) q r z hz_tgt hovlp hf

/-- Point-based overlap formula for `∂̄` local coefficients of an `ℝ`-smooth function. -/
theorem wirtingerDerivBar_extChart_symm_change_at_point_of_realSmooth
    (f : RealSmoothFunction RS) (q r p : RS.carrier)
    (hp_r : p ∈ (eChart r).source)
    (hp_q : p ∈ (eChart q).source) :
    Infrastructure.wirtingerDerivBar (f.toFun ∘ (eChart r).symm) ((eChart r) p) =
      Infrastructure.wirtingerDerivBar (f.toFun ∘ (eChart q).symm)
          (chartTransition (RS := RS) q r ((eChart r) p)) *
        starRingEnd ℂ (deriv (chartTransition (RS := RS) q r) ((eChart r) p)) := by
  have hz_tgt : (eChart r) p ∈ (eChart r).target := (eChart r).map_source hp_r
  have hovlp : (eChart r).symm ((eChart r) p) ∈ (eChart q).source := by
    rw [(eChart r).left_inv hp_r]
    exact hp_q
  exact wirtingerDerivBar_extChart_symm_change_of_realSmooth
    (RS := RS) (f := f) q r ((eChart r) p) hz_tgt hovlp

/-- Point-based overlap formula for `∂` local coefficients of an `ℝ`-smooth function. -/
theorem wirtingerDeriv_extChart_symm_change_at_point_of_realSmooth
    (f : RealSmoothFunction RS) (q r p : RS.carrier)
    (hp_r : p ∈ (eChart r).source)
    (hp_q : p ∈ (eChart q).source) :
    Infrastructure.wirtingerDeriv (f.toFun ∘ (eChart r).symm) ((eChart r) p) =
      Infrastructure.wirtingerDeriv (f.toFun ∘ (eChart q).symm)
          (chartTransition (RS := RS) q r ((eChart r) p)) *
        deriv (chartTransition (RS := RS) q r) ((eChart r) p) := by
  have hz_tgt : (eChart r) p ∈ (eChart r).target := (eChart r).map_source hp_r
  have hovlp : (eChart r).symm ((eChart r) p) ∈ (eChart q).source := by
    rw [(eChart r).left_inv hp_r]
    exact hp_q
  exact wirtingerDeriv_extChart_symm_change_of_realSmooth
    (RS := RS) (f := f) q r ((eChart r) p) hz_tgt hovlp

/-- Chart transition has nonzero derivative at points in the overlap. -/
theorem chartTransition_deriv_ne_zero (q r : RS.carrier) (z : ℂ)
    (hz_tgt : z ∈ (eChart r).target)
    (hovlp : (eChart r).symm z ∈ (eChart q).source) :
    deriv (chartTransition (RS := RS) q r) z ≠ 0 := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  change z ∈ (extChartAt 𝓘(ℂ, ℂ) r).target at hz_tgt
  change (extChartAt 𝓘(ℂ, ℂ) r).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) q).source at hovlp
  intro h_eq_zero
  set T := chartTransition (RS := RS) q r with hT_def
  set S := chartTransition (RS := RS) r q with hS_def
  set w := T z with hw_def
  -- w is in target of extChartAt q
  have hw_tgt : w ∈ (extChartAt 𝓘(ℂ, ℂ) q).target := by
    simp only [hw_def, hT_def, chartTransition, Function.comp_apply]
    exact (extChartAt 𝓘(ℂ, ℂ) q).map_source hovlp
  -- (extChartAt q).symm w ∈ source of extChartAt r
  have hovlp_inv : (extChartAt 𝓘(ℂ, ℂ) q).symm w ∈ (extChartAt 𝓘(ℂ, ℂ) r).source := by
    simp only [hw_def, hT_def, chartTransition, Function.comp_apply]
    rw [(extChartAt 𝓘(ℂ, ℂ) q).left_inv hovlp]
    exact (extChartAt 𝓘(ℂ, ℂ) r).map_target hz_tgt
  -- S ∘ T = id near z
  have hST : ∀ᶠ u in nhds z, S (T u) = u := by
    have htgt_nhds : ∀ᶠ u in nhds z, u ∈ (extChartAt 𝓘(ℂ, ℂ) r).target :=
      (isOpen_extChartAt_target (I := 𝓘(ℂ, ℂ)) r).mem_nhds hz_tgt
    have hsrc_q_nhds : (extChartAt 𝓘(ℂ, ℂ) q).source ∈
        nhds ((extChartAt 𝓘(ℂ, ℂ) r).symm z) :=
      (isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) q).mem_nhds hovlp
    have hovlp_nhds : ∀ᶠ u in nhds z,
        (extChartAt 𝓘(ℂ, ℂ) r).symm u ∈ (extChartAt 𝓘(ℂ, ℂ) q).source :=
      (continuousAt_extChartAt_symm'' (I := 𝓘(ℂ, ℂ)) hz_tgt).eventually hsrc_q_nhds
    apply (htgt_nhds.and hovlp_nhds).mono
    intro u ⟨hu_tgt, hu_ovlp⟩
    simp only [hS_def, hT_def, chartTransition, Function.comp_apply]
    rw [(extChartAt 𝓘(ℂ, ℂ) q).left_inv hu_ovlp]
    exact (extChartAt 𝓘(ℂ, ℂ) r).right_inv hu_tgt
  -- S ∘ T has derivative 1 at z
  have h_deriv_one : HasDerivAt (S ∘ T) 1 z :=
    (hasDerivAt_id z).congr_of_eventuallyEq
      (hST.mono fun u hu => show (S ∘ T) u = id u from hu)
  -- Chain rule
  have hT_ana : AnalyticAt ℂ T z := by
    change AnalyticAt ℂ (chartTransition q r) z
    exact chartTransition_analyticAt q r z
      (show z ∈ (eChart r).target from hz_tgt)
      (show (eChart r).symm z ∈ (eChart q).source from hovlp)
  have hS_ana : AnalyticAt ℂ S w := by
    change AnalyticAt ℂ (chartTransition r q) w
    exact chartTransition_analyticAt r q w
      (show w ∈ (eChart q).target from hw_tgt)
      (show (eChart q).symm w ∈ (eChart r).source from hovlp_inv)
  have hT_diff := hT_ana.differentiableAt
  have hS_diff := hS_ana.differentiableAt
  -- Chain rule: S ∘ T has deriv (deriv S w) * (deriv T z) at z
  have h_chain : HasDerivAt (S ∘ T) (deriv S w * deriv T z) z :=
    hS_diff.hasDerivAt.comp_of_eq z hT_diff.hasDerivAt hw_def
  have h_prod := h_chain.unique h_deriv_one
  rw [h_eq_zero, mul_zero] at h_prod
  exact zero_ne_one h_prod

/-!
## Chart Independence of Meromorphic Order
-/

/-- **Chart independence of meromorphic order.** -/
theorem chartOrderAt_eq_in_chart (f : RS.carrier → ℂ) (q r : RS.carrier)
    (_hf : IsChartMeromorphic (RS := RS) f)
    (hr : r ∈ (eChart q).source) :
    chartOrderAt (RS := RS) f r =
      meromorphicOrderAt (chartRep (RS := RS) f q) ((eChart q) r) := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  change r ∈ (extChartAt 𝓘(ℂ, ℂ) q).source at hr
  set e_q := extChartAt 𝓘(ℂ, ℂ) q
  set e_r := extChartAt 𝓘(ℂ, ℂ) r
  set z := e_r r  -- = chartPt r
  set w := e_q r  -- target point
  show meromorphicOrderAt (f ∘ e_r.symm) z = meromorphicOrderAt (f ∘ e_q.symm) w
  -- z is in target of e_r
  have hz_tgt : z ∈ e_r.target :=
    e_r.map_source (mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) r)
  -- e_r.symm z = r ∈ e_q.source
  have hovlp : e_r.symm z ∈ e_q.source := by
    rw [show e_r.symm z = r from e_r.left_inv (mem_extChartAt_source r)]
    exact hr
  -- Chart transition is analytic with nonzero derivative
  have hT_ana : AnalyticAt ℂ (chartTransition (RS := RS) q r) z :=
    chartTransition_analyticAt q r z
      (show z ∈ (eChart r).target from hz_tgt)
      (show (eChart r).symm z ∈ (eChart q).source from hovlp)
  have hT_deriv : deriv (chartTransition (RS := RS) q r) z ≠ 0 :=
    chartTransition_deriv_ne_zero q r z
      (show z ∈ (eChart r).target from hz_tgt)
      (show (eChart r).symm z ∈ (eChart q).source from hovlp)
  set T := chartTransition (RS := RS) q r with hT_def
  -- T(z) = w
  have hTz : T z = w := by
    simp only [hT_def, chartTransition, Function.comp_apply, z, w]
    congr 1
    exact e_r.left_inv (mem_extChartAt_source r)
  -- f ∘ e_r.symm =ᶠ[𝓝 z] (f ∘ e_q.symm) ∘ T
  have heq : ∀ᶠ u in nhds z, (f ∘ e_r.symm) u = ((f ∘ e_q.symm) ∘ T) u := by
    have htgt_nhds : ∀ᶠ u in nhds z, u ∈ e_r.target :=
      (isOpen_extChartAt_target (I := 𝓘(ℂ, ℂ)) r).mem_nhds hz_tgt
    have hsrc_q_nhds : e_q.source ∈ nhds (e_r.symm z) :=
      (isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) q).mem_nhds hovlp
    have hovlp_nhds : ∀ᶠ u in nhds z, e_r.symm u ∈ e_q.source :=
      (continuousAt_extChartAt_symm'' (I := 𝓘(ℂ, ℂ)) hz_tgt).eventually hsrc_q_nhds
    apply (htgt_nhds.and hovlp_nhds).mono
    intro u ⟨hu_tgt, hu_ovlp⟩
    simp only [Function.comp_apply, hT_def, chartTransition]
    congr 1
    exact (e_q.left_inv hu_ovlp).symm
  have h1 : meromorphicOrderAt (f ∘ e_r.symm) z =
      meromorphicOrderAt ((f ∘ e_q.symm) ∘ T) z :=
    meromorphicOrderAt_congr (heq.filter_mono nhdsWithin_le_nhds)
  rw [h1, meromorphicOrderAt_comp_of_deriv_ne_zero hT_ana hT_deriv, hTz]

/-- Near any point q, chartOrderAt f r = 0 for sufficiently close r ≠ q,
    provided chartOrderAt f q ≠ ⊤. -/
theorem chartOrderAt_eq_zero_near (f : RS.carrier → ℂ) (q : RS.carrier)
    (hf : IsChartMeromorphic (RS := RS) f)
    (hne_top : chartOrderAt (RS := RS) f q ≠ ⊤) :
    ∀ᶠ r in @nhdsWithin RS.carrier RS.topology q {q}ᶜ,
      chartOrderAt (RS := RS) f r = 0 := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  set e_q := extChartAt 𝓘(ℂ, ℂ) q
  have h_order_zero_chart : ∀ᶠ z₁ in nhdsWithin (e_q q) {e_q q}ᶜ,
      meromorphicOrderAt (chartRep (RS := RS) f q) z₁ = 0 :=
    meromorphicOrderAt_eq_zero_near (hf q) hne_top
  rw [eventually_nhdsWithin_iff] at h_order_zero_chart ⊢
  have hsrc : (chartAt ℂ q).source ∈ @nhds _ RS.topology q :=
    (chartAt ℂ q).open_source.mem_nhds (mem_chart_source ℂ q)
  have h_pulled := (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) q).eventually h_order_zero_chart
  apply (h_pulled.and hsrc).mono
  intro r ⟨hr_chart_order, hr_src⟩ hr_ne
  have hr_ne_chart : e_q r ≠ e_q q := by
    intro heq
    exact hr_ne ((extChartAt 𝓘(ℂ, ℂ) q).injOn
      (by rw [extChartAt_source]; exact hr_src)
      (mem_extChartAt_source q) heq)
  -- Convert hr_src to eChart source for chartOrderAt_eq_in_chart
  have hr_echart : r ∈ (eChart q).source := by
    change r ∈ (extChartAt 𝓘(ℂ, ℂ) q).source
    rw [extChartAt_source]; exact hr_src
  rw [chartOrderAt_eq_in_chart f q r hf hr_echart]
  exact hr_chart_order hr_ne_chart

/-!
## Finiteness of Chart Order Support
-/

/-- chartOrderSupport is finite for nonconstant chart-meromorphic functions
    on compact Riemann surfaces. -/
theorem chartOrderSupport_finite_general (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hne : ∃ p₀, chartOrderAt (RS := CRS.toRiemannSurface) f p₀ ≠ ⊤) :
    (chartOrderSupport (RS := CRS.toRiemannSurface) f).Finite := by
  letI := CRS.toRiemannSurface.topology
  letI := CRS.toRiemannSurface.chartedSpace
  haveI := CRS.toRiemannSurface.isManifold
  haveI : CompactSpace CRS.toRiemannSurface.carrier := CRS.compact
  obtain ⟨p₀, hp₀⟩ := hne
  have hne_top : ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) f q ≠ ⊤ :=
    fun q => chartOrderAt_ne_top_of_ne_top_somewhere f hf p₀ hp₀ q
  by_contra h_inf
  rw [Set.not_finite] at h_inf
  obtain ⟨x, hx_acc⟩ := h_inf.exists_accPt_principal
  have h_zero_near := chartOrderAt_eq_zero_near f x hf (hne_top x)
  rw [accPt_iff_frequently_nhdsNE] at hx_acc
  exact hx_acc (h_zero_near.mono fun r hr hr_mem => hr_mem.1 hr)

end RiemannSurfaces.Analytic
