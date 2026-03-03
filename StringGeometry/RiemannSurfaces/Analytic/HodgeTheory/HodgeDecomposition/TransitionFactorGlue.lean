import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.HodgeDecomposition.Core

namespace RiemannSurfaces.Analytic

open Complex Topology
open scoped Manifold

variable {RS : RiemannSurface}

/-- Fixed-chart triple-overlap cocycle for transition Jacobian factors. -/
theorem dbarRealTransitionFactorByCharts_cocycle_hd
    (a b c p : RS.carrier)
    (hp_c :
      letI := RS.topology
      letI := RS.chartedSpace
      p ∈ (eChart (RS := RS) c).source)
    (hp_b :
      letI := RS.topology
      letI := RS.chartedSpace
      p ∈ (eChart (RS := RS) b).source)
    (hp_a :
      letI := RS.topology
      letI := RS.chartedSpace
      p ∈ (eChart (RS := RS) a).source) :
    letI := RS.topology
    letI := RS.chartedSpace
    Infrastructure.chartTransitionFactorByCharts (RS := RS) a c p =
      Infrastructure.chartTransitionFactorByCharts (RS := RS) a b p *
        Infrastructure.chartTransitionFactorByCharts (RS := RS) b c p := by
  exact Infrastructure.chartTransitionFactorByCharts_cocycle
    (RS := RS) a b c p hp_c hp_b hp_a

/-- Fixed-chart transition factor diagonal normalization. -/
theorem dbarRealTransitionFactorByCharts_self_hd
    (q p : RS.carrier)
    (hp_q :
      letI := RS.topology
      letI := RS.chartedSpace
      p ∈ (eChart (RS := RS) q).source) :
    letI := RS.topology
    letI := RS.chartedSpace
    Infrastructure.chartTransitionFactorByCharts (RS := RS) q q p = 1 := by
  exact Infrastructure.chartTransitionFactorByCharts_self
    (RS := RS) q p hp_q

/-- Fixed-chart reverse-factor product is `1` on overlaps. -/
theorem dbarRealTransitionFactorByCharts_mul_reverse_eq_one_hd
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
    Infrastructure.chartTransitionFactorByCharts (RS := RS) q r p *
      Infrastructure.chartTransitionFactorByCharts (RS := RS) r q p = 1 := by
  exact Infrastructure.chartTransitionFactorByCharts_mul_reverse_eq_one
    (RS := RS) q r p hp_r hp_q

/-- Fixed-chart transition factors are pointwise inverses on overlaps. -/
theorem dbarRealTransitionFactorByCharts_eq_inv_reverse_hd
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
    Infrastructure.chartTransitionFactorByCharts (RS := RS) q r p =
      (Infrastructure.chartTransitionFactorByCharts (RS := RS) r q p)⁻¹ := by
  exact Infrastructure.chartTransitionFactorByCharts_eq_inv_reverse
    (RS := RS) q r p hp_r hp_q

/-- Continuity of reciprocal fixed-chart transition factors on overlaps. -/
theorem dbarRealTransitionFactorByCharts_inv_continuousAt_hd
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
    ContinuousAt
      (fun x : RS.carrier => (Infrastructure.chartTransitionFactorByCharts (RS := RS) q r x)⁻¹) p := by
  exact Infrastructure.chartTransitionFactorByCharts_inv_continuousAt
    (RS := RS) q r p hp_r hp_q

/-- `C^∞` regularity of reciprocal fixed-chart transition factors on overlaps. -/
theorem dbarRealTransitionFactorByCharts_inv_contMDiffAt_hd
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
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
      (fun x : RS.carrier => (Infrastructure.chartTransitionFactorByCharts (RS := RS) q r x)⁻¹) p := by
  exact Infrastructure.chartTransitionFactorByCharts_inv_contMDiffAt
    (RS := RS) q r p hp_r hp_q

/-- Inverse-factor version of the fixed-chart overlap identity for local `∂̄` coefficients. -/
theorem dbarRealLocalCoeff_chartChange_fixedCharts_inv_hd
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
    wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) q).symm)
        (chartTransition (RS := RS) q r ((eChart (RS := RS) r) p)) =
      wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) r).symm) ((eChart (RS := RS) r) p) *
        (Infrastructure.chartTransitionFactorByCharts (RS := RS) q r p)⁻¹ := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hchange :=
    dbarRealLocalCoeff_chartChange_fixedCharts_hd (RS := RS) f q r p hp_r hp_q
  have hfac_ne :
      Infrastructure.chartTransitionFactorByCharts (RS := RS) q r p ≠ 0 :=
    Infrastructure.chartTransitionFactorByCharts_ne_zero (RS := RS) q r p hp_r hp_q
  exact (eq_mul_inv_iff_mul_eq₀ hfac_ne).2 hchange.symm

/-- Neighborhood-level inverse-factor fixed-chart overlap identity for local `∂̄` coefficients. -/
theorem dbarRealLocalCoeff_eventuallyEq_fixedCharts_inv_hd
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
      wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) q).symm)
          (chartTransition (RS := RS) q r ((eChart (RS := RS) r) x)))
      =ᶠ[nhds p]
    (fun x : RS.carrier =>
      wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) r).symm) ((eChart (RS := RS) r) x) *
        (Infrastructure.chartTransitionFactorByCharts (RS := RS) q r x)⁻¹) := by
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
    dbarRealLocalCoeff_chartChange_fixedCharts_inv_hd (RS := RS) f q r x hx.1 hx.2)

/-- On chart overlaps, the inverse-factor version of the fixed-chart `∂̄` coefficient
right-hand side is smooth at the overlap point. -/
theorem dbarRealLocalCoeff_rhs_inv_contMDiffAt_fixedCharts_hd
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
        wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) r).symm) ((eChart (RS := RS) r) x) *
          (Infrastructure.chartTransitionFactorByCharts (RS := RS) q r x)⁻¹) p := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hcoeff :
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
        (fun x : RS.carrier =>
          wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) r).symm) ((eChart (RS := RS) r) x))
        p :=
    dbarRealLocalCoeff_contMDiffAt_fixedCharts_hd (RS := RS) f q r p hp_r hp_q
  have hInv :
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
        (fun x : RS.carrier => (Infrastructure.chartTransitionFactorByCharts (RS := RS) q r x)⁻¹) p :=
    Infrastructure.chartTransitionFactorByCharts_inv_contMDiffAt (RS := RS) q r p hp_r hp_q
  have hmulSmooth : ContDiff ℝ smoothOrder (fun z : ℂ × ℂ => z.1 * z.2) := by
    exact (contDiff_mul : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun z : ℂ × ℂ => z.1 * z.2)).of_le
      smoothOrder_le_top
  have hpair :
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ × ℂ) smoothOrder
        (fun x : RS.carrier =>
          ((fun y : RS.carrier =>
            wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) r).symm) ((eChart (RS := RS) r) y))
            x,
            (Infrastructure.chartTransitionFactorByCharts (RS := RS) q r x)⁻¹)) p :=
    hcoeff.prodMk_space hInv
  have hmulMap :
      ContMDiffAt 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ) smoothOrder
        (fun z : ℂ × ℂ => z.1 * z.2)
        (((fun y : RS.carrier =>
          wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) r).symm) ((eChart (RS := RS) r) y))
          p,
          (Infrastructure.chartTransitionFactorByCharts (RS := RS) q r p)⁻¹)) :=
    (hmulSmooth.contMDiff).contMDiffAt
  simpa [Function.comp] using hmulMap.comp p hpair

/-- On chart overlaps, the transferred local `∂̄` coefficient expression
in source chart `r` is smooth at the overlap point, via inverse-factor transport. -/
theorem dbarRealLocalCoeff_transferred_contMDiffAt_fixedCharts_hd
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
          (chartTransition (RS := RS) q r ((eChart (RS := RS) r) x))) p := by
  letI := RS.topology
  letI := RS.chartedSpace
  have heq :
      (fun x : RS.carrier =>
        wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) q).symm)
          (chartTransition (RS := RS) q r ((eChart (RS := RS) r) x)))
        =ᶠ[nhds p]
      (fun x : RS.carrier =>
        wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) r).symm) ((eChart (RS := RS) r) x) *
          (Infrastructure.chartTransitionFactorByCharts (RS := RS) q r x)⁻¹) :=
    dbarRealLocalCoeff_eventuallyEq_fixedCharts_inv_hd (RS := RS) f q r p hp_r hp_q
  have hrhs :
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
        (fun x : RS.carrier =>
          wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) r).symm) ((eChart (RS := RS) r) x) *
            (Infrastructure.chartTransitionFactorByCharts (RS := RS) q r x)⁻¹) p :=
    dbarRealLocalCoeff_rhs_inv_contMDiffAt_fixedCharts_hd (RS := RS) f q r p hp_r hp_q
  exact hrhs.congr_of_eventuallyEq heq

/-- On chart overlaps, the inverse-factor fixed-chart right-hand side is smooth
in `WithinAt` form at the overlap point. -/
theorem dbarRealLocalCoeff_rhs_inv_contMDiffWithinAt_fixedCharts_hd
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
        wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) r).symm) ((eChart (RS := RS) r) x) *
          (Infrastructure.chartTransitionFactorByCharts (RS := RS) q r x)⁻¹)
      ((eChart (RS := RS) r).source ∩ (eChart (RS := RS) q).source) p := by
  letI := RS.topology
  letI := RS.chartedSpace
  exact
    (dbarRealLocalCoeff_rhs_inv_contMDiffAt_fixedCharts_hd
      (RS := RS) f q r p hp_r hp_q).contMDiffWithinAt

/-- On chart overlaps, the transferred local `∂̄` coefficient expression
is smooth in `WithinAt` form at the overlap point. -/
theorem dbarRealLocalCoeff_transferred_contMDiffWithinAt_fixedCharts_hd
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
        wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) q).symm)
          (chartTransition (RS := RS) q r ((eChart (RS := RS) r) x)))
      ((eChart (RS := RS) r).source ∩ (eChart (RS := RS) q).source) p := by
  letI := RS.topology
  letI := RS.chartedSpace
  exact
    (dbarRealLocalCoeff_transferred_contMDiffAt_fixedCharts_hd
      (RS := RS) f q r p hp_r hp_q).contMDiffWithinAt

/-- On chart overlaps, the transferred local `∂̄` coefficient expression
is smooth on the overlap set. -/
theorem dbarRealLocalCoeff_transferred_contMDiffOn_overlap_fixedCharts_hd
    (f : RealSmoothFunction RS) (q r : RS.carrier) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
      (fun x : RS.carrier =>
        wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) q).symm)
          (chartTransition (RS := RS) q r ((eChart (RS := RS) r) x)))
      ((eChart (RS := RS) r).source ∩ (eChart (RS := RS) q).source) := by
  letI := RS.topology
  letI := RS.chartedSpace
  intro p hp
  exact
    (dbarRealLocalCoeff_transferred_contMDiffAt_fixedCharts_hd
      (RS := RS) f q r p hp.1 hp.2).contMDiffWithinAt

/-- On chart overlaps, the inverse-factor fixed-chart right-hand side
is smooth on the overlap set. -/
theorem dbarRealLocalCoeff_rhs_inv_contMDiffOn_overlap_fixedCharts_hd
    (f : RealSmoothFunction RS) (q r : RS.carrier) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
      (fun x : RS.carrier =>
        wirtingerDeriv_zbar (f.toFun ∘ (eChart (RS := RS) r).symm) ((eChart (RS := RS) r) x) *
          (Infrastructure.chartTransitionFactorByCharts (RS := RS) q r x)⁻¹)
      ((eChart (RS := RS) r).source ∩ (eChart (RS := RS) q).source) := by
  letI := RS.topology
  letI := RS.chartedSpace
  intro p hp
  exact
    (dbarRealLocalCoeff_rhs_inv_contMDiffAt_fixedCharts_hd
      (RS := RS) f q r p hp.1 hp.2).contMDiffWithinAt
