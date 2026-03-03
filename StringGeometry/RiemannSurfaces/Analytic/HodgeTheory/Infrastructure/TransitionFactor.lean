import StringGeometry.RiemannSurfaces.Analytic.Helpers.ChartTransition
import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.Infrastructure.ChartSelection
import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.Infrastructure.RealSmoothness

/-!
# Transition-Factor Infrastructure

Reusable lemmas for the chart-transition Jacobian factor
`p ↦ star(deriv (chartTransition p0 p) ((chartAt p) p))`.

This factor appears in chart-change formulas for local `(0,1)` coefficients.
It is selector-dependent through `chartAt`, so it should be treated as diagnostic
infrastructure unless/until transferred to a chart-invariant formulation.
-/

namespace RiemannSurfaces.Analytic.Infrastructure

open Complex Topology
open OnePoint
open scoped Manifold

variable {RS : RiemannSurface}

/-- Transition-Jacobian factor for chart changes from a fixed center chart `p0`. -/
noncomputable def chartTransitionFactor
    (p0 : RS.carrier) : RS.carrier → ℂ := by
  letI := RS.topology
  letI := RS.chartedSpace
  exact fun p =>
    starRingEnd ℂ (deriv (chartTransition (RS := RS) p0 p) ((chartAt ℂ p) p))

/-- If the chosen chart at `p` equals the chart at `p0`, then the transition factor is `1`. -/
theorem chartTransitionFactor_eq_one_of_chartEq
    (p0 p : RS.carrier)
    (hchart :
      letI := RS.topology
      letI := RS.chartedSpace
      @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p =
        @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p0) :
    letI := RS.topology
    letI := RS.chartedSpace
    chartTransitionFactor (RS := RS) p0 p = 1 := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hp0src : p ∈ (chartAt ℂ p0).source := by
    simpa [hchart] using (mem_chart_source ℂ p)
  have hx_tgt : ((chartAt ℂ p0) p) ∈ (chartAt ℂ p0).target :=
    (chartAt ℂ p0).map_source hp0src
  have hevent :
      (fun y : ℂ => (chartAt ℂ p0) ((chartAt ℂ p0).symm y)) =ᶠ[nhds ((chartAt ℂ p0) p)]
      (fun y : ℂ => y) := by
    simpa [id, Function.comp] using (chartAt ℂ p0).eventually_right_inverse hx_tgt
  have hderiv_aux :
      HasDerivAt (fun y : ℂ => (chartAt ℂ p0) ((chartAt ℂ p0).symm y)) (1 : ℂ)
        ((chartAt ℂ p0) p) :=
    (hasDerivAt_id ((chartAt ℂ p0) p)).congr_of_eventuallyEq hevent
  have hderiv :
      deriv (fun y : ℂ => (chartAt ℂ p0) ((chartAt ℂ p0).symm y)) ((chartAt ℂ p0) p) = (1 : ℂ) :=
    hderiv_aux.deriv
  have hchartEq : (chartAt ℂ p) p = (chartAt ℂ p0) p := by
    simp [hchart]
  have hcomp : chartTransition (RS := RS) p0 p =
      (fun y : ℂ => (chartAt ℂ p0) ((chartAt ℂ p0).symm y)) := by
    ext y
    simp [chartTransition, hchart, extChartAt]
  rw [chartTransitionFactor, hcomp, hchartEq, hderiv]
  simp

/-- The transition factor is normalized to `1` at the center point. -/
theorem chartTransitionFactor_center (p0 : RS.carrier) :
    letI := RS.topology
    letI := RS.chartedSpace
    chartTransitionFactor (RS := RS) p0 p0 = 1 := by
  letI := RS.topology
  letI := RS.chartedSpace
  simpa using chartTransitionFactor_eq_one_of_chartEq (RS := RS) p0 p0 rfl

/-- On the fixed-chart source overlap, the transition factor is nonzero. -/
theorem chartTransitionFactor_ne_zero_of_mem_source
    (p0 p : RS.carrier)
    (hp0 :
      letI := RS.topology
      letI := RS.chartedSpace
      p ∈ (chartAt ℂ p0).source) :
    letI := RS.topology
    letI := RS.chartedSpace
    chartTransitionFactor (RS := RS) p0 p ≠ 0 := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hp : p ∈ (eChart (RS := RS) p).source := by
    simp [eChart]
  have hz_tgt : ((eChart (RS := RS) p) p) ∈ (eChart (RS := RS) p).target :=
    (eChart (RS := RS) p).map_source hp
  have hovlp : (eChart (RS := RS) p).symm ((eChart (RS := RS) p) p) ∈
      (eChart (RS := RS) p0).source := by
    rw [(eChart (RS := RS) p).left_inv hp]
    simpa [eChart] using hp0
  have hderiv_ne :
      deriv (chartTransition (RS := RS) p0 p) ((eChart (RS := RS) p) p) ≠ 0 :=
    chartTransition_deriv_ne_zero (RS := RS) p0 p ((eChart (RS := RS) p) p) hz_tgt hovlp
  have hstar_ne :
      starRingEnd ℂ (deriv (chartTransition (RS := RS) p0 p) ((eChart (RS := RS) p) p)) ≠ 0 :=
    (map_ne_zero_iff (starRingEnd ℂ) (starRingEnd ℂ).injective).2 hderiv_ne
  simpa [chartTransitionFactor, eChart] using hstar_ne

/-- Near `p0`, the transition factor is nonzero. -/
theorem chartTransitionFactor_eventually_ne_zero (p0 : RS.carrier) :
    letI := RS.topology
    letI := RS.chartedSpace
    ∀ᶠ p in nhds p0, chartTransitionFactor (RS := RS) p0 p ≠ 0 := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hsrc : ∀ᶠ p in nhds p0, p ∈ (chartAt ℂ p0).source :=
    (chartAt ℂ p0).open_source.mem_nhds (mem_chart_source ℂ p0)
  exact hsrc.mono (fun p hp => chartTransitionFactor_ne_zero_of_mem_source
    (RS := RS) p0 p hp)

/-- Conditional local smoothness: if `chartAt` is eventually constant near `p0`,
the transition factor is smooth at `p0`. -/
theorem chartTransitionFactor_contMDiffAt_of_eventuallyEq_chart
    (p0 : RS.carrier) {n : WithTop ℕ∞}
    (hchart :
      letI := RS.topology
      letI := RS.chartedSpace
      (fun p : RS.carrier => @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p)
        =ᶠ[nhds p0]
      (fun _ : RS.carrier => @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p0)) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n
      (chartTransitionFactor (RS := RS) p0) p0 := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hloc : chartTransitionFactor (RS := RS) p0 =ᶠ[nhds p0] fun _ : RS.carrier => (1 : ℂ) := by
    refine hchart.mono ?_
    intro p hp
    simpa using chartTransitionFactor_eq_one_of_chartEq (RS := RS) p0 p hp
  exact (contMDiffAt_const : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n
      (fun _ : RS.carrier => (1 : ℂ)) p0).congr_of_eventuallyEq hloc

/-- Local smoothness of the transition factor under local chart-selection stability. -/
theorem chartTransitionFactor_contMDiffAt_of_chartAtLocallyConstant
    (p0 : RS.carrier) {n : WithTop ℕ∞}
    (hchart : ChartAtLocallyConstant RS) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n
      (chartTransitionFactor (RS := RS) p0) p0 := by
  exact chartTransitionFactor_contMDiffAt_of_eventuallyEq_chart
    (RS := RS) (n := n) p0 (hchart p0)

/-!
## Chart-Indexed Transition Factors (Selector-Free Local Infrastructure)

These definitions keep chart choices fixed (`q`, `r`) and avoid the moving selector
`p ↦ chartAt ℂ p` inside the transition factor.
-/

/-- Jacobian factor of a fixed chart transition `chartTransition q r`, viewed in chart coordinates. -/
noncomputable def chartTransitionFactorInCharts
    (q r : RS.carrier) : ℂ → ℂ :=
  fun z => starRingEnd ℂ (deriv (chartTransition (RS := RS) q r) z)

/-- Complex derivative of a fixed chart transition `chartTransition q r`, viewed in chart coordinates. -/
noncomputable def chartTransitionDerivInCharts
    (q r : RS.carrier) : ℂ → ℂ :=
  fun z => deriv (chartTransition (RS := RS) q r) z

/-- Fixed-chart self-transition Jacobian factor is normalized to `1`
at points in the source chart domain. -/
theorem chartTransitionFactorInCharts_self
    (q : RS.carrier) (z : ℂ)
    (hz :
      letI := RS.topology
      letI := RS.chartedSpace
      z ∈ (eChart (RS := RS) q).target) :
    letI := RS.topology
    letI := RS.chartedSpace
    chartTransitionFactorInCharts (RS := RS) q q z = 1 := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hz_chart : z ∈ (chartAt ℂ q).target := by
    simpa [eChart] using hz
  have hevent :
      (fun y : ℂ => (chartAt ℂ q) ((chartAt ℂ q).symm y)) =ᶠ[nhds z]
      (fun y : ℂ => y) := by
    simpa [id, Function.comp] using
      (chartAt ℂ q).eventually_right_inverse hz_chart
  have hderiv_aux :
      HasDerivAt (fun y : ℂ => (chartAt ℂ q) ((chartAt ℂ q).symm y)) (1 : ℂ) z :=
    (hasDerivAt_id z).congr_of_eventuallyEq hevent
  have hderiv :
      deriv (fun y : ℂ => (chartAt ℂ q) ((chartAt ℂ q).symm y)) z = (1 : ℂ) :=
    hderiv_aux.deriv
  have hcomp :
      chartTransition (RS := RS) q q =
        (fun y : ℂ => (chartAt ℂ q) ((chartAt ℂ q).symm y)) := by
    ext y
    simp [chartTransition]
  rw [chartTransitionFactorInCharts, hcomp, hderiv]
  simp

/-- Derivative cocycle for fixed chart transitions on triple overlaps (chart-coordinate form). -/
theorem chartTransitionDerivInCharts_cocycle
    (a b c : RS.carrier) (z : ℂ)
    (hz_tgt :
      letI := RS.topology
      letI := RS.chartedSpace
      z ∈ (eChart (RS := RS) c).target)
    (hovlp_bc :
      letI := RS.topology
      letI := RS.chartedSpace
      (eChart (RS := RS) c).symm z ∈ (eChart (RS := RS) b).source)
    (hovlp_ac :
      letI := RS.topology
      letI := RS.chartedSpace
      (eChart (RS := RS) c).symm z ∈ (eChart (RS := RS) a).source) :
    letI := RS.topology
    letI := RS.chartedSpace
    chartTransitionDerivInCharts (RS := RS) a c z =
      chartTransitionDerivInCharts (RS := RS) a b (chartTransition (RS := RS) b c z) *
        chartTransitionDerivInCharts (RS := RS) b c z := by
  simpa [chartTransitionDerivInCharts] using
    RiemannSurfaces.Analytic.chartTransition_deriv_comp
      (RS := RS) a b c z hz_tgt hovlp_bc hovlp_ac

/-- Jacobian-factor cocycle for fixed chart transitions on triple overlaps
(chart-coordinate form). -/
theorem chartTransitionFactorInCharts_cocycle
    (a b c : RS.carrier) (z : ℂ)
    (hz_tgt :
      letI := RS.topology
      letI := RS.chartedSpace
      z ∈ (eChart (RS := RS) c).target)
    (hovlp_bc :
      letI := RS.topology
      letI := RS.chartedSpace
      (eChart (RS := RS) c).symm z ∈ (eChart (RS := RS) b).source)
    (hovlp_ac :
      letI := RS.topology
      letI := RS.chartedSpace
      (eChart (RS := RS) c).symm z ∈ (eChart (RS := RS) a).source) :
    letI := RS.topology
    letI := RS.chartedSpace
    chartTransitionFactorInCharts (RS := RS) a c z =
      chartTransitionFactorInCharts (RS := RS) a b (chartTransition (RS := RS) b c z) *
        chartTransitionFactorInCharts (RS := RS) b c z := by
  have hderiv :
      chartTransitionDerivInCharts (RS := RS) a c z =
        chartTransitionDerivInCharts (RS := RS) a b (chartTransition (RS := RS) b c z) *
          chartTransitionDerivInCharts (RS := RS) b c z :=
    chartTransitionDerivInCharts_cocycle
      (RS := RS) a b c z hz_tgt hovlp_bc hovlp_ac
  calc
    chartTransitionFactorInCharts (RS := RS) a c z
        = starRingEnd ℂ (chartTransitionDerivInCharts (RS := RS) a c z) := by
            rfl
    _ = starRingEnd ℂ
          (chartTransitionDerivInCharts (RS := RS) a b (chartTransition (RS := RS) b c z) *
            chartTransitionDerivInCharts (RS := RS) b c z) := by
          rw [hderiv]
    _ = starRingEnd ℂ
          (chartTransitionDerivInCharts (RS := RS) a b (chartTransition (RS := RS) b c z)) *
        starRingEnd ℂ (chartTransitionDerivInCharts (RS := RS) b c z) := by
          simp
    _ = chartTransitionFactorInCharts (RS := RS) a b (chartTransition (RS := RS) b c z) *
        chartTransitionFactorInCharts (RS := RS) b c z := by
          rfl

/-- Pullback of `chartTransitionFactorInCharts q r` to the surface using the fixed source chart `r`. -/
noncomputable def chartTransitionFactorByCharts
    (q r : RS.carrier) : RS.carrier → ℂ := by
  letI := RS.topology
  letI := RS.chartedSpace
  exact fun p => chartTransitionFactorInCharts (RS := RS) q r ((eChart (RS := RS) r) p)

/-- Jacobian-factor cocycle for fixed chart transitions on triple overlaps
(surface-point form with fixed source chart pullbacks). -/
theorem chartTransitionFactorByCharts_cocycle
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
    chartTransitionFactorByCharts (RS := RS) a c p =
      chartTransitionFactorByCharts (RS := RS) a b p *
        chartTransitionFactorByCharts (RS := RS) b c p := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hz_tgt : ((eChart (RS := RS) c) p) ∈ (eChart (RS := RS) c).target :=
    (eChart (RS := RS) c).map_source hp_c
  have hovlp_bc : (eChart (RS := RS) c).symm ((eChart (RS := RS) c) p) ∈
      (eChart (RS := RS) b).source := by
    rw [(eChart (RS := RS) c).left_inv hp_c]
    exact hp_b
  have hovlp_ac : (eChart (RS := RS) c).symm ((eChart (RS := RS) c) p) ∈
      (eChart (RS := RS) a).source := by
    rw [(eChart (RS := RS) c).left_inv hp_c]
    exact hp_a
  have hchart :
      chartTransition (RS := RS) b c ((eChart (RS := RS) c) p) = (eChart (RS := RS) b) p := by
    change (extChartAt 𝓘(ℂ, ℂ) b) ((extChartAt 𝓘(ℂ, ℂ) c).symm ((extChartAt 𝓘(ℂ, ℂ) c) p)) =
      (extChartAt 𝓘(ℂ, ℂ) b) p
    exact congrArg (extChartAt 𝓘(ℂ, ℂ) b) ((extChartAt 𝓘(ℂ, ℂ) c).left_inv hp_c)
  calc
    chartTransitionFactorByCharts (RS := RS) a c p
        = chartTransitionFactorInCharts (RS := RS) a c ((eChart (RS := RS) c) p) := by
            rfl
    _ = chartTransitionFactorInCharts (RS := RS) a b
          (chartTransition (RS := RS) b c ((eChart (RS := RS) c) p)) *
        chartTransitionFactorInCharts (RS := RS) b c ((eChart (RS := RS) c) p) := by
          exact chartTransitionFactorInCharts_cocycle
            (RS := RS) a b c ((eChart (RS := RS) c) p) hz_tgt hovlp_bc hovlp_ac
    _ = chartTransitionFactorInCharts (RS := RS) a b ((eChart (RS := RS) b) p) *
        chartTransitionFactorInCharts (RS := RS) b c ((eChart (RS := RS) c) p) := by
          rw [hchart]
    _ = chartTransitionFactorByCharts (RS := RS) a b p *
        chartTransitionFactorByCharts (RS := RS) b c p := by
          rfl

/-- Surface-level normalization of fixed-chart transition factors on the diagonal. -/
theorem chartTransitionFactorByCharts_self
    (q p : RS.carrier)
    (hp :
      letI := RS.topology
      letI := RS.chartedSpace
      p ∈ (eChart (RS := RS) q).source) :
    letI := RS.topology
    letI := RS.chartedSpace
    chartTransitionFactorByCharts (RS := RS) q q p = 1 := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hz :
      ((eChart (RS := RS) q) p) ∈ (eChart (RS := RS) q).target :=
    (eChart (RS := RS) q).map_source hp
  simpa [chartTransitionFactorByCharts] using
    chartTransitionFactorInCharts_self (RS := RS) q ((eChart (RS := RS) q) p) hz

/-- Fixed-chart reverse transition factors multiply to `1` on overlaps. -/
theorem chartTransitionFactorByCharts_mul_reverse_eq_one
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
    chartTransitionFactorByCharts (RS := RS) q r p *
      chartTransitionFactorByCharts (RS := RS) r q p = 1 := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hcocycle :
      chartTransitionFactorByCharts (RS := RS) q q p =
        chartTransitionFactorByCharts (RS := RS) q r p *
          chartTransitionFactorByCharts (RS := RS) r q p :=
    chartTransitionFactorByCharts_cocycle (RS := RS) q r q p hp_q hp_r hp_q
  calc
    chartTransitionFactorByCharts (RS := RS) q r p *
        chartTransitionFactorByCharts (RS := RS) r q p
      = chartTransitionFactorByCharts (RS := RS) q q p := by simpa using hcocycle.symm
    _ = 1 := chartTransitionFactorByCharts_self (RS := RS) q p hp_q

/-- Fixed-chart transition factors are mutual inverses on overlaps. -/
theorem chartTransitionFactorByCharts_eq_inv_reverse
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
    chartTransitionFactorByCharts (RS := RS) q r p =
      (chartTransitionFactorByCharts (RS := RS) r q p)⁻¹ := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hmul :
      chartTransitionFactorByCharts (RS := RS) q r p *
        chartTransitionFactorByCharts (RS := RS) r q p = 1 :=
    chartTransitionFactorByCharts_mul_reverse_eq_one (RS := RS) q r p hp_r hp_q
  have hne :
      chartTransitionFactorByCharts (RS := RS) r q p ≠ 0 :=
    by
      intro hzero
      have h01 : (0 : ℂ) = 1 := by
        calc
          (0 : ℂ)
              = chartTransitionFactorByCharts (RS := RS) q r p *
                  chartTransitionFactorByCharts (RS := RS) r q p := by
                    simp [hzero]
          _ = 1 := hmul
      exact zero_ne_one h01
  exact (mul_eq_one_iff_eq_inv₀ hne).mp hmul

/-- For fixed chart centers `q`, `r`, the transition derivative in chart coordinates is `C^∞`
at every overlap point (over `ℂ`). -/
theorem chartTransitionDerivInCharts_contDiffAt
    (q r : RS.carrier) (z : ℂ)
    (hz_tgt :
      letI := RS.topology
      letI := RS.chartedSpace
      z ∈ (eChart (RS := RS) r).target)
    (hovlp :
      letI := RS.topology
      letI := RS.chartedSpace
      (eChart (RS := RS) r).symm z ∈ (eChart (RS := RS) q).source) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContDiffAt ℂ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (chartTransitionDerivInCharts (RS := RS) q r) z := by
  letI := RS.topology
  letI := RS.chartedSpace
  have htrans_ana : AnalyticAt ℂ (chartTransition (RS := RS) q r) z :=
    chartTransition_analyticAt (RS := RS) q r z hz_tgt hovlp
  have hderiv_ana : AnalyticAt ℂ (fun w : ℂ => deriv (chartTransition (RS := RS) q r) w) z :=
    htrans_ana.deriv
  simpa [chartTransitionDerivInCharts] using hderiv_ana.contDiffAt

/-- For fixed chart centers `q`, `r`, the transition derivative in chart coordinates is `C^∞`
at overlap points over `ℝ` (obtained by scalar restriction from `ℂ`). -/
theorem chartTransitionDerivInCharts_contDiffAt_real
    (q r : RS.carrier) (z : ℂ)
    (hz_tgt :
      letI := RS.topology
      letI := RS.chartedSpace
      z ∈ (eChart (RS := RS) r).target)
    (hovlp :
      letI := RS.topology
      letI := RS.chartedSpace
      (eChart (RS := RS) r).symm z ∈ (eChart (RS := RS) q).source) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (chartTransitionDerivInCharts (RS := RS) q r) z := by
  letI := RS.topology
  letI := RS.chartedSpace
  set g : ℂ → ℂ := chartTransitionDerivInCharts (RS := RS) q r
  have hC : ContDiffAt ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) g z := by
    simpa [g] using chartTransitionDerivInCharts_contDiffAt (RS := RS) q r z hz_tgt hovlp
  exact @ContDiffAt.restrict_scalars ℝ _ ℂ _ _ ℂ _ _ g z ((⊤ : ℕ∞) : WithTop ℕ∞)
    ℂ _ _ _ IsScalarTower.right _ IsScalarTower.right hC

/-- For fixed chart centers `q`, `r`, the transition Jacobian factor in chart coordinates
is continuous at overlap points. -/
theorem chartTransitionFactorInCharts_continuousAt
    (q r : RS.carrier) (z : ℂ)
    (hz_tgt :
      letI := RS.topology
      letI := RS.chartedSpace
      z ∈ (eChart (RS := RS) r).target)
    (hovlp :
      letI := RS.topology
      letI := RS.chartedSpace
      (eChart (RS := RS) r).symm z ∈ (eChart (RS := RS) q).source) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContinuousAt (chartTransitionFactorInCharts (RS := RS) q r) z := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hderiv_cont : ContinuousAt (chartTransitionDerivInCharts (RS := RS) q r) z :=
    (chartTransitionDerivInCharts_contDiffAt (RS := RS) q r z hz_tgt hovlp).continuousAt
  have hstar_cont :
      ContinuousAt (fun w : ℂ => starRingEnd ℂ w)
        ((chartTransitionDerivInCharts (RS := RS) q r) z) := by
    simpa [Complex.conjCLE_apply] using (Complex.conjCLE.continuousAt :
      ContinuousAt (fun w : ℂ => Complex.conjCLE w)
        ((chartTransitionDerivInCharts (RS := RS) q r) z))
  simpa [chartTransitionFactorInCharts, chartTransitionDerivInCharts, Function.comp] using
    hstar_cont.comp hderiv_cont

/-- For fixed chart centers `q`, `r`, the transition Jacobian factor in chart coordinates
is `C^∞` at overlap points over `ℝ`. -/
theorem chartTransitionFactorInCharts_contDiffAt_real
    (q r : RS.carrier) (z : ℂ)
    (hz_tgt :
      letI := RS.topology
      letI := RS.chartedSpace
      z ∈ (eChart (RS := RS) r).target)
    (hovlp :
      letI := RS.topology
      letI := RS.chartedSpace
      (eChart (RS := RS) r).symm z ∈ (eChart (RS := RS) q).source) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (chartTransitionFactorInCharts (RS := RS) q r) z := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hderivR : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (chartTransitionDerivInCharts (RS := RS) q r) z :=
    chartTransitionDerivInCharts_contDiffAt_real (RS := RS) q r z hz_tgt hovlp
  have hstarR : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : ℂ => starRingEnd ℂ w)
      ((chartTransitionDerivInCharts (RS := RS) q r) z) := by
    simpa [Complex.conjCLE_apply] using
      (Complex.conjCLE.contDiff.contDiffAt :
        ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => Complex.conjCLE w)
          ((chartTransitionDerivInCharts (RS := RS) q r) z))
  simpa [chartTransitionFactorInCharts, chartTransitionDerivInCharts, Function.comp] using
    hstarR.comp z hderivR

/-- On overlap points, fixed-chart transition factor is nonzero. -/
theorem chartTransitionFactorInCharts_ne_zero
    (q r : RS.carrier) (z : ℂ)
    (hz_tgt :
      letI := RS.topology
      letI := RS.chartedSpace
      z ∈ (eChart (RS := RS) r).target)
    (hovlp :
      letI := RS.topology
      letI := RS.chartedSpace
      (eChart (RS := RS) r).symm z ∈ (eChart (RS := RS) q).source) :
    letI := RS.topology
    letI := RS.chartedSpace
    chartTransitionFactorInCharts (RS := RS) q r z ≠ 0 := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hderiv_ne : deriv (chartTransition (RS := RS) q r) z ≠ 0 :=
    chartTransition_deriv_ne_zero (RS := RS) q r z hz_tgt hovlp
  have hstar_ne :
      starRingEnd ℂ (deriv (chartTransition (RS := RS) q r) z) ≠ 0 :=
    (map_ne_zero_iff (starRingEnd ℂ) (starRingEnd ℂ).injective).2 hderiv_ne
  simpa [chartTransitionFactorInCharts] using hstar_ne

/-- Surface-level continuity of the fixed-chart transition factor at an overlap point. -/
theorem chartTransitionFactorByCharts_continuousAt
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
    ContinuousAt (chartTransitionFactorByCharts (RS := RS) q r) p := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hz_tgt : ((eChart (RS := RS) r) p) ∈ (eChart (RS := RS) r).target :=
    (eChart (RS := RS) r).map_source hp_r
  have hovlp : (eChart (RS := RS) r).symm ((eChart (RS := RS) r) p) ∈
      (eChart (RS := RS) q).source := by
    rw [(eChart (RS := RS) r).left_inv hp_r]
    exact hp_q
  have hcoord : ContinuousAt (chartTransitionFactorInCharts (RS := RS) q r)
      ((eChart (RS := RS) r) p) :=
    chartTransitionFactorInCharts_continuousAt (RS := RS) q r ((eChart (RS := RS) r) p)
      hz_tgt hovlp
  have hchart : ContinuousAt (eChart (RS := RS) r) p := by
    simpa [eChart] using (continuousAt_extChartAt' (I := 𝓘(ℂ, ℂ)) (x := r) hp_r)
  simpa [chartTransitionFactorByCharts, Function.comp] using hcoord.comp hchart

/-- Surface-level `C^∞` regularity of the fixed chart transition map
`x ↦ chartTransition q r ((eChart r) x)` at overlap points. -/
theorem chartTransitionByCharts_contMDiffAt
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
      (fun x : RS.carrier => chartTransition (RS := RS) q r ((eChart (RS := RS) r) x)) p := by
  letI := RS.topology
  letI := RS.chartedSpace
  letI : IsManifold 𝓘(ℂ, ℂ) ⊤ RS.carrier := RS.isManifold
  letI : IsManifold 𝓘(ℝ, ℂ) ⊤ RS.carrier := isManifold_real_of_complex
  have hz_tgt : ((eChart (RS := RS) r) p) ∈ (eChart (RS := RS) r).target :=
    (eChart (RS := RS) r).map_source hp_r
  have hovlp : (eChart (RS := RS) r).symm ((eChart (RS := RS) r) p) ∈
      (eChart (RS := RS) q).source := by
    rw [(eChart (RS := RS) r).left_inv hp_r]
    exact hp_q
  have htrans_ana : AnalyticAt ℂ (chartTransition (RS := RS) q r) ((eChart (RS := RS) r) p) :=
    chartTransition_analyticAt (RS := RS) q r ((eChart (RS := RS) r) p) hz_tgt hovlp
  have htransC : ContDiffAt ℂ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (chartTransition (RS := RS) q r) ((eChart (RS := RS) r) p) :=
    htrans_ana.contDiffAt
  have htransR : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (chartTransition (RS := RS) q r) ((eChart (RS := RS) r) p) :=
    @ContDiffAt.restrict_scalars ℝ _ ℂ _ _ ℂ _ _ (chartTransition (RS := RS) q r)
      ((eChart (RS := RS) r) p) ((⊤ : ℕ∞) : WithTop ℕ∞)
      ℂ _ _ _ IsScalarTower.right _ IsScalarTower.right htransC
  have hsmooth : smoothOrder ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    simp [smoothOrder]
  have htransMD : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
      (chartTransition (RS := RS) q r) ((eChart (RS := RS) r) p) :=
    (htransR.of_le hsmooth).contMDiffAt
  have hp_chart : p ∈ (chartAt ℂ r).source := by
    simpa [eChart] using hp_r
  have hchartTop : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (eChart (RS := RS) r) p := by
    simpa [eChart] using
      (contMDiffAt_extChartAt' (I := 𝓘(ℝ, ℂ)) (H := ℂ) (x := r) (x' := p) hp_chart)
  have hchart : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder (eChart (RS := RS) r) p :=
    hchartTop.of_le hsmooth
  simpa [Function.comp] using htransMD.comp p hchart

/-- Surface-level `C^∞` (over `ℝ`) regularity of fixed-chart transition factor at overlap points. -/
theorem chartTransitionFactorByCharts_contMDiffAt
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
      (chartTransitionFactorByCharts (RS := RS) q r) p := by
  letI := RS.topology
  letI := RS.chartedSpace
  letI : IsManifold 𝓘(ℂ, ℂ) ⊤ RS.carrier := RS.isManifold
  letI : IsManifold 𝓘(ℝ, ℂ) ⊤ RS.carrier := isManifold_real_of_complex
  have hz_tgt : ((eChart (RS := RS) r) p) ∈ (eChart (RS := RS) r).target :=
    (eChart (RS := RS) r).map_source hp_r
  have hovlp : (eChart (RS := RS) r).symm ((eChart (RS := RS) r) p) ∈
      (eChart (RS := RS) q).source := by
    rw [(eChart (RS := RS) r).left_inv hp_r]
    exact hp_q
  have hcoordTop : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (chartTransitionFactorInCharts (RS := RS) q r) ((eChart (RS := RS) r) p) :=
    chartTransitionFactorInCharts_contDiffAt_real
      (RS := RS) q r ((eChart (RS := RS) r) p) hz_tgt hovlp
  have hsmooth : smoothOrder ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    simp [smoothOrder]
  have hcoord :
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
        (chartTransitionFactorInCharts (RS := RS) q r) ((eChart (RS := RS) r) p) :=
    (hcoordTop.of_le hsmooth).contMDiffAt
  have hp_chart : p ∈ (chartAt ℂ r).source := by
    simpa [eChart] using hp_r
  have hchartTop : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (eChart (RS := RS) r) p := by
    simpa [eChart] using
      (contMDiffAt_extChartAt' (I := 𝓘(ℝ, ℂ)) (H := ℂ) (x := r) (x' := p) hp_chart)
  have hchart : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder (eChart (RS := RS) r) p :=
    hchartTop.of_le hsmooth
  simpa [chartTransitionFactorByCharts, Function.comp] using hcoord.comp p hchart

/-- Surface-level continuity of the fixed-chart transition factor on chart overlap. -/
theorem chartTransitionFactorByCharts_continuousOn_overlap
    (q r : RS.carrier) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContinuousOn (chartTransitionFactorByCharts (RS := RS) q r)
      ((eChart (RS := RS) r).source ∩ (eChart (RS := RS) q).source) := by
  letI := RS.topology
  letI := RS.chartedSpace
  intro p hp
  exact (chartTransitionFactorByCharts_continuousAt (RS := RS) q r p hp.1 hp.2).continuousWithinAt

/-- Surface-level nonvanishing of fixed-chart transition factor on overlap points. -/
theorem chartTransitionFactorByCharts_ne_zero
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
    chartTransitionFactorByCharts (RS := RS) q r p ≠ 0 := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hz_tgt : ((eChart (RS := RS) r) p) ∈ (eChart (RS := RS) r).target :=
    (eChart (RS := RS) r).map_source hp_r
  have hovlp : (eChart (RS := RS) r).symm ((eChart (RS := RS) r) p) ∈
      (eChart (RS := RS) q).source := by
    rw [(eChart (RS := RS) r).left_inv hp_r]
    exact hp_q
  simpa [chartTransitionFactorByCharts] using
    chartTransitionFactorInCharts_ne_zero (RS := RS) q r ((eChart (RS := RS) r) p) hz_tgt hovlp

/-- Surface-level eventual nonvanishing of the fixed-chart transition factor near an overlap point. -/
theorem chartTransitionFactorByCharts_eventually_ne_zero
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
    ∀ᶠ x in nhds p, chartTransitionFactorByCharts (RS := RS) q r x ≠ 0 := by
  letI := RS.topology
  letI := RS.chartedSpace
  exact (chartTransitionFactorByCharts_continuousAt (RS := RS) q r p hp_r hp_q).eventually_ne
    (chartTransitionFactorByCharts_ne_zero (RS := RS) q r p hp_r hp_q)

/-- Surface-level continuity of the reciprocal fixed-chart transition factor on overlap points. -/
theorem chartTransitionFactorByCharts_inv_continuousAt
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
    ContinuousAt (fun x : RS.carrier => (chartTransitionFactorByCharts (RS := RS) q r x)⁻¹) p := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hfac : ContinuousAt (chartTransitionFactorByCharts (RS := RS) q r) p :=
    chartTransitionFactorByCharts_continuousAt (RS := RS) q r p hp_r hp_q
  have hne :
      chartTransitionFactorByCharts (RS := RS) q r p ≠ 0 :=
    chartTransitionFactorByCharts_ne_zero (RS := RS) q r p hp_r hp_q
  have hinv : ContinuousAt (fun z : ℂ => z⁻¹)
      (chartTransitionFactorByCharts (RS := RS) q r p) :=
    (contDiffAt_inv (𝕜 := ℝ)
      (x := chartTransitionFactorByCharts (RS := RS) q r p)
      (n := smoothOrder) hne).continuousAt
  simpa [Function.comp] using hinv.comp hfac

/-- Surface-level `C^∞` regularity of the reciprocal fixed-chart transition factor on overlaps. -/
theorem chartTransitionFactorByCharts_inv_contMDiffAt
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
      (fun x : RS.carrier => (chartTransitionFactorByCharts (RS := RS) q r x)⁻¹) p := by
  letI := RS.topology
  letI := RS.chartedSpace
  have hfac :
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder
        (chartTransitionFactorByCharts (RS := RS) q r) p :=
    chartTransitionFactorByCharts_contMDiffAt (RS := RS) q r p hp_r hp_q
  have hne :
      chartTransitionFactorByCharts (RS := RS) q r p ≠ 0 :=
    chartTransitionFactorByCharts_ne_zero (RS := RS) q r p hp_r hp_q
  have hinv :
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) smoothOrder (fun z : ℂ => z⁻¹)
        (chartTransitionFactorByCharts (RS := RS) q r p) := by
    exact (contDiffAt_inv ℝ hne).contMDiffAt
  exact hinv.comp p hfac

/-!
## Explicit Riemann-Sphere Formula (Diagnostic Infrastructure)

For the current explicit `chartAt` selector on `RiemannSphere`, centered at `0`,
the transition factor admits a closed form on nonzero finite points.
-/

private theorem riemannSphere_chartAt_zero_tf :
    @chartAt ℂ _ RiemannSphere.carrier RiemannSphere.topology RiemannSphere.chartedSpace
      (((0 : ℂ) : OnePoint ℂ)) = riemannSphereFiniteChart := by
  simpa using (show
    @chartAt ℂ _ RiemannSphere.carrier RiemannSphere.topology RiemannSphere.chartedSpace
      (((0 : ℂ) : OnePoint ℂ)) =
      (if (0 : ℂ) = 0 then riemannSphereFiniteChart else riemannSphereInftyChart) from rfl)

private theorem riemannSphere_chartAt_nonzero_tf (z : ℂ) (hz : z ≠ 0) :
    @chartAt ℂ _ RiemannSphere.carrier RiemannSphere.topology RiemannSphere.chartedSpace
      ((z : ℂ) : OnePoint ℂ) = riemannSphereInftyChart := by
  simpa [hz] using (show
    @chartAt ℂ _ RiemannSphere.carrier RiemannSphere.topology RiemannSphere.chartedSpace
      ((z : ℂ) : OnePoint ℂ) =
      (if z = 0 then riemannSphereFiniteChart else riemannSphereInftyChart) from rfl)

private theorem riemannSphere_transition_finite_infty_eq_inv_at_tf
    (w : ℂ) (hw : w ≠ 0) :
    ((riemannSphereFiniteChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ)
      ((riemannSphereInftyChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ).symm w)) = w⁻¹ := by
  rw [riemannSphereInftyChart_symm_apply w hw, riemannSphereFiniteChart_apply]

private theorem riemannSphere_transition_finite_infty_deriv_at_tf
    (w : ℂ) (hw : w ≠ 0) :
    deriv (fun u : ℂ =>
      ((riemannSphereFiniteChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ)
        ((riemannSphereInftyChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ).symm u))) w =
      -(w ^ 2)⁻¹ := by
  let g : ℂ → ℂ := fun u =>
    ((riemannSphereFiniteChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ)
      ((riemannSphereInftyChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ).symm u))
  have hloc : g =ᶠ[nhds w] fun u : ℂ => u⁻¹ := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds w (norm_pos_iff.mpr hw)) ?_
    intro u hu
    have hu_ne : u ≠ 0 := by
      intro hu0
      have hu_lt : dist u w < ‖w‖ := by simpa [Metric.mem_ball] using hu
      have hfalse : False := by
        simp [hu0, dist_eq_norm, norm_neg] at hu_lt
      exact hfalse.elim
    simpa [g] using riemannSphere_transition_finite_infty_eq_inv_at_tf u hu_ne
  have hderiv_aux : HasDerivAt g (-(w ^ 2)⁻¹) w := by
    exact (hasDerivAt_inv (x := w) hw).congr_of_eventuallyEq hloc
  exact hderiv_aux.deriv

/-- On `RiemannSphere`, centered at `0`, the transition factor at nonzero finite points
has explicit value `-conj(z)^2`. -/
theorem chartTransitionFactor_riemannSphere_zero_nonzero (z : ℂ) (hz : z ≠ 0) :
    letI := RiemannSphere.topology
    letI := RiemannSphere.chartedSpace
    chartTransitionFactor (RS := RiemannSphere) (((0 : ℂ) : OnePoint ℂ)) ((z : ℂ) : OnePoint ℂ) =
      - (starRingEnd ℂ z) ^ 2 := by
  letI := RiemannSphere.topology
  letI := RiemannSphere.chartedSpace
  have hchart0 : chartAt ℂ (((0 : ℂ) : OnePoint ℂ)) = riemannSphereFiniteChart :=
    riemannSphere_chartAt_zero_tf
  have hchartz : chartAt ℂ (((z : ℂ) : OnePoint ℂ)) = riemannSphereInftyChart :=
    riemannSphere_chartAt_nonzero_tf z hz
  have hz_inv : (z⁻¹ : ℂ) ≠ 0 := inv_ne_zero hz
  have hderiv_inv := riemannSphere_transition_finite_infty_deriv_at_tf (w := z⁻¹) hz_inv
  have hderiv_inv' :
      deriv (fun u : ℂ =>
        (riemannSphereFiniteChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ)
          ((riemannSphereInftyChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ).symm u)) (z⁻¹) = -(z * z) := by
    simpa [pow_two, hz, inv_inv, mul_assoc, mul_left_comm, mul_comm] using hderiv_inv
  have hcomp_eq :
      (↑(chartAt ℂ (((0 : ℂ) : OnePoint ℂ))) : OnePoint ℂ → ℂ) ∘
        (↑((chartAt ℂ (((z : ℂ) : OnePoint ℂ))).symm) : ℂ → OnePoint ℂ) =
      (fun u : ℂ =>
        (riemannSphereFiniteChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ)
          ((riemannSphereInftyChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ).symm u)) := by
    funext u
    simp [Function.comp, hchart0, hchartz]
  have hpt_eq :
      ((chartAt ℂ (((z : ℂ) : OnePoint ℂ))) (((z : ℂ) : OnePoint ℂ)) : ℂ) = z⁻¹ := by
    simpa [hchartz] using riemannSphereInftyChart_apply_coe z hz
  have hderiv :
      deriv (chartTransition (RS := RiemannSphere) (((0 : ℂ) : OnePoint ℂ)) (((z : ℂ) : OnePoint ℂ)))
        ((chartAt ℂ (((z : ℂ) : OnePoint ℂ))) (((z : ℂ) : OnePoint ℂ))) = -z ^ 2 := by
    calc
      deriv (chartTransition (RS := RiemannSphere) (((0 : ℂ) : OnePoint ℂ)) (((z : ℂ) : OnePoint ℂ)))
          ((chartAt ℂ (((z : ℂ) : OnePoint ℂ))) (((z : ℂ) : OnePoint ℂ)))
          = deriv
              ((↑(chartAt ℂ (((0 : ℂ) : OnePoint ℂ))) : OnePoint ℂ → ℂ) ∘
                (↑((chartAt ℂ (((z : ℂ) : OnePoint ℂ))).symm) : ℂ → OnePoint ℂ))
              ((chartAt ℂ (((z : ℂ) : OnePoint ℂ))) (((z : ℂ) : OnePoint ℂ))) := by
            rfl
      _ = deriv (fun u : ℂ =>
            (riemannSphereFiniteChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ)
              ((riemannSphereInftyChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ).symm u)) (z⁻¹) := by
            rw [hcomp_eq, hpt_eq]
      _ = -(z * z) := hderiv_inv'
      _ = -z ^ 2 := by simp [pow_two]
  have hstar := congrArg (starRingEnd ℂ) hderiv
  simpa [chartTransitionFactor, pow_two, map_mul, map_neg] using hstar

/-- Diagnostic result about the selector-dependent transition-factor expression:
with the current explicit `chartAt` selector on `RiemannSphere`, the transition factor
centered at `0` is not continuous at `0`.
This does **not** assert any failure of manifold smoothness of `RiemannSphere`. -/
theorem not_continuousAt_chartTransitionFactor_riemannSphere_zero :
    letI := RiemannSphere.topology
    letI := RiemannSphere.chartedSpace
    ¬ ContinuousAt
      (chartTransitionFactor (RS := RiemannSphere) (((0 : ℂ) : OnePoint ℂ)))
      (((0 : ℂ) : OnePoint ℂ)) := by
  letI := RiemannSphere.topology
  letI := RiemannSphere.chartedSpace
  intro hcont
  let p0 : OnePoint ℂ := (((0 : ℂ) : OnePoint ℂ))
  let F : OnePoint ℂ → ℂ := chartTransitionFactor (RS := RiemannSphere) p0
  let seqC : ℕ → ℂ := fun n => (n : ℂ)⁻¹
  let seqP : ℕ → OnePoint ℂ := fun n => (seqC n : OnePoint ℂ)
  let seqV : ℕ → ℂ := fun n => -(starRingEnd ℂ (seqC n)) ^ 2

  have hseqR : Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹ : ℝ)) Filter.atTop (nhds (0 : ℝ)) :=
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  have hseqC' : Filter.Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : ℂ)) Filter.atTop (nhds (0 : ℂ)) :=
    (Complex.continuous_ofReal.continuousAt.tendsto.comp hseqR)
  have hseqC : Filter.Tendsto seqC Filter.atTop (nhds (0 : ℂ)) := by
    simpa [seqC] using hseqC'
  have hseqP : Filter.Tendsto seqP Filter.atTop (nhds p0) := by
    simpa [seqP, p0] using (OnePoint.continuous_coe.continuousAt.tendsto.comp hseqC)

  have hseqV0 : Filter.Tendsto seqV Filter.atTop (nhds (0 : ℂ)) := by
    have hcontV : Continuous (fun z : ℂ => -(starRingEnd ℂ z) ^ 2) := by
      continuity
    have : Filter.Tendsto (fun n : ℕ => (fun z : ℂ => -(starRingEnd ℂ z) ^ 2) (seqC n))
        Filter.atTop (nhds ((fun z : ℂ => -(starRingEnd ℂ z) ^ 2) 0)) :=
      hcontV.continuousAt.tendsto.comp hseqC
    simpa [seqV] using this

  have hnat_ne0 : ∀ᶠ n : ℕ in Filter.atTop, (n : ℂ) ≠ 0 := by
    have hnat : ∀ᶠ n : ℕ in Filter.atTop, n ≠ 0 := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨1, ?_⟩
      intro n hn
      exact Nat.ne_of_gt (lt_of_lt_of_le (Nat.succ_pos 0) hn)
    exact hnat.mono (fun n hn => by exact_mod_cast hn)

  have hF_eq_seqV : (fun n : ℕ => F (seqP n)) =ᶠ[Filter.atTop] seqV := by
    refine hnat_ne0.mono ?_
    intro n hn
    have hseqC_ne : seqC n ≠ 0 := by
      simpa [seqC] using inv_ne_zero hn
    simpa [F, p0, seqP, seqV, seqC] using
      chartTransitionFactor_riemannSphere_zero_nonzero (z := seqC n) hseqC_ne

  have hF0 : Filter.Tendsto (fun n : ℕ => F (seqP n)) Filter.atTop (nhds (0 : ℂ)) := by
    exact Filter.Tendsto.congr' hF_eq_seqV.symm hseqV0

  have hFp0 : F p0 = (1 : ℂ) := by
    simpa [F, p0] using chartTransitionFactor_center (RS := RiemannSphere) p0
  have hF1 : Filter.Tendsto (fun n : ℕ => F (seqP n)) Filter.atTop (nhds (1 : ℂ)) := by
    have htmp : Filter.Tendsto (fun n : ℕ => F (seqP n)) Filter.atTop (nhds (F p0)) :=
      hcont.tendsto.comp hseqP
    simpa [hFp0] using htmp

  have h01 : (0 : ℂ) = 1 := tendsto_nhds_unique hF0 hF1
  exact zero_ne_one h01

/-- Consequently, the same selector-dependent centered transition factor is not
`ContMDiffAt` at `0` for any regularity order. -/
theorem not_contMDiffAt_chartTransitionFactor_riemannSphere_zero (n : WithTop ℕ∞) :
    letI := RiemannSphere.topology
    letI := RiemannSphere.chartedSpace
    ¬ ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n
      (chartTransitionFactor (RS := RiemannSphere) (((0 : ℂ) : OnePoint ℂ)))
      (((0 : ℂ) : OnePoint ℂ)) := by
  letI := RiemannSphere.topology
  letI := RiemannSphere.chartedSpace
  intro h
  exact not_continuousAt_chartTransitionFactor_riemannSphere_zero (h.continuousAt)

end RiemannSurfaces.Analytic.Infrastructure
