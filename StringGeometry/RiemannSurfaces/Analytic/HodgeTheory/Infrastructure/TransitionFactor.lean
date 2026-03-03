import StringGeometry.RiemannSurfaces.Analytic.Helpers.ChartTransition
import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.Infrastructure.ChartSelection

/-!
# Transition-Factor Infrastructure

Reusable lemmas for the chart-transition Jacobian factor
`p ↦ star(deriv (chartTransition p0 p) ((chartAt p) p))`.

This factor appears in chart-change formulas for local `(0,1)` coefficients.
-/

namespace RiemannSurfaces.Analytic.Infrastructure

open Complex Topology
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

end RiemannSurfaces.Analytic.Infrastructure
