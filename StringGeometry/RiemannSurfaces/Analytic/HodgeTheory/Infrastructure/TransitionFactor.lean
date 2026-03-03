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
