import StringGeometry.RiemannSurfaces.Analytic.Basic

/-!
# Chart Selection Infrastructure

Reusable lemmas about local/global stability of `chartAt` selections.

These are small but useful bridges when a proof needs eventual equality of chart
choices near a point.
-/

namespace RiemannSurfaces.Analytic.Infrastructure

open Topology
open OnePoint

/-- Local chart-selection stability: `chartAt` is eventually constant at every point. -/
def ChartAtLocallyConstant (RS : RiemannSurface) : Prop :=
  letI := RS.topology
  letI := RS.chartedSpace
  ∀ p0 : RS.carrier,
    (fun p : RS.carrier => @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p) =ᶠ[nhds p0]
      (fun _ : RS.carrier => @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p0)

/-- If chart selection is globally constant at a center chart, it is eventually equal
near that center. -/
theorem chartAt_eventuallyEq_of_forall_eq
    {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (p0 : M)
    (hconst : ∀ p : M, @chartAt H _ M _ _ p = @chartAt H _ M _ _ p0) :
    (fun p : M => @chartAt H _ M _ _ p) =ᶠ[nhds p0]
      (fun _ : M => @chartAt H _ M _ _ p0) := by
  exact Filter.Eventually.of_forall hconst

/-- On a model space with the `chartedSpaceSelf` instance, `chartAt` is globally the
identity chart, so it is eventually constant near every point. -/
theorem chartAt_eventuallyEq_center_self
    {H : Type*} [TopologicalSpace H] (p0 : H) :
    (fun p : H => @chartAt H _ H _ _ p) =ᶠ[nhds p0]
      (fun _ : H => @chartAt H _ H _ _ p0) := by
  refine Filter.Eventually.of_forall ?_
  intro p
  simpa using (chartAt_self_eq (H := H) (x := p)).trans
    (chartAt_self_eq (H := H) (x := p0)).symm

/-- `ComplexPlane` inherits model-space chart stability (`chartAt = refl`). -/
theorem chartAt_eventuallyEq_center_complexPlane
    (p0 : ComplexPlane.carrier) :
    letI := ComplexPlane.topology
    letI := ComplexPlane.chartedSpace
    (fun p : ComplexPlane.carrier =>
      @chartAt ℂ _ ComplexPlane.carrier ComplexPlane.topology ComplexPlane.chartedSpace p)
      =ᶠ[nhds p0]
    (fun _ : ComplexPlane.carrier =>
      @chartAt ℂ _ ComplexPlane.carrier ComplexPlane.topology ComplexPlane.chartedSpace p0) := by
  letI := ComplexPlane.topology
  letI := ComplexPlane.chartedSpace
  simpa using chartAt_eventuallyEq_center_self (H := ℂ) (p0 := (p0 : ℂ))

/-- `ComplexPlane` satisfies local chart-selection stability. -/
theorem chartAtLocallyConstant_complexPlane : ChartAtLocallyConstant ComplexPlane := by
  intro p0
  simpa using chartAt_eventuallyEq_center_complexPlane p0

/-- On `RiemannSphere`, `chartAt` is eventually constant at each nonzero finite point.

This is a local chart-selection stability statement away from the pole-switch point `0`
of the explicit selector. -/
theorem chartAt_eventuallyEq_center_riemannSphere_coe_of_ne_zero
    (a : ℂ) (ha : a ≠ 0) :
    letI := RiemannSphere.topology
    letI := RiemannSphere.chartedSpace
    (fun p : RiemannSphere.carrier =>
      @chartAt ℂ _ RiemannSphere.carrier RiemannSphere.topology RiemannSphere.chartedSpace p)
      =ᶠ[nhds ((a : ℂ) : OnePoint ℂ)]
    (fun _ : RiemannSphere.carrier =>
      @chartAt ℂ _ RiemannSphere.carrier RiemannSphere.topology RiemannSphere.chartedSpace
        ((a : ℂ) : OnePoint ℂ)) := by
  letI := RiemannSphere.topology
  letI := RiemannSphere.chartedSpace
  have hε : 0 < ‖a‖ / 2 := by
    exact half_pos (norm_pos_iff.mpr ha)
  have hpre :
      {z : ℂ |
        @chartAt ℂ _ RiemannSphere.carrier RiemannSphere.topology RiemannSphere.chartedSpace
          ((z : ℂ) : OnePoint ℂ) =
        @chartAt ℂ _ RiemannSphere.carrier RiemannSphere.topology RiemannSphere.chartedSpace
          ((a : ℂ) : OnePoint ℂ)} ∈ nhds a := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds a hε) ?_
    intro z hz
    have hz_ne : z ≠ 0 := by
      intro hz0
      have hzlt : dist (0 : ℂ) a < ‖a‖ / 2 := by
        simpa [hz0] using hz
      have hlt : ‖a‖ < ‖a‖ / 2 := by
        simpa [dist_eq_norm, norm_neg] using hzlt
      linarith
    change
      (if z = 0 then riemannSphereFiniteChart else riemannSphereInftyChart) =
        (if a = 0 then riemannSphereFiniteChart else riemannSphereInftyChart)
    simp [hz_ne, ha]
  have hset :
      {p : OnePoint ℂ |
        @chartAt ℂ _ RiemannSphere.carrier RiemannSphere.topology RiemannSphere.chartedSpace p =
        @chartAt ℂ _ RiemannSphere.carrier RiemannSphere.topology RiemannSphere.chartedSpace
          ((a : ℂ) : OnePoint ℂ)} ∈ nhds (((a : ℂ) : OnePoint ℂ)) := by
    simpa [OnePoint.nhds_coe_eq] using hpre
  exact hset

/-!
## Negative Model Example

`ChartAtLocallyConstant` is a strong chart-selection property. It holds for
`ComplexPlane`, but fails for `RiemannSphere` with the current explicit atlas:
the selector uses `riemannSphereFiniteChart` at `0` and
`riemannSphereInftyChart` at every nonzero finite point.
-/

private theorem riemannSphereInftyChart_ne_finiteChart :
    riemannSphereInftyChart ≠ riemannSphereFiniteChart := by
  intro hEq
  have hmem : (∞ : OnePoint ℂ) ∈ riemannSphereInftyChart.source := by
    simp [riemannSphereInftyChart]
  have hmem' : (∞ : OnePoint ℂ) ∈ riemannSphereFiniteChart.source := by
    simpa [hEq] using hmem
  simp [riemannSphereFiniteChart, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] at hmem'

private theorem riemannSphere_chartAt_zero :
    @chartAt ℂ _ RiemannSphere.carrier RiemannSphere.topology RiemannSphere.chartedSpace
      (((0 : ℂ) : OnePoint ℂ)) = riemannSphereFiniteChart := by
  simpa using (show
    @chartAt ℂ _ RiemannSphere.carrier RiemannSphere.topology RiemannSphere.chartedSpace
      (((0 : ℂ) : OnePoint ℂ)) =
      (if (0 : ℂ) = 0 then riemannSphereFiniteChart else riemannSphereInftyChart) from rfl)

private theorem riemannSphere_chartAt_coe_ne_zero (a : ℂ) (ha : a ≠ 0) :
    @chartAt ℂ _ RiemannSphere.carrier RiemannSphere.topology RiemannSphere.chartedSpace
      ((a : ℂ) : OnePoint ℂ) ≠
    @chartAt ℂ _ RiemannSphere.carrier RiemannSphere.topology RiemannSphere.chartedSpace
      (((0 : ℂ) : OnePoint ℂ)) := by
  rw [show @chartAt ℂ _ RiemannSphere.carrier RiemannSphere.topology RiemannSphere.chartedSpace
      ((a : ℂ) : OnePoint ℂ) =
      (if a = 0 then riemannSphereFiniteChart else riemannSphereInftyChart) from rfl]
  rw [riemannSphere_chartAt_zero]
  simpa [ha] using riemannSphereInftyChart_ne_finiteChart

private theorem riemannSphere_chartAt_eq_zero_coe_preimage :
    {a : ℂ |
      @chartAt ℂ _ RiemannSphere.carrier RiemannSphere.topology RiemannSphere.chartedSpace
        ((a : ℂ) : OnePoint ℂ) =
      @chartAt ℂ _ RiemannSphere.carrier RiemannSphere.topology RiemannSphere.chartedSpace
        (((0 : ℂ) : OnePoint ℂ))} = {(0 : ℂ)} := by
  ext a
  by_cases ha : a = 0
  · subst ha
    simp
  · simp [ha, riemannSphere_chartAt_coe_ne_zero]

private theorem singleton_zero_not_mem_nhds_complex :
    ({(0 : ℂ)} : Set ℂ) ∉ nhds (0 : ℂ) := by
  intro hzero_nhds
  rcases Metric.mem_nhds_iff.mp hzero_nhds with ⟨ε, hεpos, hεsub⟩
  have hhalf_pos : 0 < ε / 2 := by linarith
  have hhalf_mem : (((ε / 2 : ℝ) : ℂ)) ∈ Metric.ball (0 : ℂ) ε := by
    have hlt : ε / 2 < ε := by linarith
    simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, abs_of_pos hεpos] using hlt
  have hhalf_zero : (((ε / 2 : ℝ) : ℂ)) = 0 := hεsub hhalf_mem
  have hhalf_ne : (((ε / 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt hhalf_pos)
  exact hhalf_ne hhalf_zero

/-- `RiemannSphere` does **not** satisfy local chart-selection stability at `0`
for the current explicit two-chart `chartAt` selector. -/
theorem not_chartAtLocallyConstant_riemannSphere :
    ¬ ChartAtLocallyConstant RiemannSphere := by
  intro h
  have h0 := h (((0 : ℂ) : OnePoint ℂ))
  have hset :
      {p : OnePoint ℂ |
        @chartAt ℂ _ RiemannSphere.carrier RiemannSphere.topology RiemannSphere.chartedSpace p =
        @chartAt ℂ _ RiemannSphere.carrier RiemannSphere.topology RiemannSphere.chartedSpace
          (((0 : ℂ) : OnePoint ℂ))} ∈ nhds (((0 : ℂ) : OnePoint ℂ)) := h0
  have hpre :
      {a : ℂ |
        @chartAt ℂ _ RiemannSphere.carrier RiemannSphere.topology RiemannSphere.chartedSpace
          ((a : ℂ) : OnePoint ℂ) =
        @chartAt ℂ _ RiemannSphere.carrier RiemannSphere.topology RiemannSphere.chartedSpace
          (((0 : ℂ) : OnePoint ℂ))} ∈ nhds (0 : ℂ) := by
    simpa [OnePoint.nhds_coe_eq] using hset
  have hzero_nhds : ({(0 : ℂ)} : Set ℂ) ∈ nhds (0 : ℂ) := by
    simpa [riemannSphere_chartAt_eq_zero_coe_preimage] using hpre
  exact singleton_zero_not_mem_nhds_complex hzero_nhds

end RiemannSurfaces.Analytic.Infrastructure
