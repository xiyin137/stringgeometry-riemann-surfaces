import StringGeometry.RiemannSurfaces.Analytic.Basic

/-!
# Chart Selection Infrastructure

Reusable lemmas about local/global stability of `chartAt` selections.

These are small but useful bridges when a proof needs eventual equality of chart
choices near a point.
-/

namespace RiemannSurfaces.Analytic.Infrastructure

open Topology

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

end RiemannSurfaces.Analytic.Infrastructure
