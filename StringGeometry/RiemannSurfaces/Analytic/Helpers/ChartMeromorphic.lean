import StringGeometry.RiemannSurfaces.Analytic.Basic
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Separation.Connected

/-!
# Chart-Local Meromorphic Functions on Riemann Surfaces

This file defines chart-local meromorphic functions and their order theory,
bridging between our abstract `AnalyticMeromorphicFunction` (AMF) and
Mathlib's `MeromorphicAt` in charts.

## Key Definitions

* `chartRep` — The chart representation of a function: `f ∘ (extChartAt p).symm`
* `chartPt` — The chart image of a point: `(extChartAt p) p`
* `IsChartMeromorphic` — `f` is MeromorphicAt in every chart
* `chartOrderAt` — The meromorphic order in charts

## Key Results

* `chartMeromorphic_sum` — Sum of chart-meromorphic functions is chart-meromorphic
* `chartOrderAt_add_ge` — Order of sum ≥ min of orders (from Mathlib)
* `chartMeromorphic_argument_principle` — Sum of orders = 0 (moved to ArgumentPrinciple.lean)

## References

* Mathlib.Analysis.Meromorphic — MeromorphicAt, meromorphicOrderAt
-/

namespace RiemannSurfaces.Analytic

open Complex Topology
open scoped Manifold

/-!
## Chart Representation

Utility functions for working with chart representations of functions on Riemann surfaces.
-/

variable {RS : RiemannSurface}

/-- The chart representation of a function `f : RS.carrier → ℂ` at a point `p`.
    This is `f ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm : ℂ → ℂ`. -/
noncomputable def chartRep (f : RS.carrier → ℂ) (p : RS.carrier) : ℂ → ℂ :=
  letI := RS.topology
  letI := RS.chartedSpace
  f ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm

/-- The chart image of a point p on a Riemann surface. -/
noncomputable def chartPt (p : RS.carrier) : ℂ :=
  letI := RS.topology
  letI := RS.chartedSpace
  extChartAt 𝓘(ℂ, ℂ) p p

/-!
## Chart-Meromorphic Functions

A function `f : RS.carrier → ℂ` is chart-meromorphic if it is `MeromorphicAt`
in every chart. This connects the manifold-level function to Mathlib's meromorphic theory.
-/

/-- A function `f : RS.carrier → ℂ` is chart-meromorphic if for every point `p`,
    the chart representation `f ∘ (extChartAt p).symm` is `MeromorphicAt` at `chartPt p`.

    This is the correct notion of meromorphicity on a manifold: the chart representation
    should be meromorphic in the classical sense at every point. -/
def IsChartMeromorphic (f : RS.carrier → ℂ) : Prop :=
  ∀ p : RS.carrier, MeromorphicAt (chartRep f p) (chartPt (RS := RS) p)

/-- The chart-local meromorphic order at a point.
    Uses Mathlib's `meromorphicOrderAt` applied to the chart representation. -/
noncomputable def chartOrderAt (f : RS.carrier → ℂ) (p : RS.carrier) : WithTop ℤ :=
  meromorphicOrderAt (chartRep f p) (chartPt (RS := RS) p)

/-!
## Arithmetic of Chart-Meromorphic Functions

Sums and scalar multiples of chart-meromorphic functions are chart-meromorphic.
-/

/-- A constant function is chart-meromorphic. -/
theorem chartMeromorphic_const (c : ℂ) : IsChartMeromorphic (RS := RS) (fun _ => c) := by
  intro p
  exact MeromorphicAt.const c _

/-- The sum of two chart-meromorphic functions is chart-meromorphic. -/
theorem chartMeromorphic_add {f g : RS.carrier → ℂ}
    (hf : IsChartMeromorphic f) (hg : IsChartMeromorphic g) :
    IsChartMeromorphic (fun x => f x + g x) := by
  intro p
  have : chartRep (fun x => f x + g x) p = chartRep f p + chartRep g p := by
    ext z; simp [chartRep, Function.comp]
  rw [this]
  exact (hf p).add (hg p)

/-- A scalar multiple of a chart-meromorphic function is chart-meromorphic. -/
theorem chartMeromorphic_smul (c : ℂ) {f : RS.carrier → ℂ}
    (hf : IsChartMeromorphic f) :
    IsChartMeromorphic (fun x => c * f x) := by
  intro p
  have : chartRep (fun x => c * f x) p = fun z => c * chartRep f p z := by
    ext z; simp [chartRep, Function.comp]
  rw [this]
  exact (MeromorphicAt.const c _).mul (hf p)

/-- A finite sum of chart-meromorphic functions is chart-meromorphic. -/
theorem chartMeromorphic_finset_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → RS.carrier → ℂ)
    (hf : ∀ i ∈ s, IsChartMeromorphic (f i)) :
    IsChartMeromorphic (fun x => s.sum (fun i => f i x)) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact chartMeromorphic_const 0
  | @insert a s ha ih =>
    have heq : (fun x => ∑ i ∈ insert a s, f i x) =
        (fun x => f a x + ∑ i ∈ s, f i x) := by
      ext x; exact Finset.sum_insert ha
    intro p; rw [show chartRep (fun x => ∑ i ∈ insert a s, f i x) p =
        chartRep (fun x => f a x + ∑ i ∈ s, f i x) p by
      simp only [heq]]
    have hfa : IsChartMeromorphic (f a) := hf a (Finset.mem_insert_self _ _)
    have hrest : IsChartMeromorphic (fun x => s.sum (fun i => f i x)) :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    exact (chartMeromorphic_add hfa hrest) p

/-- A linear combination Σ cᵢ · fᵢ of chart-meromorphic functions is chart-meromorphic. -/
theorem chartMeromorphic_linear_combination {n : ℕ}
    (f : Fin n → RS.carrier → ℂ) (c : Fin n → ℂ)
    (hf : ∀ i, IsChartMeromorphic (f i)) :
    IsChartMeromorphic (fun x => Finset.univ.sum (fun i => c i * f i x)) := by
  apply chartMeromorphic_finset_sum
  intro i _
  exact chartMeromorphic_smul (c i) (hf i)

/-!
## Order Properties

Properties of chartOrderAt under arithmetic operations.
-/

/-- The order of a sum is at least the minimum of the individual orders. -/
theorem chartOrderAt_add_ge {f g : RS.carrier → ℂ}
    (hf : IsChartMeromorphic f) (hg : IsChartMeromorphic g)
    (p : RS.carrier) :
    min (chartOrderAt f p) (chartOrderAt g p) ≤
      chartOrderAt (fun x => f x + g x) p := by
  simp only [chartOrderAt]
  have hrep : chartRep (fun x => f x + g x) p = chartRep f p + chartRep g p := by
    ext z; simp [chartRep, Function.comp]
  rw [hrep]
  exact meromorphicOrderAt_add (hf p) (hg p)

/-- The chart order of a scalar multiple c * f is at least the chart order of f.
    When c = 0, the function is identically 0 (order = ⊤ ≥ anything).
    When c ≠ 0, the order is unchanged. -/
theorem chartOrderAt_smul_ge (c : ℂ) {f : RS.carrier → ℂ}
    (hf : IsChartMeromorphic f) (p : RS.carrier) :
    chartOrderAt f p ≤ chartOrderAt (fun x => c * f x) p := by
  by_cases hc : c = 0
  · -- c = 0: function is identically 0, order = ⊤
    subst hc
    have hzero_fun : (fun x => (0 : ℂ) * f x) = fun _ => (0 : ℂ) := by
      ext x
      simp
    rw [hzero_fun]
    simp only [chartOrderAt]
    have htop : meromorphicOrderAt (chartRep (RS := RS) (fun _ => (0 : ℂ)) p)
        (chartPt (RS := RS) p) = ⊤ := by
      exact meromorphicOrderAt_eq_top_iff.mpr
        (Filter.Eventually.of_forall fun z => by simp [chartRep, Function.comp])
    rw [htop]
    cases h : meromorphicOrderAt (chartRep (RS := RS) f p) (chartPt (RS := RS) p) with
    | top =>
      simp
    | coe m =>
      exact le_of_lt (WithTop.coe_lt_top m)
  · -- c ≠ 0: order(c * f) = order(c) + order(f) = 0 + order(f) = order(f)
    simp only [chartOrderAt]
    have hrep : chartRep (fun x => c * f x) p = (fun _ => c) * chartRep f p := by
      ext z; simp [chartRep, Function.comp]
    rw [hrep, meromorphicOrderAt_mul (MeromorphicAt.const c _) (hf p)]
    simp [meromorphicOrderAt_const, hc]

/-- chartRep f p evaluated at chartPt p equals f p. -/
theorem chartRep_apply_chartPt (f : RS.carrier → ℂ) (p : RS.carrier) :
    chartRep f p (chartPt (RS := RS) p) = f p := by
  letI := RS.topology
  letI := RS.chartedSpace
  simp only [chartRep, chartPt, Function.comp_apply]
  congr 1
  exact (extChartAt 𝓘(ℂ, ℂ) p).left_inv (mem_extChartAt_source p)

/-- If f is 0 at a point and chart-continuous there, chartOrderAt is positive.
    Needs ContinuousAt so that f(p) = 0 implies f tends to 0 near p in charts. -/
theorem chartOrderAt_pos_of_zero {f : RS.carrier → ℂ}
    (hf : IsChartMeromorphic f) (p : RS.carrier) (hfp : f p = 0)
    (hcont : ContinuousAt (chartRep (RS := RS) f p) (chartPt (RS := RS) p)) :
    0 < chartOrderAt f p := by
  simp only [chartOrderAt]
  rw [← tendsto_zero_iff_meromorphicOrderAt_pos (hf p)]
  have heq : chartRep f p (chartPt (RS := RS) p) = 0 := by
    rw [chartRep_apply_chartPt]; exact hfp
  rw [show (0 : ℂ) = chartRep f p (chartPt (RS := RS) p) from heq.symm]
  exact hcont.tendsto.mono_left nhdsWithin_le_nhds

/-- If f is chart-meromorphic and ContinuousAt in charts and f(p) ≠ 0,
    then chartOrderAt f p = 0.

    Proof: ContinuousAt + f(p) ≠ 0 implies f(z) → f(p) ≠ 0, so f is eventually
    nonzero (ruling out order = ⊤) and doesn't tend to 0 (ruling out order > 0).
    The order also can't be negative since that would mean f → ∞, contradicting
    ContinuousAt. -/
theorem chartOrderAt_eq_zero_of_continuousAt_ne_zero {f : RS.carrier → ℂ}
    (hf : IsChartMeromorphic f) (p : RS.carrier)
    (hcont : ContinuousAt (chartRep (RS := RS) f p) (chartPt (RS := RS) p))
    (hne : f p ≠ 0) :
    chartOrderAt (RS := RS) f p = 0 := by
  letI := RS.topology
  letI := RS.chartedSpace
  simp only [chartOrderAt]
  have hval : chartRep f p (chartPt (RS := RS) p) ≠ 0 := by
    rw [chartRep_apply_chartPt]; exact hne
  have hmer := hf p
  -- Step 1: order ≤ 0 (not positive)
  -- If order > 0, Tendsto to 0, but ContinuousAt gives Tendsto to f(p) ≠ 0
  have h_not_pos : ¬(0 < meromorphicOrderAt (chartRep f p) (chartPt (RS := RS) p)) := by
    intro hpos
    have h0 := (tendsto_zero_iff_meromorphicOrderAt_pos hmer).mpr hpos
    have hv : Filter.Tendsto (chartRep f p) (nhdsWithin (chartPt (RS := RS) p)
        {chartPt (RS := RS) p}ᶜ) (nhds (chartRep f p (chartPt (RS := RS) p))) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    exact hval (tendsto_nhds_unique hv h0)
  -- Step 2: order ≥ 0 (no pole when continuous)
  have h_nonneg : 0 ≤ meromorphicOrderAt (chartRep f p) (chartPt (RS := RS) p) := by
    -- If order < 0, the function has a pole → unbounded → contradicts ContinuousAt
    by_contra h_not_nonneg
    have h_neg : meromorphicOrderAt (chartRep f p) (chartPt (RS := RS) p) < 0 :=
      lt_of_not_ge h_not_nonneg
    have h_ne_top : meromorphicOrderAt (chartRep f p) (chartPt (RS := RS) p) ≠ ⊤ := by
      intro htop; rw [htop] at h_neg; exact (not_lt.mpr le_top) h_neg
    set z₀ := chartPt (RS := RS) p
    set F := chartRep f p
    set n := (meromorphicOrderAt F z₀).untop₀
    -- n < 0 (from h_neg and h_ne_top via coe_untop₀_of_ne_top)
    have hn_neg : n < 0 := by
      subst n
      have h_neg' : ((meromorphicOrderAt F z₀).untop₀ : WithTop ℤ) < (0 : WithTop ℤ) := by
        simpa [WithTop.coe_untop₀_of_ne_top h_ne_top] using h_neg
      exact WithTop.coe_lt_coe.mp h_neg'
    -- Get representation: F =ᶠ[𝓝[≠] z₀] (z - z₀)^n • g(z) with g analytic, g(z₀) ≠ 0
    obtain ⟨g, hg_ana, hg_ne, hg_eq⟩ := (meromorphicOrderAt_ne_top_iff hmer).mp h_ne_top
    -- F is bounded near z₀ (ContinuousAt)
    have hF_bdd : ∃ C : ℝ, ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, ‖F z‖ ≤ C := by
      refine ⟨‖F z₀‖ + 1, ?_⟩
      apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
      exact (hcont.norm.tendsto.eventually (Metric.ball_mem_nhds ‖F z₀‖ one_pos)).mono
        fun z hz => by rw [Real.dist_eq] at hz; linarith [(abs_lt.mp hz).2]
    obtain ⟨C, hC⟩ := hF_bdd
    -- g continuous at z₀, g(z₀) ≠ 0 ⟹ ‖g z‖ ≥ ‖g z₀‖/2 near z₀
    have hg_cont := hg_ana.continuousAt
    have hg_pos : (0 : ℝ) < ‖g z₀‖ := norm_pos_iff.mpr hg_ne
    have hg_half_pos : (0 : ℝ) < ‖g z₀‖ / 2 := half_pos hg_pos
    have hg_near : ∀ᶠ z in nhds z₀, ‖g z₀‖ / 2 ≤ ‖g z‖ :=
      (hg_cont.norm.tendsto.eventually (Metric.ball_mem_nhds ‖g z₀‖ hg_half_pos)).mono
        fun z hz => by rw [Real.dist_eq] at hz; linarith [(abs_lt.mp hz).1]
    -- (· - z₀) maps nhdsWithin z₀ {z₀}ᶜ → nhdsWithin 0 {0}ᶜ
    -- (following Mathlib.Analysis.Meromorphic.Order pattern)
    have h_sub : Filter.Tendsto (fun z => z - z₀) (nhdsWithin z₀ {z₀}ᶜ)
        (nhdsWithin 0 {(0 : ℂ)}ᶜ) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : ContinuousWithinAt (fun z => z - z₀) {z₀}ᶜ z₀ :=
          ContinuousAt.continuousWithinAt (by fun_prop)
        simpa using this.tendsto
      · filter_upwards [self_mem_nhdsWithin] with y hy
        simpa [sub_eq_zero] using hy
    -- ‖(z-z₀)^n‖ → ∞ near z₀ (n < 0)
    have h_norm_atTop : Filter.Tendsto (fun z => ‖(z - z₀) ^ n‖)
        (nhdsWithin z₀ {z₀}ᶜ) Filter.atTop :=
      (tendsto_norm_cobounded_atTop.comp
        ((tendsto_zpow_nhdsNE_zero_cobounded hn_neg).comp h_sub))
    have h_unbdd : ∀ M : ℝ, ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, M ≤ ‖(z - z₀) ^ n‖ :=
      fun M => Filter.tendsto_atTop.mp h_norm_atTop M
    -- Combine all bounds and extract a witness for contradiction
    have h_big := (h_unbdd (2 * (C + 1) / (‖g z₀‖ / 2))).and
      (hg_near.filter_mono nhdsWithin_le_nhds) |>.and hC |>.and
      (hg_eq.mono fun z hz => hz)
    obtain ⟨z, ⟨⟨⟨hz_zpow, hz_g⟩, hz_bdd⟩, hz_eq⟩⟩ := h_big.exists
    rw [hz_eq] at hz_bdd
    have h1 : 2 * (C + 1) ≤ ‖(z - z₀) ^ n‖ * ‖g z‖ := by
      calc 2 * (C + 1)
          = 2 * (C + 1) / (‖g z₀‖ / 2) * (‖g z₀‖ / 2) :=
            (div_mul_cancel₀ _ hg_half_pos.ne').symm
        _ ≤ ‖(z - z₀) ^ n‖ * ‖g z‖ :=
            mul_le_mul hz_zpow hz_g hg_half_pos.le (norm_nonneg _)
    have h2 : ‖(z - z₀) ^ n • g z‖ = ‖(z - z₀) ^ n‖ * ‖g z‖ := norm_smul _ _
    linarith [norm_nonneg ((z - z₀) ^ n • g z)]
  -- Combine: not_pos gives ≤ 0, nonneg gives ≥ 0
  exact le_antisymm (not_lt.mp h_not_pos) h_nonneg

/-- At a point where the chart representation is eventually zero
    (in a punctured neighborhood), the chart order is ⊤. -/
theorem chartOrderAt_eq_top_of_eventually_zero {f : RS.carrier → ℂ}
    (p : RS.carrier)
    (hev : ∀ᶠ z in nhdsWithin (chartPt (RS := RS) p) {chartPt (RS := RS) p}ᶜ,
      chartRep (RS := RS) f p z = 0) :
    chartOrderAt (RS := RS) f p = ⊤ := by
  simp only [chartOrderAt]
  exact meromorphicOrderAt_eq_top_iff.mpr hev

/-- If g = 0 on a full manifold neighborhood of q, then chartOrderAt g q = ⊤.
    Uses: continuity of (extChartAt q).symm pulls the zero-neighborhood back to charts. -/
theorem chartOrderAt_eq_top_of_zero_on_nhd {g : RS.carrier → ℂ} {q : RS.carrier}
    (h : ∀ᶠ z in @nhds RS.carrier RS.topology q, g z = 0) :
    chartOrderAt (RS := RS) g q = ⊤ := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  apply chartOrderAt_eq_top_of_eventually_zero
  -- Need: ∀ᶠ z in 𝓝[≠] (chartPt q), chartRep g q z = 0
  apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
  -- Goal: ∀ᶠ z in 𝓝 (chartPt q), chartRep g q z = 0
  -- Pull {z | g z = 0} through (extChartAt q).symm
  have h_left_inv := (extChartAt 𝓘(ℂ, ℂ) q).left_inv (mem_extChartAt_source q)
  -- Restate h at the symm-image point
  have h_mem : {z : RS.carrier | g z = 0} ∈ @nhds RS.carrier RS.topology
      ((extChartAt 𝓘(ℂ, ℂ) q).symm (extChartAt 𝓘(ℂ, ℂ) q q)) := by
    rw [h_left_inv]; exact h
  have h_pre := (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) q).preimage_mem_nhds h_mem
  exact Filter.eventually_of_mem h_pre (fun z hz => by
    show chartRep g q z = 0
    simp only [chartRep, Function.comp_apply]; exact hz)

/-!
## The Chart-Meromorphic Argument Principle

On a compact Riemann surface, the sum of orders of a nonzero chart-meromorphic
function is zero. This is equivalent to `analyticArgumentPrinciple`.
-/

/-- The order support of a chart-meromorphic function: points where chartOrderAt
    is nonzero AND finite. Points with order ⊤ (locally identically zero) are excluded
    because they contribute 0 to any order sum (via getD). -/
noncomputable def chartOrderSupport (f : RS.carrier → ℂ) : Set RS.carrier :=
  { p | chartOrderAt f p ≠ 0 ∧ chartOrderAt f p ≠ ⊤ }

/-- The sum of chart orders over all points with nonzero order.
    Well-defined because only finitely many points have nonzero order. -/
noncomputable def chartOrderSum (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (_hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hsupp : (chartOrderSupport (RS := CRS.toRiemannSurface) f).Finite) : ℤ :=
  hsupp.toFinset.sum (fun p => (chartOrderAt (RS := CRS.toRiemannSurface) f p).getD 0)

-- Note: `chartMeromorphic_argument_principle` has been moved to
-- `Helpers/ArgumentPrinciple.lean` where it is proved via `chartOrderSum_eq_zero`.

/-!
## Connecting MDifferentiable to Chart-Meromorphic

An `MDifferentiable` function (globally differentiable on the manifold) is chart-meromorphic.
We need `MDifferentiable` (not just `MDifferentiableAt`) because `DifferentiableOn.analyticAt`
requires differentiability on a neighborhood, not just at one point.
-/

/-- An MDifferentiable function on a Riemann surface is chart-meromorphic.
    The proof uses: MDifferentiable → DifferentiableOn in charts → AnalyticAt → MeromorphicAt. -/
theorem isChartMeromorphic_of_mdifferentiable (f : RS.carrier → ℂ)
    (hf : @MDifferentiable ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ)
      RS.carrier RS.topology RS.chartedSpace ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ℂ _ _ f) :
    IsChartMeromorphic f := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  intro p
  -- Build DifferentiableOn on chart target point-by-point
  suffices h : DifferentiableOn ℂ (chartRep f p) (extChartAt 𝓘(ℂ, ℂ) p).target by
    have hmem : (extChartAt 𝓘(ℂ, ℂ) p).target ∈ nhds (chartPt (RS := RS) p) :=
      (isOpen_extChartAt_target p).mem_nhds (mem_extChartAt_target p)
    exact (h.analyticAt hmem).meromorphicAt
  intro q hq
  set x' := (extChartAt 𝓘(ℂ, ℂ) p).symm q with hx'_def
  have hx'_source : x' ∈ (chartAt ℂ p).source := by
    rw [← extChartAt_source 𝓘(ℂ, ℂ)]
    exact (extChartAt 𝓘(ℂ, ℂ) p).map_target hq
  have hfx'_source : f x' ∈ (chartAt ℂ (f p)).source :=
    mem_chart_source ℂ (f x')
  have hmd := (mdifferentiableAt_iff_of_mem_source (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ℂ))
    (x := p) (y := f p) hx'_source hfx'_source).mp (hf x')
  obtain ⟨_, hdwa⟩ := hmd
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp,
    modelWithCornersSelf_coe, Set.range_id] at hdwa
  have hda := hdwa.differentiableAt Filter.univ_mem
  have heq : extChartAt 𝓘(ℂ, ℂ) p x' = q := (extChartAt 𝓘(ℂ, ℂ) p).right_inv hq
  rw [heq] at hda
  exact hda.differentiableWithinAt

/-- MDifferentiableAt implies ContinuousAt of the chart representation.
    For model `𝓘(ℂ, ℂ)`, writtenInExtChartAt simplifies to chartRep, and
    MDifferentiableAt gives ContinuousWithinAt on Set.univ = ContinuousAt. -/
theorem continuousAt_chartRep_of_mdifferentiableAt (g : RS.carrier → ℂ) (p : RS.carrier)
    (hmd : @MDifferentiableAt ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ)
      RS.carrier RS.topology RS.chartedSpace ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ℂ _ _ g p) :
    ContinuousAt (chartRep (RS := RS) g p) (chartPt (RS := RS) p) := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  -- chartRep g p = g ∘ (extChartAt p).symm, chartPt p = extChartAt p p
  -- ContinuousAt of composition: g continuous at p, symm continuous at chartPt p
  show ContinuousAt (g ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm) (extChartAt 𝓘(ℂ, ℂ) p p)
  apply ContinuousAt.comp _ (continuousAt_extChartAt_symm p)
  rw [(extChartAt 𝓘(ℂ, ℂ) p).left_inv (mem_extChartAt_source p)]
  exact hmd.continuousAt

/-- Helper: pull back an eventually-property from chart punctured nhd to manifold punctured nhd.
    Uses: extChartAt is a local homeomorphism, so the punctured chart nhd maps
    back to a punctured manifold nhd. Works by extracting the open set and
    using left_inv on source. -/
theorem eventually_of_chartRep {P : ℂ → Prop} (g : RS.carrier → ℂ) (p : RS.carrier)
    (h : ∀ᶠ z in nhdsWithin (chartPt (RS := RS) p) {chartPt (RS := RS) p}ᶜ,
      P (chartRep (RS := RS) g p z)) :
    ∀ᶠ q in @nhdsWithin RS.carrier RS.topology p {p}ᶜ, P (g q) := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  rw [eventually_nhdsWithin_iff] at h ⊢
  -- h : ∀ᶠ z in 𝓝 (chartPt p), z ∈ {chartPt p}ᶜ → P (chartRep g p z)
  -- Goal: ∀ᶠ q in 𝓝 p, q ∈ {p}ᶜ → P (g q)
  -- Pull back h through extChartAt (continuous at p)
  have hsrc_mem : (extChartAt 𝓘(ℂ, ℂ) p).source ∈ nhds p :=
    (isOpen_extChartAt_source p).mem_nhds (mem_extChartAt_source p)
  have h_pulled := (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) p).eventually h
  -- h_pulled : ∀ᶠ q in 𝓝 p, extChartAt p q ∈ {chartPt p}ᶜ → P (chartRep g p (extChartAt p q))
  apply (h_pulled.and hsrc_mem).mono
  intro q ⟨hq_chart, hq_src⟩ hq_ne
  have hq_ne_chart : extChartAt 𝓘(ℂ, ℂ) p q ≠ chartPt (RS := RS) p := by
    intro heq
    apply hq_ne
    exact (extChartAt 𝓘(ℂ, ℂ) p).injOn hq_src (mem_extChartAt_source p)
      (show extChartAt 𝓘(ℂ, ℂ) p q = extChartAt 𝓘(ℂ, ℂ) p p from heq)
  have := hq_chart hq_ne_chart
  -- chartRep g p (extChartAt p q) = g ((extChartAt p).symm (extChartAt p q)) = g q
  simp only [chartRep, Function.comp_apply,
    (extChartAt 𝓘(ℂ, ℂ) p).left_inv hq_src] at this
  exact this

theorem eventually_ne_zero_of_chartRep (g : RS.carrier → ℂ) (p : RS.carrier)
    (h : ∀ᶠ z in nhdsWithin (chartPt (RS := RS) p) {chartPt (RS := RS) p}ᶜ,
      chartRep (RS := RS) g p z ≠ 0) :
    ∀ᶠ q in @nhdsWithin RS.carrier RS.topology p {p}ᶜ, g q ≠ 0 :=
  eventually_of_chartRep (P := (· ≠ 0)) g p h

/-- The chart representation pulls back "eventually zero in punctured chart nhd"
    to "eventually zero in punctured manifold nhd". -/
theorem eventually_eq_zero_of_chartRep (g : RS.carrier → ℂ) (p : RS.carrier)
    (h : ∀ᶠ z in nhdsWithin (chartPt (RS := RS) p) {chartPt (RS := RS) p}ᶜ,
      chartRep (RS := RS) g p z = 0) :
    ∀ᶠ q in @nhdsWithin RS.carrier RS.topology p {p}ᶜ, g q = 0 :=
  eventually_of_chartRep (P := (· = 0)) g p h

/-!
## Meromorphic Identity Principle

On a connected Riemann surface, a chart-meromorphic function is either
locally zero everywhere or locally zero nowhere. This is the fundamental
dichotomy that underlies the identity principle for meromorphic functions.
-/

/-- A Riemann surface has at least two points.

    This follows from the chart structure: a chart maps an open neighborhood
    to an open subset of ℂ, which is infinite. Hence the manifold has ≥ 2 points. -/
theorem rs_nontrivial : @Nontrivial RS.carrier := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  haveI := RS.connected
  haveI := RS.t2
  obtain ⟨p⟩ : Nonempty RS.carrier := inferInstance
  set e := extChartAt 𝓘(ℂ, ℂ) p
  -- ℂ is connected nontrivial T1, so punctured nhds are NeBot
  haveI : Filter.NeBot (nhdsWithin (e p) ({e p}ᶜ : Set ℂ)) :=
    ConnectedSpace.neBot_nhdsWithin_compl_of_nontrivial_of_t1space _
  -- e.target is open, contains e p, hence in the punctured nhd filter
  have htgt_pnhd : e.target ∈ nhdsWithin (e p) ({e p}ᶜ : Set ℂ) :=
    nhdsWithin_le_nhds ((isOpen_extChartAt_target (I := 𝓘(ℂ, ℂ)) p).mem_nhds
      (mem_extChartAt_target (I := 𝓘(ℂ, ℂ)) p))
  -- Extract z ∈ e.target with z ≠ e p from the NeBot filter
  obtain ⟨z, hz_tgt, hz_ne⟩ :=
    Filter.nonempty_of_mem (Filter.inter_mem htgt_pnhd self_mem_nhdsWithin)
  rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hz_ne
  refine ⟨⟨p, e.symm z, fun h => hz_ne ?_⟩⟩
  calc z = e (e.symm z) := (e.right_inv hz_tgt).symm
    _ = e p := by rw [h]

/-- On a Riemann surface, no point is isolated: the punctured neighborhood
    filter is always nontrivial.

    Uses: ConnectedSpace + Nontrivial + T1Space ⟹ NeBot (𝓝[≠] x). -/
theorem rs_nhdsNE_neBot (p : RS.carrier) :
    @Filter.NeBot _ (@nhdsWithin RS.carrier RS.topology p {p}ᶜ) := by
  letI := RS.topology
  haveI := RS.connected
  haveI := RS.t2
  haveI : @Nontrivial RS.carrier := rs_nontrivial
  exact ConnectedSpace.neBot_nhdsWithin_compl_of_nontrivial_of_t1space p

/-- **Meromorphic identity principle on connected Riemann surfaces.**

    If g is chart-meromorphic on a connected Riemann surface and
    chartOrderAt g p₀ ≠ ⊤ at some point p₀, then chartOrderAt g q ≠ ⊤
    for ALL q. Equivalently, g is not locally identically zero near any point.

    **Proof:** The sets U = {p | locally zero} and V = {p | not locally zero}
    are both open (U by propagation, V by the MeromorphicAt dichotomy + NeBot).
    RS is connected, so one is empty. Since p₀ ∈ V, we get V = RS. -/
theorem chartOrderAt_ne_top_of_ne_top_somewhere
    (g : RS.carrier → ℂ) (hcm : IsChartMeromorphic g)
    (p₀ : RS.carrier) (hne : chartOrderAt (RS := RS) g p₀ ≠ ⊤) (q : RS.carrier) :
    chartOrderAt (RS := RS) g q ≠ ⊤ := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  haveI := RS.connected
  haveI := RS.t2
  -- Define U = {p | chartOrderAt g p = ⊤} (locally zero)
  -- We show U is clopen and p₀ ∉ U, hence U = ∅ by connectivity
  set U := { p : RS.carrier | chartOrderAt (RS := RS) g p = ⊤ } with hU_def
  suffices hU_clopen : @IsClopen RS.carrier RS.topology U by
    -- By connectivity, U = ∅ or U = univ
    rcases @isClopen_iff RS.carrier RS.topology _ U |>.mp hU_clopen with h | h
    · -- U = ∅: every point has order ≠ ⊤
      exact fun hq => by
        have : q ∈ U := hq; rw [h] at this; exact this
    · -- U = univ: contradicts p₀ ∉ U
      exact absurd (show p₀ ∈ U from h ▸ Set.mem_univ _) (by simp [hU_def, hne])
  constructor
  · -- IsClosed U: show Uᶜ is open
    rw [← isOpen_compl_iff]
    rw [isOpen_iff_forall_mem_open]
    intro p hp
    simp only [Set.mem_compl_iff, hU_def, Set.mem_setOf_eq] at hp
    -- chartOrderAt g p ≠ ⊤ → g eventually nonzero in punctured chart nhd
    have h_ev_ne := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hcm p)).mp hp
    have h_mfld_ne := eventually_ne_zero_of_chartRep g p h_ev_ne
    -- Convert and propagate: ∀ᶠ q in 𝓝 p, ∀ᶠ z in 𝓝 q, z ∈ {p}ᶜ → g z ≠ 0
    rw [eventually_nhdsWithin_iff] at h_mfld_ne
    have h_prop := h_mfld_ne.eventually_nhds
    obtain ⟨W, hW_sub, hW_open, hp_W⟩ := eventually_nhds_iff.mp h_prop
    refine ⟨W, fun r hr => ?_, hW_open, hp_W⟩
    simp only [Set.mem_compl_iff, hU_def, Set.mem_setOf_eq]
    -- Show chartOrderAt g r ≠ ⊤
    intro hr_top
    -- g is eventually zero near r (from order = ⊤)
    have h_mfld_zero := eventually_eq_zero_of_chartRep g r
      (meromorphicOrderAt_eq_top_iff.mp hr_top)
    have hr_prop := hW_sub r hr
    -- hr_prop : ∀ᶠ z in 𝓝 r, z ∈ {p}ᶜ → g z ≠ 0
    by_cases hrp : r = p
    · exact hp (hrp ▸ hr_top)
    · -- r ≠ p: combine {p}ᶜ ∈ 𝓝 r with hr_prop to get g ≠ 0 on 𝓝 r
      have hne_p : ({p}ᶜ : Set RS.carrier) ∈ @nhds _ RS.topology r :=
        isOpen_compl_singleton.mem_nhds
          (show r ∈ ({p}ᶜ : Set RS.carrier) by
            rw [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hrp)
      -- g ≠ 0 on full 𝓝 r (combining membership + implication)
      have h_ne_nhds : ∀ᶠ z in @nhds _ RS.topology r, g z ≠ 0 :=
        (Filter.eventually_of_mem hne_p (fun _ h => h)).mp hr_prop
      -- g ≠ 0 eventually in 𝓝[≠] r
      have h_ne : ∀ᶠ z in @nhdsWithin _ RS.topology r {r}ᶜ, g z ≠ 0 :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds h_ne_nhds
      -- g = 0 eventually in 𝓝[≠] r
      -- Combined: ∀ᶠ z in 𝓝[≠] r, False → contradicts NeBot
      haveI := rs_nhdsNE_neBot (RS := RS) r
      have : ∀ᶠ z in @nhdsWithin _ RS.topology r {r}ᶜ, False :=
        h_ne.mp (h_mfld_zero.mono fun z heq hne => hne heq)
      exact absurd (Filter.empty_mem_iff_bot.mp
        (Filter.mem_of_superset this (fun _ h => h.elim))) (Filter.NeBot.ne ‹_›)
  · -- IsOpen U
    rw [isOpen_iff_forall_mem_open]
    intro p hp
    simp only [hU_def, Set.mem_setOf_eq] at hp
    -- chartOrderAt g p = ⊤ → g eventually zero in punctured manifold nhd
    have h_mfld_zero := eventually_eq_zero_of_chartRep g p
      (meromorphicOrderAt_eq_top_iff.mp hp)
    -- Convert and propagate
    rw [eventually_nhdsWithin_iff] at h_mfld_zero
    have h_prop := h_mfld_zero.eventually_nhds
    obtain ⟨V, hV_sub, hV_open, hp_V⟩ := eventually_nhds_iff.mp h_prop
    refine ⟨V, fun r hr => ?_, hV_open, hp_V⟩
    simp only [hU_def, Set.mem_setOf_eq]
    by_cases hrp : r = p
    · exact hrp ▸ hp
    · apply chartOrderAt_eq_top_of_zero_on_nhd
      have hne_p : ({p}ᶜ : Set RS.carrier) ∈ @nhds _ RS.topology r :=
        isOpen_compl_singleton.mem_nhds
          (show r ∈ ({p}ᶜ : Set RS.carrier) by
            rw [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hrp)
      exact (Filter.eventually_of_mem hne_p (fun _ h => h)).mp (hV_sub r hr)

end RiemannSurfaces.Analytic
