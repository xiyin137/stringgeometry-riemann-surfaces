import StringGeometry.RiemannSurfaces.Analytic.Helpers.ChartMeromorphic
import StringGeometry.RiemannSurfaces.Analytic.Helpers.ChartTransition
import StringGeometry.RiemannSurfaces.Analytic.Helpers.ConnectedComplement
import StringGeometry.RiemannSurfaces.Analytic.Helpers.AnalyticKthRoot
import StringGeometry.RiemannSurfaces.Analytic.Helpers.AnalyticExtension
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Argument Principle for Compact Riemann Surfaces

This file proves the argument principle: for a nonconstant chart-meromorphic function
on a compact Riemann surface, the sum of orders (zeros positive, poles negative) is zero.

## Strategy

1. **Local mapping theorem** (sorry'd): An analytic function of order k at z₀ takes
   each nearby value exactly k times near z₀.

2. **Fiber multiplicity constancy**: The fiber multiplicity function N(c) (summing local
   multiplicities over preimages of c) is constant on ℂ by:
   - Local constancy (local mapping theorem + compactness)
   - Connectedness of ℂ minus finite branch set

3. **Conclusion**: N(0) = total zero order, N(∞) = total pole order.
   Since N is constant, these are equal, giving chartOrderSum = 0.

## Main Results

* `chartOrderSum_eq_zero` — The argument principle: chartOrderSum f = 0

## References

* Forster, "Lectures on Riemann Surfaces", Chapter 8
-/

namespace RiemannSurfaces.Analytic

open Complex Topology Classical Filter
open scoped Manifold Topology

variable {RS : RiemannSurface}

/-!
## Part 1: Local Mapping Theorem

The foundational result about analytic functions in ℂ. This states that
an analytic function with a zero of order k at z₀ takes each nearby value
exactly k times (counted without multiplicity, since all zeros are simple
for nonzero values sufficiently close to 0).

The proof uses either:
- Rouché's theorem (via Cauchy integral formula)
- Direct k-th root extraction + inverse function theorem
Both approaches require substantial infrastructure from complex analysis.
-/

/-- The derivative of an analytic function with a zero of finite positive order
    is nonzero on a punctured ball around the zero point.

    Proof: The derivative-order relation gives `analyticOrderAt (deriv H) z₀ = k - 1`,
    which is finite. So by isolated zeros of analytic functions, `deriv H ≠ 0`
    on a punctured neighborhood. -/
theorem deriv_ne_zero_punctured_ball {H : ℂ → ℂ} {z₀ : ℂ} {k : ℕ}
    (_hk : 1 ≤ k)
    (hH : AnalyticAt ℂ H z₀) (hH0 : H z₀ = 0)
    (hord : analyticOrderAt H z₀ = k) :
    ∃ ρ > 0, ∀ z, ‖z - z₀‖ < ρ → z ≠ z₀ → deriv H z ≠ 0 := by
  have hH'_ana : AnalyticAt ℂ (deriv H) z₀ := hH.deriv
  -- The order of deriv H is finite (= k - 1)
  have hH'_ord_ne_top : analyticOrderAt (deriv H) z₀ ≠ ⊤ := by
    intro h_top
    have h_add := hH.analyticOrderAt_deriv_add_one
    rw [hH0] at h_add
    rw [h_top, top_add] at h_add
    have h_eq : analyticOrderAt (H · - (0 : ℂ)) z₀ = analyticOrderAt H z₀ := by
      congr 1; ext z; simp
    rw [h_eq, hord] at h_add
    exact absurd h_add WithTop.top_ne_coe
  -- Apply isolated zeros: deriv H ≠ 0 on punctured neighborhood
  rcases hH'_ana.eventually_eq_zero_or_eventually_ne_zero with h_zero | h_ne
  · exact absurd (analyticOrderAt_eq_top.mpr h_zero) hH'_ord_ne_top
  · rw [eventually_nhdsWithin_iff] at h_ne
    obtain ⟨ρ, hρ_pos, hρ⟩ := Metric.eventually_nhds_iff.mp h_ne
    exact ⟨ρ, hρ_pos, fun z hz hne => hρ (by rwa [dist_eq_norm]) hne⟩

/-- **Local mapping theorem for analytic functions.**

If h is analytic at z₀ with h(z₀) = 0 and analyticOrderAt h z₀ = k ≥ 1,
then there exist r, ε > 0 such that:
1. h has no zeros in B(z₀, r) other than z₀
2. For every nonzero w with ‖w‖ < ε, #{z ∈ B(z₀, r) : h(z) = w} = k

This is a standard result in complex analysis. The proof goes via:
- Factor h(z) = (z - z₀)^k · g(z) with g(z₀) ≠ 0
- Extract k-th root: set φ(z) = (z - z₀) · g(z)^{1/k}, then h(z) = φ(z)^k
- φ is a local biholomorphism (by IFT, since φ'(z₀) = g(z₀)^{1/k} ≠ 0)
- h(z) = w ⟺ φ(z)^k = w ⟺ φ(z) = w^{1/k} · ζ^j for j = 0,...,k-1
- Each of the k k-th roots gives a unique solution via φ⁻¹ -/
theorem local_mapping_theorem {h : ℂ → ℂ} {z₀ : ℂ} {k : ℕ} {r_bound : ℝ}
    (hk : 1 ≤ k)
    (hana : AnalyticAt ℂ h z₀)
    (_hh0 : h z₀ = 0)
    (hord : analyticOrderAt h z₀ = k)
    (hr_bound : 0 < r_bound) :
    ∃ r > 0, r ≤ r_bound ∧ ∃ ε > 0,
      -- (1) z₀ is an isolated zero
      (∀ z, ‖z - z₀‖ < r → z ≠ z₀ → h z ≠ 0) ∧
      -- (2) For w near 0, exactly k preimages
      (∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ε →
        {z : ℂ | ‖z - z₀‖ < r ∧ h z = w}.ncard = k) ∧
      -- (3) Derivative is nonzero away from z₀
      (∀ z, ‖z - z₀‖ < r → z ≠ z₀ → deriv h z ≠ 0) := by
  -- Step 1: Normal form h(z) = (z - z₀)^k · g(z), g analytic, g(z₀) ≠ 0
  obtain ⟨g, hg_ana, hg_ne, hg_eq⟩ := hana.analyticOrderAt_eq_natCast.mp hord
  -- Step 2: k-th root of g: ψ^k = g near z₀
  obtain ⟨ψ, hψ_ana, hψ_ne, hψ_pow⟩ :=
    AnalyticKthRoot.analytic_kth_root hk hg_ana hg_ne
  -- Step 3: Define φ(z) = (z - z₀) · ψ(z), so h(z) = φ(z)^k near z₀
  set φ : ℂ → ℂ := fun z => (z - z₀) * ψ z
  have hφ_ana : AnalyticAt ℂ φ z₀ := (analyticAt_id.sub analyticAt_const).mul hψ_ana
  have hφ_z₀ : φ z₀ = 0 := by simp [φ, sub_self]
  have h_eq : ∀ᶠ z in nhds z₀, h z = φ z ^ k := by
    filter_upwards [hg_eq, hψ_pow] with z hg_z hψ_z
    rw [hg_z, smul_eq_mul, ← hψ_z, ← mul_pow]
  -- Step 4: deriv φ z₀ = ψ(z₀) ≠ 0
  have hφ_hd : HasDerivAt φ (ψ z₀) z₀ := by
    have h1 : HasDerivAt (fun z => z - z₀) 1 z₀ := (hasDerivAt_id z₀).sub_const z₀
    have h2 : HasDerivAt ψ (deriv ψ z₀) z₀ := hψ_ana.differentiableAt.hasDerivAt
    have := h1.mul h2
    simp only [one_mul, sub_self, zero_mul, add_zero] at this
    exact this
  have hφ'_eq : deriv φ z₀ = ψ z₀ := hφ_hd.deriv
  have hφ'_ne : deriv φ z₀ ≠ 0 := hφ'_eq ▸ hψ_ne
  -- Step 5: IFT → local homeomorphism R for φ
  have hsd : HasStrictDerivAt φ (deriv φ z₀) z₀ := hφ_ana.hasStrictDerivAt
  set hfda := hsd.hasStrictFDerivAt_equiv hφ'_ne
  set R := hfda.toOpenPartialHomeomorph φ
  have hR_coe : (R : ℂ → ℂ) = φ := HasStrictFDerivAt.toOpenPartialHomeomorph_coe hfda
  have hz₀_src : z₀ ∈ R.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hfda
  have h0_tgt : (0 : ℂ) ∈ R.target := by
    rw [← hφ_z₀, ← hR_coe]; exact R.map_source hz₀_src
  have hR_symm_0 : R.symm 0 = z₀ := by
    rw [← hφ_z₀, ← hR_coe]; exact R.left_inv hz₀_src
  -- Step 6: Choose parameters
  -- Get r₁ such that B(z₀, r₁) ⊆ R.source and h = φ^k on B(z₀, r₁)
  have h_src_eq : ∀ᶠ z in nhds z₀, z ∈ R.source ∧ h z = φ z ^ k := by
    filter_upwards [R.open_source.mem_nhds hz₀_src, h_eq] with z h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨r₁, hr₁_pos, hr₁_sub⟩ := Metric.eventually_nhds_iff.mp h_src_eq
  -- Get derivative ball: deriv h ≠ 0 near z₀
  obtain ⟨ρ_h, hρ_h_pos, hderiv_h_ne⟩ := deriv_ne_zero_punctured_ball hk hana _hh0 hord
  -- Shrink radius to satisfy all constraints
  set r := min (min r₁ ρ_h) r_bound with hr_def
  have hr_pos : 0 < r := lt_min (lt_min hr₁_pos hρ_h_pos) hr_bound
  have hr_le_r₁ : r ≤ r₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hr_le_ρ : r ≤ ρ_h := le_trans (min_le_left _ _) (min_le_right _ _)
  have hr_le_bound : r ≤ r_bound := min_le_right _ _
  -- Get δ₁ such that R.symm(B(0, δ₁)) ⊆ B(z₀, r)
  have hR_symm_cont : ContinuousAt R.symm 0 :=
    R.symm.continuousAt (R.symm_source ▸ h0_tgt)
  obtain ⟨δ₁, hδ₁_pos, hδ₁_sub⟩ := Metric.continuousAt_iff.mp hR_symm_cont r hr_pos
  -- Convert hδ₁_sub to use z₀ instead of R.symm 0
  replace hδ₁_sub : ∀ y, dist y 0 < δ₁ → dist (R.symm y) z₀ < r := by
    intro y hy; have := hδ₁_sub hy; rwa [hR_symm_0] at this
  -- Ensure δ₁ is in R.target
  have h_tgt_nhd : ∀ᶠ y in nhds (0 : ℂ), y ∈ R.target :=
    R.open_target.mem_nhds h0_tgt
  obtain ⟨δ₂, hδ₂_pos, hδ₂_sub⟩ := Metric.eventually_nhds_iff.mp h_tgt_nhd
  set δ := min δ₁ δ₂ with hδ_def
  have hδ_pos : 0 < δ := lt_min hδ₁_pos hδ₂_pos
  -- Set ε = δ^k (so |w| < ε implies all k-th roots have modulus < δ)
  set ε := δ ^ k with hε_def
  have hε_pos : 0 < ε := pow_pos hδ_pos k
  -- Step 7: Prove conditions
  refine ⟨r, hr_pos, hr_le_bound, ε, hε_pos, ?_, ?_, ?_⟩
  · -- Condition 1: Isolated zero
    intro z hz hne hh_eq_zero
    have hz_r₁ : dist z z₀ < r₁ := lt_of_lt_of_le (by rwa [dist_eq_norm]) hr_le_r₁
    have ⟨hz_src, h_eq_φk⟩ := hr₁_sub hz_r₁
    rw [h_eq_φk] at hh_eq_zero
    have hφ_z_zero : φ z = 0 := by
      rcases eq_or_ne k 0 with rfl | hk0
      · omega
      · exact (pow_eq_zero_iff hk0).mp hh_eq_zero
    -- φ(z) = 0 and φ is injective on R.source → z = z₀
    have hR_inj : Set.InjOn R R.source := R.injOn
    have : R z = R z₀ := by
      show φ z = φ z₀
      rw [hφ_z_zero, hφ_z₀]
    exact hne (hR_inj hz_src hz₀_src this)
  · -- Condition 2: ncard = k
    intro w hw_pos hw_lt
    -- Every k-th root ζ of w has |ζ|^k = |w| < ε = δ^k, so |ζ| < δ
    have hroot_small : ∀ ζ : ℂ, ζ ^ k = w → ‖ζ‖ < δ := by
      intro ζ hζ
      have h1 : ‖ζ‖ ^ k = ‖w‖ := AnalyticKthRoot.norm_kthRoot_eq w k ζ hζ
      have h2 : ‖w‖ < δ ^ k := by rwa [hε_def] at hw_lt
      exact lt_of_pow_lt_pow_left₀ k (le_of_lt hδ_pos) (h1 ▸ h2)
    -- Every k-th root is in R.target
    have hroot_tgt : ∀ ζ : ℂ, ζ ^ k = w → ζ ∈ R.target := by
      intro ζ hζ
      apply hδ₂_sub
      simpa [dist_eq_norm] using (hroot_small ζ hζ).trans_le (min_le_right _ _)
    -- R.symm(ζ) ∈ B(z₀, r) for each root ζ (δ₁ → R.symm lands in B(z₀, r))
    have hroot_ball : ∀ ζ : ℂ, ζ ^ k = w → dist (R.symm ζ) z₀ < r := by
      intro ζ hζ
      apply hδ₁_sub
      simpa [dist_eq_norm] using (hroot_small ζ hζ).trans_le (min_le_left _ _)
    -- The preimage set equals the image of {ζ : ζ^k = w} under R.symm
    have h_preim_eq : {z : ℂ | ‖z - z₀‖ < r ∧ h z = w} =
        R.symm '' {ζ : ℂ | ζ ^ k = w} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · -- z is a preimage → z = R.symm(φ(z)) with φ(z)^k = w
        intro ⟨hz_ball, hz_eq⟩
        have hz_r₁ : dist z z₀ < r₁ := lt_of_lt_of_le (by rwa [dist_eq_norm]) hr_le_r₁
        have ⟨hz_src, h_eq_φk⟩ := hr₁_sub hz_r₁
        have hφk : φ z ^ k = w := by rw [← h_eq_φk]; exact hz_eq
        refine ⟨φ z, ?_, ?_⟩
        · exact hφk
        · have : R z = φ z := by rw [← hR_coe]
          rw [← this, R.left_inv hz_src]
      · -- ζ^k = w and z = R.symm(ζ) → z is in ball and h(z) = w
        intro ⟨ζ, hζ_pow, hz_eq⟩
        subst hz_eq
        refine ⟨?_, ?_⟩
        · rw [← dist_eq_norm]; exact hroot_ball ζ hζ_pow
        · have hsrc : R.symm ζ ∈ R.source := R.map_target (hroot_tgt ζ hζ_pow)
          have ⟨_, h_eq_φk⟩ := hr₁_sub (lt_of_lt_of_le (hroot_ball ζ hζ_pow) hr_le_r₁)
          rw [h_eq_φk]
          have : φ (R.symm ζ) = ζ := by
            rw [← hR_coe]; exact R.right_inv (hroot_tgt ζ hζ_pow)
          rw [this, hζ_pow]
    -- R.symm is injective on {ζ : ζ^k = w}
    have hR_symm_inj : Set.InjOn R.symm {ζ : ℂ | ζ ^ k = w} := by
      intro a ha b hb hab
      have ha_tgt := hroot_tgt a ha
      have hb_tgt := hroot_tgt b hb
      have : R (R.symm a) = R (R.symm b) := by rw [hab]
      rw [R.right_inv ha_tgt, R.right_inv hb_tgt] at this
      exact this
    -- ncard = k
    rw [h_preim_eq, Set.InjOn.ncard_image hR_symm_inj]
    have hw_ne : w ≠ 0 := fun h => by simp [h] at hw_pos
    exact AnalyticKthRoot.ncard_kthRoots w hw_ne k (by omega)
  · -- Condition 3: Derivative nonzero away from z₀
    exact fun z hz hne => hderiv_h_ne z (lt_of_lt_of_le hz hr_le_ρ) hne

/-!
## Part 2: Fiber Multiplicity Constancy

For a nonconstant chart-meromorphic function on a compact RS, the "fiber
multiplicity" N(c) — the total multiplicity of preimages of c in the regular
locus — is constant as a function of c ∈ ℂ.

This follows from:
- Local mapping theorem (Part 1)
- Compactness of the surface (no extra preimages appear)
- Connectedness of ℂ minus finite branch set
-/

/-- The **regular locus** of a chart-meromorphic function: the set of points
    where chartOrderAt is nonneg (i.e., not poles). -/
def regularLocus (f : RS.carrier → ℂ) : Set RS.carrier :=
  { p | (0 : WithTop ℤ) ≤ chartOrderAt (RS := RS) f p }

/-- Nonconstancy on the regular locus provides two regular points with distinct values. -/
private theorem exists_distinct_values_on_regularLocus {RS : RiemannSurface}
    (f : RS.carrier → ℂ)
    (hnc : ¬ ∀ p q, p ∈ regularLocus (RS := RS) f →
      q ∈ regularLocus (RS := RS) f → f p = f q) :
    ∃ p q, p ∈ regularLocus (RS := RS) f ∧ q ∈ regularLocus (RS := RS) f ∧ f p ≠ f q := by
  push_neg at hnc
  exact hnc

/-- If `f` is nonconstant on its regular locus, then for every `c` there is a point with `f p ≠ c`. -/
theorem exists_ne_value_of_nonconstant_regularLocus {RS : RiemannSurface}
    (f : RS.carrier → ℂ)
    (hnc : ¬ ∀ p q, p ∈ regularLocus (RS := RS) f →
      q ∈ regularLocus (RS := RS) f → f p = f q)
    (c : ℂ) :
    ∃ p : RS.carrier, f p ≠ c := by
  obtain ⟨p, q, _hp, _hq, hpq⟩ := exists_distinct_values_on_regularLocus (RS := RS) f hnc
  by_cases hpc : f p = c
  · refine ⟨q, ?_⟩
    intro hqc
    exact hpq (hpc.trans hqc.symm)
  · exact ⟨p, hpc⟩

/-- If `f` is nonconstant on its regular locus, then for every `c` there is a
    regular point with value not equal to `c`. -/
theorem exists_regular_ne_value_of_nonconstant_regularLocus {RS : RiemannSurface}
    (f : RS.carrier → ℂ)
    (hnc : ¬ ∀ p q, p ∈ regularLocus (RS := RS) f →
      q ∈ regularLocus (RS := RS) f → f p = f q)
    (c : ℂ) :
    ∃ p : RS.carrier, p ∈ regularLocus (RS := RS) f ∧ f p ≠ c := by
  obtain ⟨p, q, hp, hq, hpq⟩ := exists_distinct_values_on_regularLocus (RS := RS) f hnc
  by_cases hpc : f p = c
  · refine ⟨q, hq, ?_⟩
    intro hqc
    exact hpq (hpc.trans hqc.symm)
  · exact ⟨p, hp, hpc⟩

/-- **Fiber multiplicity**: the sum of chart orders of f - c over all preimages
    of c in the regular locus. -/
noncomputable def fiberMultiplicity (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (c : ℂ)
    (hfib : {p : CRS.toRiemannSurface.carrier |
      f p = c ∧ (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p}.Finite) : ℤ :=
  hfib.toFinset.sum (fun p =>
    (chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p).getD 0)

/-- The pole set of a chart-meromorphic function: points with negative chart order. -/
noncomputable def poleSet (f : RS.carrier → ℂ) : Set RS.carrier :=
  { p | chartOrderAt (RS := RS) f p < 0 }

/- **Constancy of fiber multiplicity.**

On a compact RS, for a nonconstant chart-meromorphic function, the fiber
multiplicity N(c) is the same for all c ∈ ℂ. This is the degree of f
as a map to ℙ¹.

The formalized constancy theorem is provided in
`Helpers/ArgumentPrinciple/FiberMultiplicity.lean` as
`fiberMultiplicity_constant` with an explicit regular-value compatibility
hypothesis (or continuity-based variants). -/

/-!
## Part 3: The Argument Principle

Using the constancy of fiber multiplicity, we derive chartOrderSum = 0.
-/

/-- Helper: At a pole of a chart-meromorphic function, f ≠ c in a punctured manifold
    neighborhood, for any constant c. -/
theorem eventually_ne_const_at_pole {RS : RiemannSurface}
    (f : RS.carrier → ℂ)
    (_hf : IsChartMeromorphic (RS := RS) f)
    (p : RS.carrier)
    (hpole : chartOrderAt (RS := RS) f p < 0)
    (c : ℂ) :
    ∀ᶠ q in @nhdsWithin RS.carrier RS.topology p {p}ᶜ, f q ≠ c := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  -- chartRep f p has a pole at chartPt p: it tends to cobounded (infinity)
  have htend := tendsto_cobounded_of_meromorphicOrderAt_neg hpole
  -- Eventually ‖chartRep f p z‖ > ‖c‖ + 1 in punctured chart nhd
  rw [← tendsto_norm_atTop_iff_cobounded] at htend
  have h_ev : ∀ᶠ z in nhdsWithin (chartPt (RS := RS) p) {chartPt (RS := RS) p}ᶜ,
      chartRep (RS := RS) f p z ≠ c := by
    apply (htend.eventually (Filter.eventually_ge_atTop (‖c‖ + 1))).mono
    intro z hz habs
    rw [habs] at hz; linarith
  exact eventually_of_chartRep (P := (· ≠ c)) f p h_ev

/-- Helper: AccPt in the manifold implies accumulating values in charts. -/
theorem accPt_implies_frequently_in_chart {RS : RiemannSurface}
    (f : RS.carrier → ℂ)
    (p₀ : RS.carrier)
    (S : Set RS.carrier)
    (hacc : @AccPt RS.carrier RS.topology p₀ (Filter.principal S))
    (hS : ∀ q ∈ S, f q = c) :
    ∃ᶠ z in @nhdsWithin RS.carrier RS.topology p₀ {p₀}ᶜ, f z = c := by
  letI := RS.topology
  rw [accPt_iff_frequently_nhdsNE] at hacc
  exact hacc.mono (fun z hz => hS z hz)

/-- **Fiber finiteness**: On a compact RS, a chart-meromorphic function with
    analytic regularity at non-pole points has finite fibers.

    The regularity hypothesis `hreg` requires that at non-pole points,
    the chart representation is actually analytic (not just meromorphic).
    This is automatically satisfied by functions defined by explicit formulas
    (e.g., linear combinations of meromorphic sections). -/
theorem fiber_finite (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hreg : ∀ p, (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p →
      AnalyticAt ℂ (chartRep (RS := CRS.toRiemannSurface) f p)
        (chartPt (RS := CRS.toRiemannSurface) p))
    (c : ℂ) (hne : ∃ p, f p ≠ c) :
    {p : CRS.toRiemannSurface.carrier |
      f p = c ∧ (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p}.Finite := by
  letI := CRS.toRiemannSurface.topology
  letI := CRS.toRiemannSurface.chartedSpace
  haveI := CRS.toRiemannSurface.isManifold
  haveI := CRS.toRiemannSurface.connected
  haveI := CRS.toRiemannSurface.t2
  have hfc : IsChartMeromorphic (RS := CRS.toRiemannSurface) (fun x => f x - c) := by
    simpa [sub_eq_add_neg] using
      (chartMeromorphic_add (RS := CRS.toRiemannSurface) hf
        (chartMeromorphic_const (RS := CRS.toRiemannSurface) (-c)))
  obtain ⟨p₀, hp₀_val⟩ := hne
  have hp₀_ne_top : chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p₀ ≠ ⊤ := by
    by_cases hpole₀ : chartOrderAt (RS := CRS.toRiemannSurface) f p₀ < 0
    · intro htop
      have h_ev_ne : ∀ᶠ q in @nhdsWithin _ CRS.toRiemannSurface.topology p₀ {p₀}ᶜ, f q ≠ c :=
        eventually_ne_const_at_pole (RS := CRS.toRiemannSurface) f hf p₀ hpole₀ c
      have h_ev_zero_chart :
          ∀ᶠ z in nhdsWithin (chartPt (RS := CRS.toRiemannSurface) p₀)
            {chartPt (RS := CRS.toRiemannSurface) p₀}ᶜ,
            chartRep (RS := CRS.toRiemannSurface) (fun x => f x - c) p₀ z = 0 :=
        meromorphicOrderAt_eq_top_iff.mp htop
      have h_ev_zero :
          ∀ᶠ q in @nhdsWithin _ CRS.toRiemannSurface.topology p₀ {p₀}ᶜ,
            (fun x => f x - c) q = 0 :=
        eventually_eq_zero_of_chartRep (RS := CRS.toRiemannSurface) (fun x => f x - c) p₀
          h_ev_zero_chart
      have h_ev_eq : ∀ᶠ q in @nhdsWithin _ CRS.toRiemannSurface.topology p₀ {p₀}ᶜ, f q = c :=
        h_ev_zero.mono (fun q hq => sub_eq_zero.mp hq)
      haveI := rs_nhdsNE_neBot (RS := CRS.toRiemannSurface) p₀
      have hfalse : ∀ᶠ q in @nhdsWithin _ CRS.toRiemannSurface.topology p₀ {p₀}ᶜ, False :=
        (h_ev_eq.and h_ev_ne).mono (fun q hq => hq.2 hq.1)
      exact absurd (Filter.empty_mem_iff_bot.mp
        (Filter.mem_of_superset hfalse (fun _ h => h.elim))) (Filter.NeBot.ne ‹_›)
    · have hnonneg₀ : (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p₀ :=
        le_of_not_gt hpole₀
      have hcont_f₀ : ContinuousAt
          (chartRep (RS := CRS.toRiemannSurface) f p₀)
          (chartPt (RS := CRS.toRiemannSurface) p₀) := (hreg p₀ hnonneg₀).continuousAt
      have hrep_sub₀ : chartRep (RS := CRS.toRiemannSurface) (fun x => f x - c) p₀ =
          fun z => chartRep (RS := CRS.toRiemannSurface) f p₀ z - c := by
        ext z
        simp [chartRep, Function.comp]
      have hcont_sub₀ : ContinuousAt
          (fun z => chartRep (RS := CRS.toRiemannSurface) f p₀ z - c)
          (chartPt (RS := CRS.toRiemannSurface) p₀) :=
        hcont_f₀.sub continuousAt_const
      have hcont₀ : ContinuousAt
          (chartRep (RS := CRS.toRiemannSurface) (fun x => f x - c) p₀)
          (chartPt (RS := CRS.toRiemannSurface) p₀) := by
        simpa [hrep_sub₀] using hcont_sub₀
      have hne₀ : (fun x => f x - c) p₀ ≠ 0 := by
        simpa [sub_eq_zero] using hp₀_val
      have hzero₀ : chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p₀ = 0 :=
        chartOrderAt_eq_zero_of_continuousAt_ne_zero (RS := CRS.toRiemannSurface) hfc p₀ hcont₀ hne₀
      rw [hzero₀]
      exact WithTop.zero_ne_top
  have hne_top_all : ∀ p, chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p ≠ ⊤ :=
    fun p => chartOrderAt_ne_top_of_ne_top_somewhere (RS := CRS.toRiemannSurface)
      (fun x => f x - c) hfc p₀ hp₀_ne_top p
  have hsupp_fin : (chartOrderSupport (RS := CRS.toRiemannSurface) (fun x => f x - c)).Finite :=
    chartOrderSupport_finite_general CRS (fun x => f x - c) hfc ⟨p₀, hp₀_ne_top⟩
  refine hsupp_fin.subset ?_
  intro p hp
  rcases hp with ⟨hfp, hnonnegp⟩
  have hfp_zero : (fun x => f x - c) p = 0 := by
    simp [hfp]
  have hcont_f : ContinuousAt
      (chartRep (RS := CRS.toRiemannSurface) f p)
      (chartPt (RS := CRS.toRiemannSurface) p) := (hreg p hnonnegp).continuousAt
  have hrep_sub : chartRep (RS := CRS.toRiemannSurface) (fun x => f x - c) p =
      fun z => chartRep (RS := CRS.toRiemannSurface) f p z - c := by
    ext z
    simp [chartRep, Function.comp]
  have hcont_sub : ContinuousAt
      (fun z => chartRep (RS := CRS.toRiemannSurface) f p z - c)
      (chartPt (RS := CRS.toRiemannSurface) p) :=
    hcont_f.sub continuousAt_const
  have hcont : ContinuousAt
      (chartRep (RS := CRS.toRiemannSurface) (fun x => f x - c) p)
      (chartPt (RS := CRS.toRiemannSurface) p) := by
    simpa [hrep_sub] using hcont_sub
  have hpos : (0 : WithTop ℤ) < chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p :=
    chartOrderAt_pos_of_zero (RS := CRS.toRiemannSurface) hfc p hfp_zero hcont
  rw [chartOrderSupport, Set.mem_setOf_eq]
  exact ⟨ne_of_gt hpos, hne_top_all p⟩

/-- The total pole order: Σ |ord_p(f)| over poles. -/
noncomputable def totalPoleOrder (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hpole_fin : (poleSet (RS := CRS.toRiemannSurface) f).Finite) : ℤ :=
  hpole_fin.toFinset.sum (fun p =>
    -((chartOrderAt (RS := CRS.toRiemannSurface) f p).getD 0))

/-- Poles are finite for a chart-meromorphic function on a compact RS. -/
theorem poleSet_finite (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (_hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hsupp : (chartOrderSupport (RS := CRS.toRiemannSurface) f).Finite) :
    (poleSet (RS := CRS.toRiemannSurface) f).Finite := by
  apply hsupp.subset
  intro p hp
  simp only [poleSet, Set.mem_setOf_eq] at hp
  simp only [chartOrderSupport, Set.mem_setOf_eq]
  constructor
  · intro h0; rw [h0] at hp; exact (not_lt.mpr le_rfl) (by exact_mod_cast hp)
  · intro htop; rw [htop] at hp; exact absurd hp (not_lt.mpr le_top)

/-- The positive part of chartOrderSupport: zeros. -/
noncomputable def zeroSet (f : RS.carrier → ℂ) : Set RS.carrier :=
  { p | 0 < chartOrderAt (RS := RS) f p ∧ chartOrderAt (RS := RS) f p ≠ ⊤ }

/-- Zeros are finite for a chart-meromorphic function on a compact RS. -/
theorem zeroSet_finite (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (_hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hsupp : (chartOrderSupport (RS := CRS.toRiemannSurface) f).Finite) :
    (zeroSet (RS := CRS.toRiemannSurface) f).Finite := by
  apply hsupp.subset
  intro p hp
  simp only [zeroSet, Set.mem_setOf_eq] at hp
  simp only [chartOrderSupport, Set.mem_setOf_eq]
  exact ⟨fun h0 => by rw [h0] at hp; exact (lt_irrefl (0 : WithTop ℤ)) hp.1, hp.2⟩

/-- chartOrderSupport equals the disjoint union of zeroSet and poleSet. -/
theorem chartOrderSupport_eq_union (f : RS.carrier → ℂ) :
    chartOrderSupport (RS := RS) f = zeroSet (RS := RS) f ∪ poleSet (RS := RS) f := by
  ext p
  simp only [chartOrderSupport, zeroSet, poleSet, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · intro ⟨hne0, hne_top⟩
    cases h : chartOrderAt (RS := RS) f p with
    | top => exact absurd h hne_top
    | coe m =>
      have hm_ne : m ≠ 0 := fun hm0 => hne0 (by rw [h, hm0]; rfl)
      rcases Int.lt_or_gt_of_ne hm_ne with hm_neg | hm_pos
      · right
        simpa [h] using (show ((m : WithTop ℤ) < (0 : WithTop ℤ)) from WithTop.coe_lt_coe.2 hm_neg)
      · left
        exact ⟨by
          simpa [h] using
            (show ((0 : WithTop ℤ) < (m : WithTop ℤ)) from WithTop.coe_lt_coe.2 hm_pos),
          WithTop.coe_ne_top⟩
  · intro h
    rcases h with ⟨hpos, hne_top⟩ | hneg
    · exact ⟨ne_of_gt hpos, hne_top⟩
    · constructor
      · exact fun h0 => absurd (h0 ▸ hneg : (0 : WithTop ℤ) < 0) (lt_irrefl 0)
      · exact fun htop => absurd (htop ▸ hneg) (not_lt.mpr le_top)

/-- zeroSet and poleSet are disjoint. -/
theorem zeroSet_poleSet_disjoint (f : RS.carrier → ℂ) :
    Disjoint (zeroSet (RS := RS) f) (poleSet (RS := RS) f) := by
  refine Set.disjoint_left.2 ?_
  intro p hz hp
  simp only [zeroSet, poleSet, Set.mem_setOf_eq] at hz hp
  exact absurd (lt_trans hz.1 hp) (lt_irrefl 0)

/-- **Key lemma: chartOrderSum splits into zero and pole contributions.**

chartOrderSum f = (total zero order) - (total pole order)

This is immediate from the definition: the support splits into zeros and poles,
and the chart order at zeros is positive while at poles is negative. -/
theorem chartOrderSum_split (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hsupp : (chartOrderSupport (RS := CRS.toRiemannSurface) f).Finite) :
    chartOrderSum CRS f hf hsupp =
      (zeroSet_finite CRS f hf hsupp).toFinset.sum
        (fun p => (chartOrderAt (RS := CRS.toRiemannSurface) f p).getD 0) -
      totalPoleOrder CRS f (poleSet_finite CRS f hf hsupp) := by
  unfold chartOrderSum totalPoleOrder
  set zF := (zeroSet_finite CRS f hf hsupp).toFinset
  set pF := (poleSet_finite CRS f hf hsupp).toFinset
  -- Step 1: hsupp.toFinset = zF ∪ pF
  have hunion : hsupp.toFinset = zF ∪ pF := by
    ext p
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, zF, pF,
      chartOrderSupport_eq_union (RS := CRS.toRiemannSurface) f, Set.mem_union]
  -- Step 2: Disjoint zF pF
  have hdisj : Disjoint zF pF := by
    rw [Finset.disjoint_left]
    intro p hp_z hp_p
    have hz : p ∈ zeroSet (RS := CRS.toRiemannSurface) f :=
      (zeroSet_finite CRS f hf hsupp).mem_toFinset.mp hp_z
    have hp : p ∈ poleSet (RS := CRS.toRiemannSurface) f :=
      (poleSet_finite CRS f hf hsupp).mem_toFinset.mp hp_p
    simp only [zeroSet, poleSet, Set.mem_setOf_eq] at hz hp
    exact absurd (lt_trans hz.1 hp) (lt_irrefl 0)
  -- Step 3: Split the sum and simplify
  rw [hunion, Finset.sum_union hdisj]
  have hpole_neg : pF.sum (fun p => (chartOrderAt (RS := CRS.toRiemannSurface) f p).getD 0) =
      -pF.sum (fun p => -((chartOrderAt (RS := CRS.toRiemannSurface) f p).getD 0)) := by
    rw [Finset.sum_neg_distrib, neg_neg]
  rw [hpole_neg]; ring

/-!
## Part 4: Degree Theory Infrastructure

Key lemmas relating chart orders of `f - c` to those of `f`, and the core
degree theory statement that total zero order equals total pole order.
-/

/-- Helper: chartRep of (f - c) is chartRep f minus the constant c. -/
theorem chartRep_sub_const (f : RS.carrier → ℂ) (c : ℂ) (p : RS.carrier) :
    chartRep (RS := RS) (fun x => f x - c) p = fun z => chartRep (RS := RS) f p z - c := by
  ext z; simp [chartRep, Function.comp]

/-- **Pole invariance**: At a pole of f, subtracting a constant c doesn't change
    the chart order. This follows from the fact that the pole order (negative)
    is strictly less than the order of any constant (0 or ⊤), so
    `meromorphicOrderAt_add_eq_left_of_lt` applies. -/
theorem chartOrderAt_sub_const_at_pole {f : RS.carrier → ℂ} {p : RS.carrier} (c : ℂ)
    (hpole : chartOrderAt (RS := RS) f p < 0) :
    chartOrderAt (RS := RS) (fun x => f x - c) p = chartOrderAt (RS := RS) f p := by
  by_cases hc : c = 0
  · -- f - 0 = f
    subst hc; simp only [sub_zero]
  · simp only [chartOrderAt, chartRep_sub_const]
    have hrep : (fun z => chartRep (RS := RS) f p z - c) =
        chartRep (RS := RS) f p + fun _ => -c := by
      ext z; simp [Pi.add_apply, sub_eq_add_neg]
    rw [hrep]
    apply meromorphicOrderAt_add_eq_left_of_lt (MeromorphicAt.const (-c) _)
    show meromorphicOrderAt (chartRep (RS := RS) f p) (chartPt (RS := RS) p) <
        meromorphicOrderAt (fun _ => -c) (chartPt (RS := RS) p)
    rw [meromorphicOrderAt_const]
    simp only [neg_eq_zero, hc, ↓reduceIte]
    exact hpole

/-- Subtracting a constant preserves the pole/non-pole dichotomy (`< 0`). -/
theorem chartOrderAt_sub_const_lt_zero_iff {f : RS.carrier → ℂ} {p : RS.carrier} (c : ℂ) :
    chartOrderAt (RS := RS) (fun x => f x - c) p < 0 ↔ chartOrderAt (RS := RS) f p < 0 := by
  constructor
  · intro hpole_sub
    have h :=
      chartOrderAt_sub_const_at_pole (RS := RS) (f := fun x => f x - c) (p := p) (-c) hpole_sub
    have h' : chartOrderAt (RS := RS) f p =
        chartOrderAt (RS := RS) (fun x => f x - c) p := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
    exact h'.symm ▸ hpole_sub
  · intro hpole
    exact (chartOrderAt_sub_const_at_pole (RS := RS) (f := f) (p := p) c hpole) ▸ hpole

/-- Subtracting a constant preserves non-pole status (`≥ 0`). -/
theorem chartOrderAt_sub_const_nonneg_iff {f : RS.carrier → ℂ} {p : RS.carrier} (c : ℂ) :
    (0 : WithTop ℤ) ≤ chartOrderAt (RS := RS) (fun x => f x - c) p ↔
      (0 : WithTop ℤ) ≤ chartOrderAt (RS := RS) f p := by
  constructor
  · intro h
    exact le_of_not_gt (fun hpole =>
      (not_lt_of_ge h) ((chartOrderAt_sub_const_lt_zero_iff (RS := RS) (f := f) (p := p) c).2 hpole))
  · intro h
    exact le_of_not_gt (fun hpole_sub =>
      (not_lt_of_ge h) ((chartOrderAt_sub_const_lt_zero_iff (RS := RS) (f := f) (p := p) c).1 hpole_sub))

/-- The total zero order of a chart-meromorphic function: the sum of chart orders
    over all zeros (points with positive finite order). -/
noncomputable def totalZeroOrder (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hzero_fin : (zeroSet (RS := CRS.toRiemannSurface) f).Finite) : ℤ :=
  hzero_fin.toFinset.sum (fun p =>
    (chartOrderAt (RS := CRS.toRiemannSurface) f p).getD 0)

/-!
## Degree Theory Helpers

These lemmas support the proof that totalZeroOrder = totalPoleOrder, by establishing
that chartOrderSum(f - c) is locally constant in c and equals 0 for large |c|.
-/

/-- f - c is chart-meromorphic when f is. -/
theorem chartMeromorphic_sub_const {f : RS.carrier → ℂ} (c : ℂ)
    (hf : IsChartMeromorphic f) :
    IsChartMeromorphic (RS := RS) (fun x => f x - c) := by
  have : (fun x => f x - c) = fun x => f x + (-c) := by ext x; ring
  rw [this]; exact chartMeromorphic_add hf (chartMeromorphic_const (-c))

/-- chartOrderSupport(f - c) is finite for chart-meromorphic f on a compact RS
    when all orders of f are ≠ ⊤. Either all orders of f-c are ⊤ (empty support)
    or some order ≠ ⊤ (use `chartOrderSupport_finite_general`). -/
theorem chartOrderSupport_sub_const_finite (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ) (c : ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f) :
    (chartOrderSupport (RS := CRS.toRiemannSurface) (fun x => f x - c)).Finite := by
  have hfc := chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c hf
  by_cases h : ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) q = ⊤
  · -- All orders ⊤ → support is empty (since support requires order ≠ ⊤)
    have : chartOrderSupport (RS := CRS.toRiemannSurface) (fun x => f x - c) = ∅ := by
      ext p; simp only [chartOrderSupport, Set.mem_setOf_eq, Set.mem_empty_iff_false,
        iff_false, not_and]; intro _; exact absurd (h p)
    rw [this]; exact Set.finite_empty
  · push_neg at h
    exact chartOrderSupport_finite_general CRS _ hfc h

/-!
## Extensionality Lemmas for chartOrderSum

The function `chartOrderSum` depends on proof terms. These lemmas ensure
that extensionally equal functions give the same chartOrderSum.
-/

/-- chartOrderAt is invariant under extensional equality of functions. -/
theorem chartOrderAt_congr' {RS : RiemannSurface}
    {f g : RS.carrier → ℂ} (h : ∀ x, f x = g x) (p : RS.carrier) :
    chartOrderAt (RS := RS) f p = chartOrderAt (RS := RS) g p := by
  simp only [chartOrderAt, chartRep]
  congr 1; ext z; exact h _

/-- chartOrderSupport is invariant under extensional equality. -/
theorem chartOrderSupport_congr' {RS : RiemannSurface}
    {f g : RS.carrier → ℂ} (h : ∀ x, f x = g x) :
    chartOrderSupport (RS := RS) f = chartOrderSupport (RS := RS) g := by
  ext p; simp only [chartOrderSupport, Set.mem_setOf_eq, chartOrderAt_congr' h]

/-- chartOrderSum is invariant under extensional equality. -/
theorem chartOrderSum_congr' (CRS : CompactRiemannSurface)
    {f g : CRS.toRiemannSurface.carrier → ℂ}
    (h : ∀ x, f x = g x)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hg : IsChartMeromorphic (RS := CRS.toRiemannSurface) g)
    (hsupp_f : (chartOrderSupport (RS := CRS.toRiemannSurface) f).Finite)
    (hsupp_g : (chartOrderSupport (RS := CRS.toRiemannSurface) g).Finite) :
    chartOrderSum CRS f hf hsupp_f = chartOrderSum CRS g hg hsupp_g := by
  simp only [chartOrderSum]
  have hset : chartOrderSupport (RS := CRS.toRiemannSurface) f =
    chartOrderSupport (RS := CRS.toRiemannSurface) g := chartOrderSupport_congr' h
  have hfin : hsupp_f.toFinset = hsupp_g.toFinset := by
    ext p; simp [Set.Finite.mem_toFinset, hset]
  rw [hfin]
  apply Finset.sum_congr rfl
  intro p _
  rw [chartOrderAt_congr' h]

/-- f - 0 = f extensionally. -/
theorem chartOrderSum_sub_zero (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hsupp : (chartOrderSupport (RS := CRS.toRiemannSurface) f).Finite)
    (hfc : IsChartMeromorphic (RS := CRS.toRiemannSurface) (fun x => f x - 0))
    (hsupp_c : (chartOrderSupport (RS := CRS.toRiemannSurface) (fun x => f x - 0)).Finite) :
    chartOrderSum CRS (fun x => f x - 0) hfc hsupp_c = chartOrderSum CRS f hf hsupp :=
  chartOrderSum_congr' CRS (fun x => by ring) hfc hf hsupp_c hsupp

/-!
## Degree Theory: chartOrderSum = 0

The key degree theory result: for nonconstant chart-meromorphic functions on compact
Riemann surfaces, `chartOrderSum f = 0`. This is proven by:
1. Showing N(c) = chartOrderSum(f-c) is locally constant (via LMT + compactness)
2. Showing N(c₀) = 0 for large |c₀|
3. Using connectedness of ℂ to conclude N is constant, hence N(0) = 0
-/

/-- **Maximum principle for compact Riemann surfaces**: a chart-meromorphic function with
    all orders ≥ 0 and ≠ ⊤ has all orders = 0 (i.e., no zeros).

    This is because a holomorphic function on a compact Riemann surface is constant.
    A nonzero constant has order 0 everywhere. The zero constant has order ⊤, which is
    excluded by hne_top. -/
theorem chartOrderAt_eq_zero_of_all_nonneg (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hne_top : ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) f q ≠ ⊤)
    (hno_pole : ∀ q, (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f q) :
    ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) f q = 0 := by
  letI := CRS.toRiemannSurface.topology
  letI := CRS.toRiemannSurface.chartedSpace
  haveI := CRS.toRiemannSurface.isManifold
  haveI := CRS.toRiemannSurface.t2
  haveI : CompactSpace CRS.toRiemannSurface.carrier := CRS.compact
  -- Step 1: the corrected function is constant
  obtain ⟨a, ha⟩ := correctedFn_constant CRS f hf hne_top hno_pole
  -- Step 2: the constant a is nonzero
  have ha_ne : a ≠ 0 := by
    intro ha_zero
    -- If a = 0, correctedValue = 0 at every point
    have h_cv_zero : ∀ q, correctedValue (hf q) (hno_pole q) = 0 :=
      fun q => by rw [show correctedValue (hf q) (hno_pole q) =
        correctedFn CRS f hf hno_pole q from rfl, ha q, ha_zero]
    -- By contrapositive of correctedValue_ne_zero_of_eq_zero: order ≠ 0
    have h_ne_zero : ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) f q ≠ 0 :=
      fun q hq => correctedValue_ne_zero_of_eq_zero (hf q) hq (h_cv_zero q)
    -- Since order ≥ 0 and ≠ 0, order > 0 at every point
    have h_pos : ∀ q, (0 : WithTop ℤ) < chartOrderAt (RS := CRS.toRiemannSurface) f q :=
      fun q => lt_of_le_of_ne (hno_pole q) (Ne.symm (h_ne_zero q))
    -- But chartOrderAt_eq_zero_near says near any point, order = 0
    haveI : @ConnectedSpace _ CRS.toRiemannSurface.topology := CRS.toRiemannSurface.connected
    have ⟨q₀⟩ : Nonempty CRS.toRiemannSurface.carrier := inferInstance
    haveI := rs_nhdsNE_neBot (RS := CRS.toRiemannSurface) q₀
    have h_zero_near := chartOrderAt_eq_zero_near f q₀ hf (hne_top q₀)
    obtain ⟨r, hr⟩ := h_zero_near.exists
    exact absurd hr (ne_of_gt (h_pos r))
  -- Step 3: at each q, order = 0 (not > 0)
  intro q
  by_contra hq
  have hpos : (0 : WithTop ℤ) < chartOrderAt (RS := CRS.toRiemannSurface) f q :=
    lt_of_le_of_ne (hno_pole q) (Ne.symm hq)
  -- Positive order ⟹ correctedValue = 0
  have h_cv_zero := correctedValue_eq_zero_of_pos (hf q) hpos
  -- But correctedValue = a ≠ 0
  have h_cv_a : correctedValue (hf q) (hno_pole q) = a := ha q
  -- By proof irrelevance: le_of_lt hpos = hno_pole q (both prove same Prop)
  rw [show correctedValue (hf q) (le_of_lt hpos) =
    correctedValue (hf q) (hno_pole q) from rfl] at h_cv_zero
  rw [h_cv_a] at h_cv_zero
  exact ha_ne h_cv_zero

/-- At a non-pole point with positive chart order and c₀ ≠ 0, the chart order of (f - c₀) is 0.

    Proof: chartRep f p tends to 0 (positive order), so chartRep(f - c₀) p tends to -c₀ ≠ 0.
    The constant -c₀ has meromorphic order 0 < positive order, so by
    `meromorphicOrderAt_add_eq_left_of_lt`, the sum has order 0. -/
theorem chartOrderAt_sub_const_eq_zero_at_pos_order {RS : RiemannSurface}
    {f : RS.carrier → ℂ} {p : RS.carrier} {c₀ : ℂ}
    (hf : IsChartMeromorphic (RS := RS) f)
    (hc₀ : c₀ ≠ 0)
    (hpos : (0 : WithTop ℤ) < chartOrderAt (RS := RS) f p)
    (_hne_top : chartOrderAt (RS := RS) f p ≠ ⊤) :
    chartOrderAt (RS := RS) (fun x => f x - c₀) p = 0 := by
  simp only [chartOrderAt, chartRep_sub_const]
  have hrep : (fun z => chartRep (RS := RS) f p z - c₀) =
      (fun _ => -c₀) + chartRep (RS := RS) f p := by
    ext z; simp [Pi.add_apply, sub_eq_add_neg, add_comm]
  rw [hrep]
  have hconst_mer : MeromorphicAt (fun _ : ℂ => -c₀) (chartPt (RS := RS) p) :=
    MeromorphicAt.const (-c₀) _
  have hconst_ord : meromorphicOrderAt (fun _ : ℂ => -c₀) (chartPt (RS := RS) p) = 0 := by
    rw [meromorphicOrderAt_const]; simp [hc₀]
  have hlt : meromorphicOrderAt (fun _ : ℂ => -c₀) (chartPt (RS := RS) p) <
      meromorphicOrderAt (chartRep (RS := RS) f p) (chartPt (RS := RS) p) := by
    rw [hconst_ord]; exact hpos
  rw [meromorphicOrderAt_add_eq_left_of_lt (hf p) hlt, hconst_ord]

/-- At a zero-order non-pole point where the corrected value ≠ c, chartOrderAt(f - c) = 0.

    Proof: chartRep f p tends to correctedValue v in the punctured neighborhood,
    so chartRep(f-c) p tends to v - c ≠ 0. By `tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero`,
    the meromorphic order is 0. -/
theorem chartOrderAt_sub_const_eq_zero_of_correctedValue_ne {RS : RiemannSurface}
    {f : RS.carrier → ℂ} {p : RS.carrier} {c : ℂ}
    (hf : IsChartMeromorphic (RS := RS) f)
    (hord : chartOrderAt (RS := RS) f p = 0)
    (hne : correctedValue (hf p) (le_of_eq hord.symm) ≠ c) :
    chartOrderAt (RS := RS) (fun x => f x - c) p = 0 := by
  simp only [chartOrderAt, chartRep_sub_const]
  -- The limit of chartRep f p is correctedValue ≠ c
  set v := correctedValue (hf p) (le_of_eq hord.symm) with hv_def
  have hv_ne : v ≠ c := hne
  have hv_tend : Tendsto (chartRep (RS := RS) f p)
      (nhdsWithin (chartPt (RS := RS) p) {chartPt (RS := RS) p}ᶜ)
      (nhds v) :=
    correctedValue_tendsto (hf p) (le_of_eq hord.symm)
  -- chartRep f p - c tends to v - c ≠ 0
  have h_sub_tend : Tendsto (fun z => chartRep (RS := RS) f p z - c)
      (nhdsWithin (chartPt (RS := RS) p) {chartPt (RS := RS) p}ᶜ)
      (nhds (v - c)) :=
    hv_tend.sub tendsto_const_nhds
  have h_sub_ne : v - c ≠ 0 := sub_ne_zero.mpr hv_ne
  -- MeromorphicAt for the difference
  have h_mer : MeromorphicAt (fun z => chartRep (RS := RS) f p z - c) (chartPt (RS := RS) p) :=
    (hf p).sub (MeromorphicAt.const c _)
  -- By the iff: ∃ nonzero limit → order = 0
  exact (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero h_mer).mp ⟨v - c, h_sub_ne, h_sub_tend⟩

/-- At a non-pole point where chartOrderAt f p = 0, the corrected value is locally bounded:
    it equals the limit of chartRep f p at chartPt p. -/
noncomputable def correctedValueAt {RS : RiemannSurface}
    (f : RS.carrier → ℂ) (hf : IsChartMeromorphic (RS := RS) f)
    (p : RS.carrier) (hord : chartOrderAt (RS := RS) f p = 0) : ℂ :=
  correctedValue (hf p) (le_of_eq hord.symm)

/-- Corrected values respect subtraction by constants at non-pole points. -/
theorem correctedValue_sub_const_eq {g : ℂ → ℂ} {x c : ℂ}
    (hg : MeromorphicAt g x)
    (hord_g : (0 : WithTop ℤ) ≤ meromorphicOrderAt g x)
    (hord_sub : (0 : WithTop ℤ) ≤ meromorphicOrderAt (fun z => g z - c) x) :
    correctedValue (hg.sub (MeromorphicAt.const c _)) hord_sub = correctedValue hg hord_g - c := by
  haveI : Filter.NeBot (nhdsWithin x ({x}ᶜ : Set ℂ)) :=
    ConnectedSpace.neBot_nhdsWithin_compl_of_nontrivial_of_t1space x
  have htend_g :
      Tendsto g (nhdsWithin x {x}ᶜ) (nhds (correctedValue hg hord_g)) :=
    correctedValue_tendsto hg hord_g
  have htend_sub₁ :
      Tendsto (fun z => g z - c) (nhdsWithin x {x}ᶜ) (nhds (correctedValue hg hord_g - c)) :=
    htend_g.sub tendsto_const_nhds
  have htend_sub₂ :
      Tendsto (fun z => g z - c) (nhdsWithin x {x}ᶜ)
        (nhds (correctedValue (hg.sub (MeromorphicAt.const c _)) hord_sub)) :=
    correctedValue_tendsto (hg.sub (MeromorphicAt.const c _)) hord_sub
  exact tendsto_nhds_unique htend_sub₂ htend_sub₁

/-- Positive order of `g - c` forces the corrected value of `g` to be `c`
    (at non-pole points). -/
theorem correctedValue_eq_const_of_sub_pos {g : ℂ → ℂ} {x c : ℂ}
    (hg : MeromorphicAt g x)
    (hord_g : (0 : WithTop ℤ) ≤ meromorphicOrderAt g x)
    (hpos_sub : (0 : WithTop ℤ) < meromorphicOrderAt (fun z => g z - c) x) :
    correctedValue hg hord_g = c := by
  have hord_sub : (0 : WithTop ℤ) ≤ meromorphicOrderAt (fun z => g z - c) x := le_of_lt hpos_sub
  have hcv_sub_zero :
      correctedValue (hg.sub (MeromorphicAt.const c _)) hord_sub = 0 :=
    correctedValue_eq_zero_of_pos (hg.sub (MeromorphicAt.const c _)) hpos_sub
  have hcv_sub :
      correctedValue (hg.sub (MeromorphicAt.const c _)) hord_sub =
        correctedValue hg hord_g - c :=
    correctedValue_sub_const_eq hg hord_g hord_sub
  have hsub_zero : correctedValue hg hord_g - c = 0 := by
    calc
      correctedValue hg hord_g - c =
          correctedValue (hg.sub (MeromorphicAt.const c _)) hord_sub := hcv_sub.symm
      _ = 0 := hcv_sub_zero
  exact sub_eq_zero.mp hsub_zero

/-- Under chart-level continuity, positive order of `f - c` at `p` forces `f p = c`. -/
theorem eq_const_of_shift_pos_of_continuousAt {RS : RiemannSurface}
    {f : RS.carrier → ℂ} {p : RS.carrier} {c : ℂ}
    (hf : IsChartMeromorphic (RS := RS) f)
    (hcont : ContinuousAt (chartRep (RS := RS) f p) (chartPt (RS := RS) p))
    (hpos : (0 : WithTop ℤ) < chartOrderAt (RS := RS) (fun x => f x - c) p) :
    f p = c := by
  let g : RS.carrier → ℂ := fun x => f x - c
  have hg : IsChartMeromorphic (RS := RS) g :=
    chartMeromorphic_sub_const (RS := RS) c hf
  have hrep_sub : chartRep (RS := RS) g p = fun z => chartRep (RS := RS) f p z - c := by
    ext z
    simp [g, chartRep, Function.comp]
  have hcont_g : ContinuousAt (chartRep (RS := RS) g p) (chartPt (RS := RS) p) := by
    have hcont_sub : ContinuousAt (fun z => chartRep (RS := RS) f p z - c)
        (chartPt (RS := RS) p) := hcont.sub continuousAt_const
    simpa [hrep_sub]
      using hcont_sub
  have hnonneg_g : (0 : WithTop ℤ) ≤ chartOrderAt (RS := RS) g p := le_of_lt hpos
  have hcv_eq : correctedValue (hg p) hnonneg_g = g p := by
    -- The corrected value agrees with point-value at continuous non-polar points.
    have hcv_chart :
        correctedValue (hg p) hnonneg_g =
          chartRep (RS := RS) g p (chartPt (RS := RS) p) := by
      exact correctedValue_eq_of_continuousAt (hg p) hnonneg_g hcont_g
    simpa [chartRep_apply_chartPt] using hcv_chart
  have hcv_zero : correctedValue (hg p) hnonneg_g = 0 :=
    correctedValue_eq_zero_of_pos (hg p) hpos
  have hg_p_zero : g p = 0 := by
    exact hcv_eq.symm.trans hcv_zero
  simpa [g, sub_eq_zero] using hg_p_zero

/-- Under chart-level continuity, point-value equality `f p = c` forces positive order of `f - c`. -/
theorem shift_pos_of_eq_const_of_continuousAt {RS : RiemannSurface}
    {f : RS.carrier → ℂ} {p : RS.carrier} {c : ℂ}
    (hf : IsChartMeromorphic (RS := RS) f)
    (hcont : ContinuousAt (chartRep (RS := RS) f p) (chartPt (RS := RS) p))
    (hEq : f p = c) :
    (0 : WithTop ℤ) < chartOrderAt (RS := RS) (fun x => f x - c) p := by
  let g : RS.carrier → ℂ := fun x => f x - c
  have hg : IsChartMeromorphic (RS := RS) g :=
    chartMeromorphic_sub_const (RS := RS) c hf
  have hrep_sub : chartRep (RS := RS) g p = fun z => chartRep (RS := RS) f p z - c := by
    ext z
    simp [g, chartRep, Function.comp]
  have hcont_g : ContinuousAt (chartRep (RS := RS) g p) (chartPt (RS := RS) p) := by
    have hcont_sub : ContinuousAt (fun z => chartRep (RS := RS) f p z - c)
        (chartPt (RS := RS) p) := hcont.sub continuousAt_const
    simpa [hrep_sub] using hcont_sub
  have hgp0 : g p = 0 := by
    simpa [g, sub_eq_zero] using hEq
  exact chartOrderAt_pos_of_zero (RS := RS) hg p hgp0 hcont_g

/-- Under chart-level continuity, positive order of `f - c` is equivalent to `f p = c`. -/
private theorem shift_pos_iff_eq_const_of_continuousAt {RS : RiemannSurface}
    {f : RS.carrier → ℂ} {p : RS.carrier} {c : ℂ}
    (hf : IsChartMeromorphic (RS := RS) f)
    (hcont : ContinuousAt (chartRep (RS := RS) f p) (chartPt (RS := RS) p)) :
    ((0 : WithTop ℤ) < chartOrderAt (RS := RS) (fun x => f x - c) p) ↔ f p = c := by
  constructor
  · intro hpos
    exact eq_const_of_shift_pos_of_continuousAt (RS := RS) hf hcont hpos
  · intro hEq
    exact shift_pos_of_eq_const_of_continuousAt (RS := RS) hf hcont hEq

/-- Regular-point continuity gives point-value/corrected-value compatibility. -/
theorem regularValue_compat_of_continuous_regular {RS : RiemannSurface}
    {f : RS.carrier → ℂ}
    (hf : IsChartMeromorphic (RS := RS) f)
    (hcont_reg : ∀ p, (0 : WithTop ℤ) ≤ chartOrderAt (RS := RS) f p →
      ContinuousAt (chartRep (RS := RS) f p) (chartPt (RS := RS) p)) :
    ∀ p (hp : (0 : WithTop ℤ) ≤ chartOrderAt (RS := RS) f p),
      f p = correctedValue (hf p) hp := by
  intro p hp
  have hcv_chart :
      correctedValue (hf p) hp =
        chartRep (RS := RS) f p (chartPt (RS := RS) p) :=
    correctedValue_eq_of_continuousAt (hf p) hp (hcont_reg p hp)
  simpa [chartRep_apply_chartPt] using hcv_chart.symm

/-- Regular-point MDifferentiability gives point-value/corrected-value compatibility. -/
theorem regularValue_compat_of_mdifferentiable_regular {RS : RiemannSurface}
    {f : RS.carrier → ℂ}
    (hf : IsChartMeromorphic (RS := RS) f)
    (hmd_reg : ∀ p, (0 : WithTop ℤ) ≤ chartOrderAt (RS := RS) f p →
      @MDifferentiableAt ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ)
        RS.carrier RS.topology RS.chartedSpace ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ℂ _ _ f p) :
    ∀ p (hp : (0 : WithTop ℤ) ≤ chartOrderAt (RS := RS) f p),
      f p = correctedValue (hf p) hp := by
  intro p hp
  exact regularValue_compat_of_continuous_regular (RS := RS) hf
    (fun q hq =>
      continuousAt_chartRep_of_mdifferentiableAt (RS := RS) f q (hmd_reg q hq)) p hp

/-- Global MDifferentiability gives point-value/corrected-value compatibility
at every non-polar point. -/
theorem regularValue_compat_of_mdifferentiable {RS : RiemannSurface}
    {f : RS.carrier → ℂ}
    (hf : IsChartMeromorphic (RS := RS) f)
    (hmd : @MDifferentiable ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ)
      RS.carrier RS.topology RS.chartedSpace
      ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ℂ _ _ f) :
    ∀ p (hp : (0 : WithTop ℤ) ≤ chartOrderAt (RS := RS) f p),
      f p = correctedValue (hf p) hp := by
  intro p hp
  exact regularValue_compat_of_mdifferentiable_regular (RS := RS) hf
    (fun q _hq => hmd q) p hp

/-!
## Local Pole Preimage Lemma

The fundamental local result: at a pole of a meromorphic function, the local sum
of orders of g - c is 0 for large |c|. This is the engine behind the degree
theory proof.

The proof uses:
1. Analytic extension of 1/g at the pole (via `exists_analyticExtension_of_nonneg_order`)
2. Local mapping theorem for the preimage count
3. Derivative argument for simplicity of preimages
4. Compactness for containment of preimages in a small ball
-/

/-- **Pole invariance (ℂ version)**: subtracting a constant doesn't change
    the meromorphic order at a pole. -/
theorem meromorphicOrderAt_sub_const_at_pole_loc {g : ℂ → ℂ} {z₀ : ℂ} (c : ℂ)
    (hpole : meromorphicOrderAt g z₀ < 0) :
    meromorphicOrderAt (fun z => g z - c) z₀ = meromorphicOrderAt g z₀ := by
  by_cases hc : c = 0
  · subst hc; simp
  · have hrep : (fun z => g z - c) = g + fun _ => -c := by
      ext z; simp [Pi.add_apply, sub_eq_add_neg]
    rw [hrep]
    apply meromorphicOrderAt_add_eq_left_of_lt (MeromorphicAt.const (-c) _)
    rw [meromorphicOrderAt_const]; simp [hc]; exact hpole

/-- **Simple zero order**: An analytic function with f(z₀) = 0 and f'(z₀) ≠ 0
    has meromorphic order 1 at z₀. -/
theorem meromorphicOrderAt_eq_one_of_simple_zero {f : ℂ → ℂ} {z₀ : ℂ}
    (hf_ana : AnalyticAt ℂ f z₀) (hfz : f z₀ = 0) (hf' : deriv f z₀ ≠ 0) :
    meromorphicOrderAt f z₀ = 1 := by
  have h1 : analyticOrderAt (f · - f z₀) z₀ = 1 :=
    hf_ana.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hf'
  rw [hfz] at h1
  have h2 : analyticOrderAt (f · - (0 : ℂ)) z₀ = analyticOrderAt f z₀ := by
    congr 1; ext z; simp
  rw [h2] at h1
  rw [hf_ana.meromorphicOrderAt_eq, h1]; rfl

/-- **Local pole preimage lemma.** At a pole of a meromorphic function g of order
    -n (n ≥ 1), there exist r > 0 (with r ≤ ρ) and C > 0 such that for |c| > C:
    there is a finite set S ⊆ B(z₀, r) containing all points with nonzero finite
    meromorphicOrderAt of (g - c), and the sum of orders over S is 0.

    The set S consists of z₀ (contributing -n) and n simple zeros of g - c
    (each contributing +1), so the total is 0. -/
theorem meromorphic_pole_local_sum_zero {g : ℂ → ℂ} {z₀ : ℂ} {ρ : ℝ}
    (hg : MeromorphicAt g z₀) (hpole : meromorphicOrderAt g z₀ < 0)
    (hρ : 0 < ρ) :
    ∃ r > 0, r ≤ ρ ∧ ∃ C > 0, ∀ c : ℂ, C < ‖c‖ →
      ∃ (S : Finset ℂ),
        -- S is contained in B(z₀, r)
        (∀ z ∈ S, ‖z - z₀‖ < r) ∧
        -- S contains all points with nonzero finite order for g - c in B(z₀, r)
        (∀ z, ‖z - z₀‖ < r → meromorphicOrderAt (fun w => g w - c) z ≠ 0 →
          meromorphicOrderAt (fun w => g w - c) z ≠ ⊤ → z ∈ S) ∧
        -- The sum of orders over S is 0
        S.sum (fun z => (meromorphicOrderAt (fun w => g w - c) z).getD 0) = 0 := by
  have hne_top : meromorphicOrderAt g z₀ ≠ ⊤ := by
    intro h; rw [h] at hpole; exact absurd le_top (not_le.mpr hpole)
  set m : ℤ := (meromorphicOrderAt g z₀).untop₀ with hm_def
  have hm_coe : meromorphicOrderAt g z₀ = (m : WithTop ℤ) :=
    (WithTop.coe_untop₀_of_ne_top hne_top).symm
  have hm_neg : m < 0 := by
    have hpole' : ((m : WithTop ℤ) < (0 : WithTop ℤ)) := by
      simpa [hm_coe] using hpole
    exact WithTop.coe_lt_coe.mp hpole'
  set n : ℕ := (-m).toNat with hn_def
  have hn_eq : (n : ℤ) = -m := Int.toNat_of_nonneg (le_of_lt (neg_pos.mpr hm_neg))
  have hn_pos : 1 ≤ n := by omega
  have hm_eq : meromorphicOrderAt g z₀ = (-(n : ℤ) : WithTop ℤ) := by
    rw [hm_coe]; congr 1; linarith [hn_eq]
  have hg_inv : MeromorphicAt g⁻¹ z₀ := hg.inv
  have hg_inv_ord : meromorphicOrderAt g⁻¹ z₀ = (n : ℤ) := by
    rw [meromorphicOrderAt_inv, hm_eq]; simp
  have hg_inv_nonneg : (0 : WithTop ℤ) ≤ meromorphicOrderAt g⁻¹ z₀ := by
    rw [hg_inv_ord]
    exact WithTop.coe_le_coe.mpr (Int.natCast_nonneg n)
  have hg_inv_ne_top : meromorphicOrderAt g⁻¹ z₀ ≠ ⊤ := by
    rw [hg_inv_ord]; exact WithTop.coe_ne_top
  obtain ⟨H, hH_ana, hH_agree, hH_mord⟩ :=
    exists_analyticExtension_of_nonneg_order hg_inv hg_inv_ne_top hg_inv_nonneg
  have hH_mord_eq : meromorphicOrderAt H z₀ = (n : ℤ) := by rw [hH_mord, hg_inv_ord]
  have hH_aord : analyticOrderAt H z₀ = n := by
    have h := hH_ana.meromorphicOrderAt_eq
    rw [hH_mord_eq] at h
    cases hn' : analyticOrderAt H z₀ with
    | top => simp [hn'] at h
    | coe k => simp [hn'] at h; exact_mod_cast h.symm
  have hH0 : H z₀ = 0 := by
    rw [← hH_ana.analyticOrderAt_ne_zero]
    rw [hH_aord]
    exact_mod_cast Nat.one_le_iff_ne_zero.mp hn_pos
  obtain ⟨r_ana, hr_ana_pos, hH_ana_ball⟩ :=
    Metric.eventually_nhds_iff.mp hH_ana.eventually_analyticAt
  obtain ⟨r_agr, hr_agr_pos, h_agree_ball⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp hH_agree)
  obtain ⟨r, hr_pos, hr_le_bound, ε, hε_pos, h_iso, h_count, h_deriv_ne⟩ :=
    local_mapping_theorem (h := H) (z₀ := z₀) (k := n) (r_bound := min ρ (min r_ana r_agr))
      hn_pos hH_ana hH0 hH_aord (lt_min hρ (lt_min hr_ana_pos hr_agr_pos))
  have hr_le_ρ : r ≤ ρ := le_trans hr_le_bound (min_le_left _ _)
  have hr_le_ana : r ≤ r_ana := le_trans hr_le_bound (le_trans (min_le_right _ _) (min_le_left _ _))
  have hr_le_agr : r ≤ r_agr := le_trans hr_le_bound (le_trans (min_le_right _ _) (min_le_right _ _))
  set C : ℝ := ε⁻¹ + 1 with hC_def
  have hC_pos : 0 < C := by
    have : (0 : ℝ) ≤ ε⁻¹ := inv_nonneg.mpr (le_of_lt hε_pos)
    linarith
  refine ⟨r, hr_pos, hr_le_ρ, C, hC_pos, ?_⟩
  intro c hc
  set w : ℂ := c⁻¹ with hw_def
  have hc_ne_zero : c ≠ 0 := by
    intro hc0
    have : ‖c‖ = 0 := by simpa [hc0]
    linarith [hc]
  have hc_norm_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc_ne_zero
  have hw_ne : w ≠ 0 := by
    simpa [hw_def] using inv_ne_zero hc_ne_zero
  have hw_norm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
  have hw_norm_lt : ‖w‖ < ε := by
    have hε_inv_lt : ε⁻¹ < ‖c‖ := by
      have hC_lt : C < ‖c‖ := hc
      linarith [hC_def]
    have h_inv : (‖c‖)⁻¹ < ε := (inv_lt_comm₀ hc_norm_pos hε_pos).2 hε_inv_lt
    simpa [hw_def, norm_inv] using h_inv
  have h_count_w : {z : ℂ | ‖z - z₀‖ < r ∧ H z = w}.ncard = n :=
    h_count w hw_norm_pos hw_norm_lt
  set T : Set ℂ := {z : ℂ | ‖z - z₀‖ < r ∧ H z = w}
  have hT_ncard : T.ncard = n := by
    simpa [T] using h_count_w
  have hn_pos' : 0 < n := Nat.succ_le_iff.mp hn_pos
  have hT_finite : T.Finite := Set.finite_of_ncard_pos (by simpa [hT_ncard] using hn_pos')
  refine ⟨insert z₀ hT_finite.toFinset, ?_, ?_, ?_⟩
  · -- S is contained in B(z₀, r)
    intro z hzS
    rcases Finset.mem_insert.mp hzS with rfl | hzT
    · simpa using hr_pos
    · exact (hT_finite.mem_toFinset.mp hzT).1
  · -- Capture all nonzero finite-order points of (g - c) in the ball
    intro z hz hord_ne0 hord_ne_top
    by_cases hzz₀ : z = z₀
    · exact Finset.mem_insert.mpr (Or.inl hzz₀)
    · refine Finset.mem_insert.mpr (Or.inr ?_)
      have hzT : z ∈ T := by
        have hHz_ne0 : H z ≠ 0 := h_iso z hz hzz₀
        by_cases hHw : H z = w
        · exact ⟨hz, hHw⟩
        · have hH_ana_z : AnalyticAt ℂ H z :=
            hH_ana_ball (lt_of_lt_of_le (by rwa [dist_eq_norm]) hr_le_ana)
          set z0 : ℂ := z₀ with hz0_def
          have hg_eq_near : g =ᶠ[nhds z] fun u => (H u)⁻¹ := by
            set d : ℝ := min (r_agr - dist z z0) (dist z z0 / 2) with hd_def
            have hd_pos : 0 < d := by
              have hz_dist : dist z z0 < r_agr := by
                simpa [hz0_def] using (lt_of_lt_of_le (by rwa [dist_eq_norm]) hr_le_agr)
              have hz_dist_pos : 0 < dist z z0 := by
                simpa [hz0_def] using (dist_pos.mpr hzz₀)
              have hleft : 0 < r_agr - dist z z0 := by linarith
              have hright : 0 < dist z z0 / 2 := by positivity
              simpa [hd_def] using lt_min hleft hright
            exact Filter.eventually_of_mem (Metric.ball_mem_nhds z hd_pos) (fun u hu => by
              have hu_dist : dist u z < d := Metric.mem_ball.mp hu
              have hu_agr0 : dist u z0 < r_agr := by
                have hdu : dist u z < r_agr - dist z z0 := lt_of_lt_of_le hu_dist (min_le_left _ _)
                linarith [dist_triangle u z z0]
              have hu_ne0 : u ≠ z0 := by
                intro hu0
                subst hu0
                have hu_dist' : dist z z0 < d := by simpa [dist_comm] using hu_dist
                have : dist z z0 < dist z z0 / 2 := by
                  exact lt_of_lt_of_le hu_dist' (min_le_right _ _)
                have hnonneg : 0 ≤ dist z z0 := dist_nonneg
                linarith
              calc g u = ((g u)⁻¹)⁻¹ := (inv_inv (g u)).symm
                _ = (g⁻¹ u)⁻¹ := rfl
                _ = (H u)⁻¹ := by
                  have hu_agr : dist u z₀ < r_agr := by simpa [hz0_def] using hu_agr0
                  have hu_ne : u ∈ ({z₀} : Set ℂ)ᶜ := by
                    simpa [hz0_def] using (Set.mem_compl_singleton_iff.mpr hu_ne0)
                  rw [h_agree_ball hu_agr hu_ne])
          have h_congr : (fun u => g u - c) =ᶠ[nhdsWithin z {z}ᶜ] (fun u => (H u)⁻¹ - c) :=
            (hg_eq_near.filter_mono nhdsWithin_le_nhds).mono fun u hu => by
              show g u - c = (H u)⁻¹ - c
              rw [hu]
          have h_inv_ne_c : (H z)⁻¹ ≠ c := by
            intro hEq
            apply hHw
            have : H z = c⁻¹ := by simpa using congrArg Inv.inv hEq
            simpa [hw_def] using this
          have h_ord_zero : meromorphicOrderAt (fun u => (H u)⁻¹ - c) z = 0 := by
            have h_ana : AnalyticAt ℂ (fun u => (H u)⁻¹ - c) z :=
              (hH_ana_z.inv hHz_ne0).sub analyticAt_const
            exact (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero h_ana.meromorphicAt).mp
              ⟨(H z)⁻¹ - c, sub_ne_zero.mpr h_inv_ne_c,
                h_ana.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩
          have h_ord : meromorphicOrderAt (fun u => g u - c) z = 0 := by
            rw [meromorphicOrderAt_congr h_congr]
            exact h_ord_zero
          exact (hord_ne0 h_ord).elim
      exact hT_finite.mem_toFinset.mpr hzT
  · -- Sum of local orders in S is zero: pole contribution (-n) + n simple zeros (+1)
    have hz0_not_mem : z₀ ∉ hT_finite.toFinset := by
      intro hz0_mem
      have hz0_in_T : z₀ ∈ T := hT_finite.mem_toFinset.mp hz0_mem
      exact hw_ne (by simpa [hH0] using hz0_in_T.2.symm)
    rw [Finset.sum_insert hz0_not_mem]
    have hz0_term : (meromorphicOrderAt (fun u => g u - c) z₀).getD 0 = -(n : ℤ) := by
      have hz0_ord : meromorphicOrderAt (fun u => g u - c) z₀ = (-(n : ℤ) : WithTop ℤ) := by
        rw [meromorphicOrderAt_sub_const_at_pole_loc c hpole, hm_eq]
      exact congrArg (fun t : WithTop ℤ => t.getD 0) hz0_ord
    have hsum_T :
        hT_finite.toFinset.sum (fun z => (meromorphicOrderAt (fun u => g u - c) z).getD 0) =
          (n : ℤ) := by
      have h_each_one : ∀ z ∈ hT_finite.toFinset,
          (meromorphicOrderAt (fun u => g u - c) z).getD 0 = 1 := by
        intro z hz_fin
        have hzT : z ∈ T := hT_finite.mem_toFinset.mp hz_fin
        have hz_ball : ‖z - z₀‖ < r := hzT.1
        have hHz : H z = w := hzT.2
        have hzz0 : z ≠ z₀ := by
          intro hEq
          have hw0 : w = 0 := by
            calc
              w = H z := hHz.symm
              _ = H z₀ := by simpa [hEq]
              _ = 0 := hH0
          exact hw_ne hw0
        have hHz_ne0 : H z ≠ 0 := by
          rw [hHz]
          exact hw_ne
        have hH_ana_z : AnalyticAt ℂ H z :=
          hH_ana_ball (lt_of_lt_of_le (by rwa [dist_eq_norm]) hr_le_ana)
        have hderiv_z : deriv H z ≠ 0 := h_deriv_ne z hz_ball hzz0
        set z0 : ℂ := z₀ with hz0_def
        set d : ℝ := min (min (r_agr - dist z z0) (r - dist z z0)) (dist z z0 / 2) with hd_def
        have hd_pos : 0 < d := by
          have hz_dist_agr : dist z z0 < r_agr := by
            simpa [hz0_def] using (lt_of_lt_of_le (by rwa [dist_eq_norm]) hr_le_agr)
          have hz_dist_r : dist z z0 < r := by
            simpa [dist_eq_norm] using hz_ball
          have hz_dist_pos : 0 < dist z z0 := by
            simpa [hz0_def] using (dist_pos.mpr hzz0)
          have h1 : 0 < r_agr - dist z z0 := by linarith
          have h2 : 0 < r - dist z z0 := by linarith
          have h3 : 0 < dist z z0 / 2 := by positivity
          have h12 : 0 < min (r_agr - dist z z0) (r - dist z z0) := lt_min h1 h2
          simpa [hd_def] using lt_min h12 h3
        have hg_eq_near : g =ᶠ[nhds z] fun u => (H u)⁻¹ := by
          exact Filter.eventually_of_mem (Metric.ball_mem_nhds z hd_pos) (fun u hu => by
            have hu_dist : dist u z < d := Metric.mem_ball.mp hu
            have hu_agr0 : dist u z0 < r_agr := by
              have hu1 : dist u z < r_agr - dist z z0 := by
                exact lt_of_lt_of_le hu_dist (le_trans (min_le_left _ _) (min_le_left _ _))
              linarith [dist_triangle u z z0]
            have hu_ne0 : u ≠ z0 := by
              intro hu0
              subst hu0
              have hu_dist' : dist z z0 < d := by simpa [dist_comm] using hu_dist
              have : dist z z0 < dist z z0 / 2 := by
                exact lt_of_lt_of_le hu_dist' (min_le_right _ _)
              have hnonneg : 0 ≤ dist z z0 := dist_nonneg
              linarith
            have hu_agr : dist u z₀ < r_agr := by simpa [hz0_def] using hu_agr0
            have hu_ne : u ∈ ({z₀} : Set ℂ)ᶜ := by
              simpa [hz0_def] using (Set.mem_compl_singleton_iff.mpr hu_ne0)
            calc
              g u = ((g u)⁻¹)⁻¹ := (inv_inv (g u)).symm
              _ = (g⁻¹ u)⁻¹ := rfl
              _ = (H u)⁻¹ := by rw [h_agree_ball hu_agr hu_ne])
        have hH_near : ∀ᶠ u in nhds z, H u ≠ 0 := by
          exact Filter.eventually_of_mem (Metric.ball_mem_nhds z hd_pos) (fun u hu => by
            have hu_dist : dist u z < d := Metric.mem_ball.mp hu
            have hu_r0 : dist u z0 < r := by
              have hu1 : dist u z < r - dist z z0 := by
                exact lt_of_lt_of_le hu_dist (le_trans (min_le_left _ _) (min_le_right _ _))
              linarith [dist_triangle u z z0]
            have hu_ne0 : u ≠ z0 := by
              intro hu0
              subst hu0
              have hu_dist' : dist z z0 < d := by simpa [dist_comm] using hu_dist
              have : dist z z0 < dist z z0 / 2 := by
                exact lt_of_lt_of_le hu_dist' (min_le_right _ _)
              have hnonneg : 0 ≤ dist z z0 := dist_nonneg
              linarith
            have hu_r : dist u z₀ < r := by simpa [hz0_def] using hu_r0
            have hu_ne : u ≠ z₀ := by simpa [hz0_def] using hu_ne0
            exact h_iso u (by simpa [dist_eq_norm] using hu_r) hu_ne)
        have h_mul_congr :
            (fun u => (g u - c) * H u) =ᶠ[nhdsWithin z {z}ᶜ] (fun u => 1 - c * H u) := by
          exact ((hg_eq_near.and hH_near).filter_mono nhdsWithin_le_nhds).mono (fun u hu => by
            rcases hu with ⟨hu_g, hu_H⟩
            calc
              (g u - c) * H u = ((H u)⁻¹ - c) * H u := by rw [hu_g]
              _ = 1 - c * H u := by
                rw [sub_mul, inv_mul_cancel₀ hu_H])
        have hcw : c * w = 1 := by
          simp [hw_def, hc_ne_zero]
        have h_one_minus :
            (fun u => 1 - c * H u) = (fun _ : ℂ => -c) * (fun u => H u - w) := by
          funext u
          calc
            1 - c * H u = c * w - c * H u := by simpa [hcw]
            _ = (-c) * (H u - w) := by ring
        have h_ord_H_sub_w : meromorphicOrderAt (fun u => H u - w) z = 1 := by
          have hzero_z : (fun u => H u - w) z = 0 := by simpa [hHz]
          have hderiv_sub : deriv (fun u => H u - w) z ≠ 0 := by simpa using hderiv_z
          exact meromorphicOrderAt_eq_one_of_simple_zero
            (hH_ana_z.sub analyticAt_const) hzero_z hderiv_sub
        have h_ord_one_minus : meromorphicOrderAt (fun u => 1 - c * H u) z = 1 := by
          rw [h_one_minus]
          have hmul :
              meromorphicOrderAt ((fun _ : ℂ => -c) * (fun u => H u - w)) z =
                meromorphicOrderAt (fun u => H u - w) z :=
            meromorphicOrderAt_mul_of_ne_zero (x := z)
              (f := fun u => H u - w) (g := fun _ : ℂ => -c)
              (hg := analyticAt_const) (hg' := by simpa using neg_ne_zero.mpr hc_ne_zero)
          rw [hmul, h_ord_H_sub_w]
        have h_ord_mul : meromorphicOrderAt (fun u => (g u - c) * H u) z = 1 := by
          rw [meromorphicOrderAt_congr h_mul_congr]
          exact h_ord_one_minus
        have h_ord_sub : meromorphicOrderAt (fun u => g u - c) z = 1 := by
          have hmul :
              meromorphicOrderAt (fun u => H u * (g u - c)) z =
                meromorphicOrderAt (fun u => g u - c) z :=
            meromorphicOrderAt_mul_of_ne_zero (x := z)
              (f := fun u => g u - c) (g := H) hH_ana_z hHz_ne0
          have hmul' : meromorphicOrderAt (fun u => H u * (g u - c)) z = 1 := by
            have hswap : (fun u => H u * (g u - c)) = (fun u => (g u - c) * H u) := by
              funext u
              ring
            rw [hswap]
            exact h_ord_mul
          rw [hmul] at hmul'
          exact hmul'
        exact congrArg (fun t : WithTop ℤ => t.getD 0) h_ord_sub
      calc
        hT_finite.toFinset.sum (fun z => (meromorphicOrderAt (fun u => g u - c) z).getD 0)
            = hT_finite.toFinset.sum (fun _ => (1 : ℤ)) := by
              refine Finset.sum_congr rfl ?_
              intro z hz
              exact h_each_one z hz
        _ = (hT_finite.toFinset.card : ℤ) := by simp
        _ = (n : ℤ) := by
              have hcard : hT_finite.toFinset.card = n := by
                calc
                  hT_finite.toFinset.card = T.ncard := by
                    symm
                    exact Set.ncard_eq_toFinset_card T hT_finite
                  _ = n := hT_ncard
              exact_mod_cast hcard
    rw [hz0_term, hsum_T]
    ring
/-- If G is analytic at w and G(w) ≠ c, then meromorphicOrderAt(G - c, w) = 0. -/
private theorem meromorphicOrderAt_analytic_sub_const_eq_zero' {G : ℂ → ℂ} {w c : ℂ}
    (hG : AnalyticAt ℂ G w) (hne : G w ≠ c) :
    meromorphicOrderAt (fun z => G z - c) w = 0 := by
  have h_ana : AnalyticAt ℂ (fun z => G z - c) w := hG.sub analyticAt_const
  have h_ne : G w - c ≠ 0 := sub_ne_zero.mpr hne
  exact (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero h_ana.meromorphicAt).mp
    ⟨G w - c, h_ne, h_ana.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩

/-- At a non-pole point q with chartOrderAt(f - c₀, q) = 0, there exists a neighborhood and
    ε > 0 such that chartOrderAt(f - c, r) = 0 for r near q and c near c₀. -/
private theorem chartOrderAt_sub_const_eq_zero_near_c₀
    {f : RS.carrier → ℂ} {q : RS.carrier} {c₀ : ℂ}
    (hf : IsChartMeromorphic (RS := RS) f)
    (hne_top : chartOrderAt (RS := RS) f q ≠ ⊤)
    (hord : (0 : WithTop ℤ) ≤ chartOrderAt (RS := RS) f q)
    (hzero : chartOrderAt (RS := RS) (fun x => f x - c₀) q = 0) :
    ∃ V ∈ @nhds _ RS.topology q, ∃ ε : ℝ, 0 < ε ∧
      ∀ r ∈ V, ∀ c : ℂ, ‖c - c₀‖ < ε →
        chartOrderAt (RS := RS) (fun x => f x - c) r = 0 := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  obtain ⟨G, hG_ana, hG_agree, _⟩ :=
    exists_analyticExtension_of_nonneg_order (hf q) hne_top hord
  set z₀ := chartPt (RS := RS) q
  set e_q := extChartAt 𝓘(ℂ, ℂ) q
  -- G(z₀) ≠ c₀: chartOrderAt(f-c₀, q) = 0 means G(z₀) - c₀ ≠ 0
  have hG_ne_c₀ : G z₀ ≠ c₀ := by
    intro h_eq
    -- meromorphicOrderAt(chartRep f q - c₀, z₀) = 0 from hzero
    have h0 : meromorphicOrderAt (fun z => chartRep (RS := RS) f q z - c₀) z₀ = 0 := by
      rw [← chartRep_sub_const]; exact hzero
    -- meromorphicOrderAt(G - c₀, z₀) = 0 by agreement
    have h_congr : (fun z => chartRep (RS := RS) f q z - c₀)
        =ᶠ[nhdsWithin z₀ {z₀}ᶜ] (fun z => G z - c₀) := by
      filter_upwards [hG_agree] with z hz; rw [hz]
    rw [meromorphicOrderAt_congr h_congr] at h0
    -- But G(z₀) = c₀ → (G - c₀)(z₀) = 0 → G - c₀ has positive order
    have h_ana : AnalyticAt ℂ (fun z => G z - c₀) z₀ := hG_ana.sub analyticAt_const
    have h_vanish : (fun z => G z - c₀) z₀ = 0 := by simp [h_eq]
    -- meromorphicOrderAt = 0 → analyticOrderAt = 0 → f(z₀) ≠ 0, contradicting h_vanish
    have h_aord_zero : analyticOrderAt (fun z => G z - c₀) z₀ = 0 := by
      have h_eq := h_ana.meromorphicOrderAt_eq
      rw [h0] at h_eq
      cases h : analyticOrderAt (fun z => G z - c₀) z₀ with
      | top => simp [h] at h_eq
      | coe n => simp [h] at h_eq; exact_mod_cast h_eq.symm
    exact (h_ana.analyticOrderAt_ne_zero.mpr h_vanish) h_aord_zero
  set δ := ‖G z₀ - c₀‖ with hδ_def
  have hδ_pos : 0 < δ := norm_pos_iff.mpr (sub_ne_zero.mpr hG_ne_c₀)
  -- Build filter: G analytic, |G(w) - c₀| > δ/2, agrees with chartRep f q
  have h_evt : ∀ᶠ w in nhds z₀,
      AnalyticAt ℂ G w ∧ δ / 2 < ‖G w - c₀‖ ∧
      (w ≠ z₀ → chartRep (RS := RS) f q w = G w) := by
    refine (hG_ana.eventually_analyticAt).and ((?_ : ∀ᶠ w in nhds z₀,
      δ / 2 < ‖G w - c₀‖).and ?_)
    · have h_cont : ContinuousAt (fun w => ‖G w - c₀‖) z₀ :=
        (hG_ana.continuousAt.sub continuousAt_const).norm
      exact h_cont.preimage_mem_nhds (Ioi_mem_nhds (by linarith : δ / 2 < δ))
    · exact (eventually_nhdsWithin_iff.mp hG_agree).mono fun w hw hne => hw hne
  obtain ⟨U, hU_sub, hU_open, hz₀_U⟩ := eventually_nhds_iff.mp h_evt
  -- Pull back to manifold
  have he_src : e_q.source ∈ nhds q :=
    (isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) q).mem_nhds (mem_extChartAt_source q)
  have he_pull : e_q ⁻¹' U ∈ nhds q :=
    (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) q).preimage_mem_nhds (hU_open.mem_nhds hz₀_U)
  refine ⟨e_q.source ∩ e_q ⁻¹' U, Filter.inter_mem he_src he_pull, δ / 4,
    by linarith, ?_⟩
  intro r ⟨hr_src, hr_U⟩ c hc
  obtain ⟨hG_ana_w, hG_bound_w, hG_agree_w⟩ := hU_sub (e_q r) hr_U
  -- G(e_q r) ≠ c: |G(e_q r) - c₀| > δ/2 and |c - c₀| < δ/4
  have hG_ne_c : G (e_q r) ≠ c := fun h => by
    have : ‖G (e_q r) - c₀‖ ≤ ‖c - c₀‖ := by rw [h]
    linarith
  rw [chartOrderAt_eq_in_chart (fun x => f x - c) q r
      (chartMeromorphic_sub_const c hf) hr_src, chartRep_sub_const]
  have h_congr : (fun z => chartRep (RS := RS) f q z - c)
      =ᶠ[nhdsWithin (e_q r) {e_q r}ᶜ] (fun z => G z - c) := by
    by_cases hrq : r = q
    · subst hrq
      filter_upwards [hG_agree] with z hz; rw [hz]
    · have hne_z₀ : e_q r ≠ z₀ := by
        intro h; exact hrq (e_q.injOn hr_src (mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) q) h)
      have h_agree_nhd : ∀ᶠ w in nhds (e_q r),
          chartRep (RS := RS) f q w = G w :=
        Filter.eventually_of_mem
          ((hU_open.inter (isClosed_singleton (x := z₀)).isOpen_compl).mem_nhds
            ⟨hr_U, show e_q r ∈ ({z₀} : Set ℂ)ᶜ from fun h => hne_z₀ h⟩)
          (fun w ⟨hw_U, hw_ne⟩ => (hU_sub w hw_U).2.2
            (show w ≠ z₀ from fun h => hw_ne (Set.mem_singleton_iff.mpr h)))
      filter_upwards [h_agree_nhd.filter_mono nhdsWithin_le_nhds] with z hz; rw [hz]
  rw [meromorphicOrderAt_congr h_congr]
  exact meromorphicOrderAt_analytic_sub_const_eq_zero' hG_ana_w hG_ne_c

/-- On a compact set K with no poles and all orders of f-c₀ equal to 0,
    for c near c₀, chartOrderAt(f-c, q) = 0 for all q ∈ K. -/
theorem no_support_on_compact_near_c₀ (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hne_top : ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) f q ≠ ⊤)
    (c₀ : ℂ)
    (K : Set CRS.toRiemannSurface.carrier)
    (hK : @IsCompact CRS.toRiemannSurface.carrier CRS.toRiemannSurface.topology K)
    (hK_no_pole : ∀ q ∈ K,
      (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f q)
    (hK_no_support : ∀ q ∈ K,
      chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c₀) q = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ c : ℂ, ‖c - c₀‖ < ε → ∀ q ∈ K,
      chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) q = 0 := by
  letI := CRS.toRiemannSurface.topology
  letI := CRS.toRiemannSurface.chartedSpace
  haveI := CRS.toRiemannSurface.isManifold
  haveI := CRS.toRiemannSurface.t2
  haveI : CompactSpace CRS.toRiemannSurface.carrier := CRS.compact
  have h_local_data : ∀ q, ∃ V ∈ nhds q, ∃ εb : ℝ, 0 < εb ∧
      (q ∈ K → ∀ r ∈ V, ∀ c : ℂ, ‖c - c₀‖ < εb →
        chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) r = 0) := by
    intro q
    by_cases hq : q ∈ K
    · obtain ⟨V, hV, εb, hεb_pos, hεb_bound⟩ :=
        chartOrderAt_sub_const_eq_zero_near_c₀ hf (hne_top q) (hK_no_pole q hq)
          (hK_no_support q hq)
      exact ⟨V, hV, εb, hεb_pos, fun _ => hεb_bound⟩
    · exact ⟨Set.univ, Filter.univ_mem, 1, one_pos, fun h => absurd h hq⟩
  choose V hV_nhds εb hεb_pos hεb_prop using h_local_data
  obtain ⟨t, ht_sub, ht_cover⟩ := hK.elim_nhds_subcover V (fun q _ => hV_nhds q)
  by_cases hK_emp : K = ∅
  · subst hK_emp; exact ⟨1, one_pos, fun _ _ _ hq => absurd hq (Set.mem_empty_iff_false _).mp⟩
  have hK_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_emp
  have ht_ne : t.Nonempty := by
    by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h
    obtain ⟨q, hq⟩ := hK_ne; have := ht_cover hq; rw [h] at this; simp at this
  set ε := t.inf' ht_ne εb
  have hε_pos : 0 < ε :=
    Finset.inf'_induction ht_ne εb (fun _ h₁ _ h₂ => lt_min h₁ h₂) (fun j _ => hεb_pos j)
  refine ⟨ε, hε_pos, ?_⟩
  intro c hc q hq
  obtain ⟨i, hi_t, hq_Vi⟩ := Set.mem_iUnion₂.mp (ht_cover hq)
  have hc_bound : ‖c - c₀‖ < εb i :=
    lt_of_lt_of_le hc (Finset.inf'_le εb hi_t)
  exact hεb_prop i (ht_sub i hi_t) q hq_Vi c hc_bound

/-- At a pole of f, the local sum of orders of (chartRep f q - c) in a chart ball
    is constant (= pole order) for all c near c₀.
    Near a pole, |chartRep f q(z)| → ∞, so chartRep f q(z) ≠ c for c bounded
    and z near the pole. The finset S = {z₀} captures the pole contribution only. -/
private theorem pole_local_chart_sum_constant
    {f : RS.carrier → ℂ} {q : RS.carrier} (c₀ : ℂ) {ρ : ℝ}
    (hf : IsChartMeromorphic (RS := RS) f)
    (hpole : chartOrderAt (RS := RS) f q < 0)
    (hρ : 0 < ρ) :
    ∃ r > 0, r ≤ ρ ∧ ∃ ε > 0, ∀ c : ℂ, ‖c - c₀‖ < ε →
      ∃ S : Finset ℂ,
        (∀ z ∈ S, ‖z - chartPt (RS := RS) q‖ < r) ∧
        (∀ z, ‖z - chartPt (RS := RS) q‖ < r →
          meromorphicOrderAt (fun w => chartRep (RS := RS) f q w - c) z ≠ 0 →
          meromorphicOrderAt (fun w => chartRep (RS := RS) f q w - c) z ≠ ⊤ →
          z ∈ S) ∧
        S.sum (fun z => (meromorphicOrderAt
          (fun w => chartRep (RS := RS) f q w - c) z).getD 0) =
          (chartOrderAt (RS := RS) (fun x => f x - c₀) q).getD 0 := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  set g := chartRep (RS := RS) f q
  set z₀ := chartPt (RS := RS) q
  -- Step 1: Extract pole order n ≥ 1 and construct H = analytic extension of g⁻¹
  have hpole_z : meromorphicOrderAt g z₀ < 0 := hpole
  have hne_top_z : meromorphicOrderAt g z₀ ≠ ⊤ := by
    intro h; rw [h] at hpole_z; exact absurd le_top (not_le.mpr hpole_z)
  set m : ℤ := (meromorphicOrderAt g z₀).untop₀ with hm_def
  have hm_coe : meromorphicOrderAt g z₀ = (m : WithTop ℤ) :=
    (WithTop.coe_untop₀_of_ne_top hne_top_z).symm
  have hm_neg : m < 0 := by
    have hpole_z' : ((m : WithTop ℤ) < (0 : WithTop ℤ)) := by
      simpa [hm_coe] using hpole_z
    exact WithTop.coe_lt_coe.mp hpole_z'
  set n := (-m).toNat with hn_def
  have hn_eq : (n : ℤ) = -m := Int.toNat_of_nonneg (le_of_lt (neg_pos.mpr hm_neg))
  have hn_pos : 1 ≤ n := by omega
  have hm_eq : meromorphicOrderAt g z₀ = (-(n : ℤ) : WithTop ℤ) := by
    rw [hm_coe]; congr 1; linarith [hn_eq]
  have hg_inv : MeromorphicAt g⁻¹ z₀ := (hf q).inv
  have hg_inv_ord : meromorphicOrderAt g⁻¹ z₀ = (n : ℤ) := by
    rw [meromorphicOrderAt_inv, hm_eq]; simp
  have hg_inv_nonneg : (0 : WithTop ℤ) ≤ meromorphicOrderAt g⁻¹ z₀ := by
    rw [hg_inv_ord]
    exact WithTop.coe_le_coe.mpr (Int.natCast_nonneg n)
  have hg_inv_ne_top : meromorphicOrderAt g⁻¹ z₀ ≠ ⊤ := by
    rw [hg_inv_ord]; exact WithTop.coe_ne_top
  obtain ⟨H, hH_ana, hH_agree, hH_mord⟩ :=
    exists_analyticExtension_of_nonneg_order hg_inv hg_inv_ne_top hg_inv_nonneg
  -- Step 2: Get analytic order of H
  have hH_mord_eq : meromorphicOrderAt H z₀ = (n : ℤ) := by rw [hH_mord, hg_inv_ord]
  have hH_aord : analyticOrderAt H z₀ = n := by
    have h := hH_ana.meromorphicOrderAt_eq
    rw [hH_mord_eq] at h
    cases hn : analyticOrderAt H z₀ with
    | top => simp [hn] at h
    | coe k => simp [hn] at h; exact_mod_cast h.symm
  have hH0 : H z₀ = 0 := by
    rw [← hH_ana.analyticOrderAt_ne_zero]
    rw [hH_aord]; exact_mod_cast Nat.one_le_iff_ne_zero.mp hn_pos
  -- Step 3: Extract key balls
  -- (a) Isolated zero of H: H(z) ≠ 0 for z ≠ z₀ near z₀
  have hH_aord_ne_top : analyticOrderAt H z₀ ≠ ⊤ := by
    rw [hH_aord]; exact WithTop.coe_ne_top
  have h_iso_evt : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, H z ≠ 0 := by
    rcases hH_ana.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (analyticOrderAt_eq_top.mpr h) hH_aord_ne_top
    · exact h
  obtain ⟨r_iso, hr_iso, h_iso⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp h_iso_evt)
  -- (b) Analyticity ball: H analytic at all points near z₀
  obtain ⟨r_ana, hr_ana, hH_ana_ball⟩ :=
    Metric.eventually_nhds_iff.mp hH_ana.eventually_analyticAt
  -- (c) Agreement ball: g⁻¹ = H near z₀ (punctured)
  obtain ⟨r_agr, hr_agr, h_agree_ball⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp hH_agree)
  -- (d) Continuity ball: ‖H(z)‖ < δ where δ = (‖c₀‖ + 2)⁻¹
  set δ := (‖c₀‖ + 2)⁻¹ with hδ_def
  have hc₀_bound_pos : (0 : ℝ) < ‖c₀‖ + 2 := by linarith [norm_nonneg c₀]
  have hδ_pos : 0 < δ := inv_pos.mpr hc₀_bound_pos
  have hH_cont_evt : ∀ᶠ z in nhds z₀, ‖H z‖ < δ := by
    have h_tend : Tendsto H (nhds z₀) (nhds (0 : ℂ)) := by
      rw [← hH0]
      exact hH_ana.continuousAt
    have h_norm : Tendsto (fun z => ‖H z‖) (nhds z₀) (nhds ‖(0 : ℂ)‖) := h_tend.norm
    have h_neigh : nhds ‖(0 : ℂ)‖ = nhds (0 : ℝ) := by simp
    have h_norm0 : Tendsto (fun z => ‖H z‖) (nhds z₀) (nhds (0 : ℝ)) := by
      simpa [h_neigh] using h_norm
    exact h_norm0.eventually (Iio_mem_nhds hδ_pos)
  obtain ⟨r_cont, hr_cont, h_cont⟩ := Metric.eventually_nhds_iff.mp hH_cont_evt
  -- Step 3: Combine into r ≤ ρ
  set r := min (min (min r_iso r_ana) (min r_agr r_cont)) ρ with hr_def
  have hr : 0 < r := lt_min (lt_min (lt_min hr_iso hr_ana) (lt_min hr_agr hr_cont)) hρ
  have hr_le : r ≤ ρ := min_le_right _ _
  -- Convenience: ball property extraction
  have h_in_iso (z : ℂ) (hz : ‖z - z₀‖ < r) : dist z z₀ < r_iso :=
    lt_of_lt_of_le (by rwa [dist_eq_norm]) (le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (min_le_left _ _)))
  have h_in_ana (z : ℂ) (hz : ‖z - z₀‖ < r) : dist z z₀ < r_ana :=
    lt_of_lt_of_le (by rwa [dist_eq_norm]) (le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (min_le_right _ _)))
  have h_in_agr (z : ℂ) (hz : ‖z - z₀‖ < r) : dist z z₀ < r_agr :=
    lt_of_lt_of_le (by rwa [dist_eq_norm]) (le_trans (min_le_left _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have h_in_cont (z : ℂ) (hz : ‖z - z₀‖ < r) : dist z z₀ < r_cont :=
    lt_of_lt_of_le (by rwa [dist_eq_norm]) (le_trans (min_le_left _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _)))
  -- Step 4: Prove the result with S = {z₀}, ε = 1
  refine ⟨r, hr, hr_le, 1, one_pos, ?_⟩
  intro c hc
  refine ⟨{z₀}, ?_, ?_, ?_⟩
  · -- S ⊆ B(z₀, r)
    intro z hz; simp only [Finset.mem_singleton] at hz; subst hz; simp [hr]
  · -- Capture: all support in ball is in S = {z₀}
    intro z hz hord_ne0 hord_ne_top
    simp only [Finset.mem_singleton]
    by_contra hne
    -- z ≠ z₀ and z ∈ B(z₀, r)
    have hHz_ne : H z ≠ 0 :=
      h_iso (h_in_iso z hz) (Set.mem_compl_singleton_iff.mpr hne)
    have hHz_small : ‖H z‖ < δ := h_cont (h_in_cont z hz)
    -- g =ᶠ H⁻¹ near z (since z ≠ z₀ and agreement holds on punctured nhds)
    have hgz : g z = (H z)⁻¹ := by
      have h_agr := h_agree_ball (h_in_agr z hz) (Set.mem_compl_singleton_iff.mpr hne)
      calc g z = ((g z)⁻¹)⁻¹ := (inv_inv (g z)).symm
        _ = (g⁻¹ z)⁻¹ := rfl
        _ = (H z)⁻¹ := by rw [h_agr]
    -- |g(z)| = |H(z)|⁻¹ > 1/δ = ‖c₀‖ + 2
    have hgz_large : ‖c₀‖ + 2 ≤ ‖g z‖ := by
      rw [hgz, norm_inv]
      rw [le_inv_comm₀ (by linarith [norm_nonneg c₀] : (0 : ℝ) < ‖c₀‖ + 2)
        (norm_pos_iff.mpr hHz_ne)]
      exact le_of_lt hHz_small
    -- ‖c‖ < ‖g z‖
    have hgz_ne_c : g z ≠ c := by
      intro h; rw [h] at hgz_large
      have : ‖c‖ ≤ ‖c₀‖ + ‖c - c₀‖ := norm_le_norm_add_norm_sub' c c₀
      linarith
    -- g is analytic at z (H analytic, H(z) ≠ 0 → H⁻¹ analytic)
    have hH_ana_z : AnalyticAt ℂ H z := hH_ana_ball (h_in_ana z hz)
    have hg_eq_near : g =ᶠ[nhds z] fun w => (H w)⁻¹ := by
      set d := min (r_agr - dist z z₀) (dist z z₀ / 2)
      have hd_pos : 0 < d :=
        lt_min (by linarith [h_in_agr z hz]) (half_pos (dist_pos.mpr hne))
      exact Filter.eventually_of_mem (Metric.ball_mem_nhds z hd_pos) fun w hw => by
        have hw_dist : dist w z < d := Metric.mem_ball.mp hw
        have hw_agr : dist w z₀ < r_agr := by
          linarith [dist_triangle w z z₀, min_le_left (r_agr - dist z z₀) (dist z z₀ / 2)]
        have hw_ne : w ≠ z₀ := by
          intro heq; rw [heq] at hw_dist
          linarith [min_le_right (r_agr - dist z z₀) (dist z z₀ / 2), dist_comm z z₀,
            (dist_nonneg : 0 ≤ dist z₀ z)]
        calc g w = ((g w)⁻¹)⁻¹ := (inv_inv _).symm
          _ = (g⁻¹ w)⁻¹ := rfl
          _ = (H w)⁻¹ := by rw [h_agree_ball hw_agr (Set.mem_compl_singleton_iff.mpr hw_ne)]
    -- meromorphicOrderAt(g - c, z) = meromorphicOrderAt(H⁻¹ - c, z) = 0
    have h_congr : (fun w => g w - c) =ᶠ[nhdsWithin z {z}ᶜ] (fun w => (H w)⁻¹ - c) :=
      (hg_eq_near.filter_mono nhdsWithin_le_nhds).mono fun w hw => by
        show g w - c = (H w)⁻¹ - c; rw [hw]
    rw [meromorphicOrderAt_congr h_congr] at hord_ne0
    exact hord_ne0 (meromorphicOrderAt_analytic_sub_const_eq_zero'
      (hH_ana_z.inv hHz_ne) (show (H z)⁻¹ ≠ c by rwa [← hgz]))
  · -- Sum: S.sum = chartOrderAt(f - c₀, q).getD 0
    simp only [Finset.sum_singleton]
    -- meromorphicOrderAt(g - c, z₀) = meromorphicOrderAt(g, z₀) by pole invariance
    rw [meromorphicOrderAt_sub_const_at_pole_loc c hpole_z]
    -- chartOrderAt(f - c₀, q) = chartOrderAt(f, q) by pole invariance
    rw [show chartOrderAt (RS := RS) (fun x => f x - c₀) q =
      chartOrderAt (RS := RS) f q from chartOrderAt_sub_const_at_pole c₀ hpole]
    -- meromorphicOrderAt g z₀ = chartOrderAt f q definitionally
    rfl

/-- At a non-pole point q where f-c₀ has a zero of positive finite order k,
    the local sum of orders of (chartRep f q - c) in a chart ball is constant (= k)
    for all c near c₀, by the Local Mapping Theorem.

    For c ≠ c₀ with |c-c₀| small: LMT gives exactly k simple preimages of G = c
    near z₀, each contributing order 1, summing to k.
    For c = c₀: the isolated zero z₀ has order k, summing to k. -/
private theorem zero_local_chart_sum_constant
    {f : RS.carrier → ℂ} {q : RS.carrier} (c₀ : ℂ) {ρ : ℝ}
    (hf : IsChartMeromorphic (RS := RS) f)
    (hne_top : chartOrderAt (RS := RS) f q ≠ ⊤)
    (hord_nonneg : (0 : WithTop ℤ) ≤ chartOrderAt (RS := RS) f q)
    (hzero : (0 : WithTop ℤ) < chartOrderAt (RS := RS) (fun x => f x - c₀) q)
    (hzero_ne_top : chartOrderAt (RS := RS) (fun x => f x - c₀) q ≠ ⊤)
    (hρ : 0 < ρ) :
    ∃ r > 0, r ≤ ρ ∧ ∃ ε > 0, ∀ c : ℂ, ‖c - c₀‖ < ε →
      ∃ S : Finset ℂ,
        (∀ z ∈ S, ‖z - chartPt (RS := RS) q‖ < r) ∧
        (∀ z, ‖z - chartPt (RS := RS) q‖ < r →
          meromorphicOrderAt (fun w => chartRep (RS := RS) f q w - c) z ≠ 0 →
          meromorphicOrderAt (fun w => chartRep (RS := RS) f q w - c) z ≠ ⊤ →
          z ∈ S) ∧
        S.sum (fun z => (meromorphicOrderAt
          (fun w => chartRep (RS := RS) f q w - c) z).getD 0) =
          (chartOrderAt (RS := RS) (fun x => f x - c₀) q).getD 0 := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  set g := chartRep (RS := RS) f q
  set z₀ := chartPt (RS := RS) q
  have hzero_mord_pos : (0 : WithTop ℤ) < meromorphicOrderAt (fun w => g w - c₀) z₀ := by
    simpa [g, z₀, chartOrderAt, chartRep_sub_const] using hzero
  have hzero_mord_ne_top : meromorphicOrderAt (fun w => g w - c₀) z₀ ≠ ⊤ := by
    simpa [g, z₀, chartOrderAt, chartRep_sub_const] using hzero_ne_top
  set m : ℤ := (meromorphicOrderAt (fun w => g w - c₀) z₀).untop₀ with hm_def
  have hm_coe : meromorphicOrderAt (fun w => g w - c₀) z₀ = (m : WithTop ℤ) :=
    (WithTop.coe_untop₀_of_ne_top hzero_mord_ne_top).symm
  have hm_pos : 0 < m := by
    have hpos' : (0 : WithTop ℤ) < (m : WithTop ℤ) := by
      simpa [hm_coe] using hzero_mord_pos
    exact WithTop.coe_lt_coe.mp hpos'
  set k : ℕ := m.toNat with hk_def
  have hk_eq : (k : ℤ) = m := Int.toNat_of_nonneg (le_of_lt hm_pos)
  have hk_pos : 1 ≤ k := by omega
  have hzero_mord_eq : meromorphicOrderAt (fun w => g w - c₀) z₀ = (k : ℤ) := by
    rw [hm_coe, ← hk_eq]
  obtain ⟨G, hG_ana, hG_agree, _⟩ :=
    exists_analyticExtension_of_nonneg_order (hf q) hne_top hord_nonneg
  have h_congr : (fun w => g w - c₀) =ᶠ[nhdsWithin z₀ {z₀}ᶜ] (fun w => G w - c₀) := by
    filter_upwards [hG_agree] with w hw
    simpa [g] using congrArg (fun t => t - c₀) hw
  have hG_sub_mord : meromorphicOrderAt (fun w => G w - c₀) z₀ = (k : ℤ) := by
    have htmp := hzero_mord_eq
    rw [meromorphicOrderAt_congr h_congr] at htmp
    exact htmp
  have hG_sub_ana : AnalyticAt ℂ (fun w => G w - c₀) z₀ := hG_ana.sub analyticAt_const
  have hG_sub_aord : analyticOrderAt (fun w => G w - c₀) z₀ = k := by
    have h := hG_sub_ana.meromorphicOrderAt_eq
    rw [hG_sub_mord] at h
    cases hk' : analyticOrderAt (fun w => G w - c₀) z₀ with
    | top => simp [hk'] at h
    | coe n => simp [hk'] at h; exact_mod_cast h.symm
  have hG_sub_zero : (fun w => G w - c₀) z₀ = 0 := by
    rw [← hG_sub_ana.analyticOrderAt_ne_zero]
    rw [hG_sub_aord]
    exact_mod_cast Nat.one_le_iff_ne_zero.mp hk_pos
  obtain ⟨r_ana, hr_ana_pos, hG_ana_ball⟩ :=
    Metric.eventually_nhds_iff.mp hG_ana.eventually_analyticAt
  obtain ⟨r_agr, hr_agr_pos, h_agree_ball⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp hG_agree)
  obtain ⟨r, hr_pos, hr_le_bound, ε, hε_pos, h_iso, h_count, h_deriv_ne⟩ :=
    local_mapping_theorem (h := fun w => G w - c₀) (z₀ := z₀) (k := k)
      (r_bound := min ρ (min r_ana r_agr))
      hk_pos hG_sub_ana hG_sub_zero hG_sub_aord (lt_min hρ (lt_min hr_ana_pos hr_agr_pos))
  have hr_le_ρ : r ≤ ρ := le_trans hr_le_bound (min_le_left _ _)
  have hr_le_ana : r ≤ r_ana :=
    le_trans hr_le_bound (le_trans (min_le_right _ _) (min_le_left _ _))
  have hr_le_agr : r ≤ r_agr :=
    le_trans hr_le_bound (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨r, hr_pos, hr_le_ρ, ε, hε_pos, ?_⟩
  intro c hc
  by_cases hcc : c = c₀
  · subst c
    refine ⟨{z₀}, ?_, ?_, ?_⟩
    · intro z hz
      simp only [Finset.mem_singleton] at hz
      subst hz
      simpa using hr_pos
    · intro z hz hord_ne0 hord_ne_top
      simp only [Finset.mem_singleton]
      by_contra hne
      have hG_sub_ne : (G z - c₀) ≠ 0 := h_iso z hz hne
      have hG_sub_ana_z : AnalyticAt ℂ (fun w => G w - c₀) z :=
        (hG_ana_ball (lt_of_lt_of_le (by rwa [dist_eq_norm]) hr_le_ana)).sub analyticAt_const
      have h_eq_near : (fun w => chartRep (RS := RS) f q w - c₀)
          =ᶠ[nhds z] (fun w => G w - c₀) := by
        set d : ℝ := min (r_agr - dist z z₀) (dist z z₀ / 2) with hd_def
        have hd_pos : 0 < d := by
          have hz_agr : dist z z₀ < r_agr := lt_of_lt_of_le (by rwa [dist_eq_norm]) hr_le_agr
          have hz_pos : 0 < dist z z₀ := dist_pos.mpr hne
          have h1 : 0 < r_agr - dist z z₀ := by linarith
          have h2 : 0 < dist z z₀ / 2 := by positivity
          simpa [hd_def] using lt_min h1 h2
        exact Filter.eventually_of_mem (Metric.ball_mem_nhds z hd_pos) (fun w hw => by
          have hw_dist : dist w z < d := Metric.mem_ball.mp hw
          have hw_agr : dist w z₀ < r_agr := by
            have hlt : dist w z < r_agr - dist z z₀ := lt_of_lt_of_le hw_dist (min_le_left _ _)
            linarith [dist_triangle w z z₀]
          have hw_ne : w ≠ z₀ := by
            intro hw0
            subst hw0
            have : dist z z₀ < dist z z₀ / 2 := by
              have hw_dist' : dist z z₀ < d := by simpa [dist_comm] using hw_dist
              exact lt_of_lt_of_le hw_dist' (min_le_right _ _)
            have hnonneg : 0 ≤ dist z z₀ := dist_nonneg
            linarith
          have hw_eq : chartRep (RS := RS) f q w = G w :=
            h_agree_ball hw_agr (Set.mem_compl_singleton_iff.mpr hw_ne)
          simpa using congrArg (fun t => t - c₀) hw_eq)
      have h_congr : (fun w => chartRep (RS := RS) f q w - c₀)
          =ᶠ[nhdsWithin z {z}ᶜ] (fun w => G w - c₀) :=
        h_eq_near.filter_mono nhdsWithin_le_nhds
      have h_ord0 : meromorphicOrderAt (fun w => G w - c₀) z = 0 := by
        exact (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hG_sub_ana_z.meromorphicAt).mp
          ⟨G z - c₀, hG_sub_ne, hG_sub_ana_z.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩
      rw [meromorphicOrderAt_congr h_congr] at hord_ne0
      exact (hord_ne0 h_ord0).elim
    · -- At c = c₀, the singleton sum is exactly chartOrderAt(f-c₀,q).getD 0
      simp [chartOrderAt, chartRep_sub_const, g, z₀]
  · set v : ℂ := c - c₀ with hv_def
    have hv_ne : v ≠ 0 := by simpa [hv_def, sub_eq_zero] using hcc
    have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
    have hv_norm_lt : ‖v‖ < ε := by simpa [hv_def] using hc
    have h_count_v :
        {z : ℂ | ‖z - z₀‖ < r ∧ (G z - c₀) = v}.ncard = k :=
      h_count v hv_norm_pos hv_norm_lt
    set T : Set ℂ := {z : ℂ | ‖z - z₀‖ < r ∧ (G z - c₀) = v} with hT_def
    have hT_ncard : T.ncard = k := by simpa [T, hT_def] using h_count_v
    have hk_pos' : 0 < k := Nat.succ_le_iff.mp hk_pos
    have hT_finite : T.Finite := Set.finite_of_ncard_pos (by simpa [hT_ncard] using hk_pos')
    refine ⟨hT_finite.toFinset, ?_, ?_, ?_⟩
    · intro z hz
      exact (hT_finite.mem_toFinset.mp hz).1
    · intro z hz hord_ne0 _hord_ne_top
      have hz_ne : z ≠ z₀ := by
        intro hz0
        subst hz0
        have hGz0_eq : G z₀ = c₀ := sub_eq_zero.mp hG_sub_zero
        have hGz0_ne_c : G z₀ ≠ c := by
          intro hEq
          exact hcc (calc
            c = G z₀ := hEq.symm
            _ = c₀ := hGz0_eq)
        have h_congr0 : (fun w => g w - c) =ᶠ[nhdsWithin z₀ {z₀}ᶜ] (fun w => G w - c) := by
          filter_upwards [hG_agree] with w hw
          simpa [g] using congrArg (fun t => t - c) hw
        have h_ord0 : meromorphicOrderAt (fun w => g w - c) z₀ = 0 := by
          rw [meromorphicOrderAt_congr h_congr0]
          exact meromorphicOrderAt_analytic_sub_const_eq_zero' hG_ana hGz0_ne_c
        exact (hord_ne0 h_ord0).elim
      have h_congrz : (fun w => g w - c) =ᶠ[nhdsWithin z {z}ᶜ] (fun w => G w - c) := by
        have h_eq_nhds : (fun w => g w - c) =ᶠ[nhds z] (fun w => G w - c) := by
          set d : ℝ := min (r_agr - dist z z₀) (dist z z₀ / 2) with hd_def
          have hd_pos : 0 < d := by
            have hz_agr : dist z z₀ < r_agr := lt_of_lt_of_le (by rwa [dist_eq_norm]) hr_le_agr
            have hz_pos : 0 < dist z z₀ := dist_pos.mpr hz_ne
            have h1 : 0 < r_agr - dist z z₀ := by linarith
            have h2 : 0 < dist z z₀ / 2 := by positivity
            simpa [hd_def] using lt_min h1 h2
          exact Filter.eventually_of_mem (Metric.ball_mem_nhds z hd_pos) (fun w hw => by
            have hw_dist : dist w z < d := Metric.mem_ball.mp hw
            have hw_agr : dist w z₀ < r_agr := by
              have hlt : dist w z < r_agr - dist z z₀ := lt_of_lt_of_le hw_dist (min_le_left _ _)
              linarith [dist_triangle w z z₀]
            have hw_ne : w ≠ z₀ := by
              intro hw0
              subst hw0
              have : dist z z₀ < dist z z₀ / 2 := by
                have hw_dist' : dist z z₀ < d := by simpa [dist_comm] using hw_dist
                exact lt_of_lt_of_le hw_dist' (min_le_right _ _)
              have hnonneg : 0 ≤ dist z z₀ := dist_nonneg
              linarith
            have hw_eq : chartRep (RS := RS) f q w = G w :=
              h_agree_ball hw_agr (Set.mem_compl_singleton_iff.mpr hw_ne)
            simpa [g] using congrArg (fun t => t - c) hw_eq)
        exact h_eq_nhds.filter_mono nhdsWithin_le_nhds
      by_contra hnot
      have hG_ne_c : G z ≠ c := by
        intro hEq
        apply hnot
        have hzT : z ∈ T := by
          refine ⟨hz, ?_⟩
          have h_sub : G z - c₀ = c - c₀ := by simpa [hEq]
          simpa [hv_def] using h_sub
        exact hT_finite.mem_toFinset.mpr hzT
      have hG_ana_z : AnalyticAt ℂ G z :=
        hG_ana_ball (lt_of_lt_of_le (by rwa [dist_eq_norm]) hr_le_ana)
      have h_ord0G : meromorphicOrderAt (fun w => G w - c) z = 0 :=
        meromorphicOrderAt_analytic_sub_const_eq_zero' hG_ana_z hG_ne_c
      have h_ord0 : meromorphicOrderAt (fun w => g w - c) z = 0 := by
        rw [meromorphicOrderAt_congr h_congrz]
        exact h_ord0G
      exact (hord_ne0 h_ord0).elim
    · -- For c ≠ c₀, each point in T is a simple zero of (g - c); summing gives k.
      have h_each_one : ∀ z ∈ hT_finite.toFinset,
          (meromorphicOrderAt (fun w => g w - c) z).getD 0 = 1 := by
        intro z hz_fin
        have hzT : z ∈ T := hT_finite.mem_toFinset.mp hz_fin
        have hz_ball : ‖z - z₀‖ < r := hzT.1
        have hz_eq_v : G z - c₀ = v := hzT.2
        have hz_ne : z ≠ z₀ := by
          intro hz0
          have hv0 : v = 0 := by
            subst hz0
            calc
              v = G z₀ - c₀ := by simpa using hz_eq_v.symm
              _ = 0 := hG_sub_zero
          exact hv_ne hv0
        have hG_ana_z : AnalyticAt ℂ G z :=
          hG_ana_ball (lt_of_lt_of_le (by rwa [dist_eq_norm]) hr_le_ana)
        have hderiv_sub : deriv (fun w => G w - c) z ≠ 0 := by
          simpa using (h_deriv_ne z hz_ball hz_ne)
        have hzero_z : (fun w => G w - c) z = 0 := by
          have h_sub : G z - c₀ = c - c₀ := by simpa [hv_def] using hz_eq_v
          have h_add := congrArg (fun t : ℂ => t + c₀) h_sub
          have hGc : G z = c := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h_add
          simpa [hGc]
        have h_ord_G : meromorphicOrderAt (fun w => G w - c) z = 1 :=
          meromorphicOrderAt_eq_one_of_simple_zero (hG_ana_z.sub analyticAt_const) hzero_z hderiv_sub
        have h_congrz : (fun w => g w - c) =ᶠ[nhdsWithin z {z}ᶜ] (fun w => G w - c) := by
          have h_eq_nhds : (fun w => g w - c) =ᶠ[nhds z] (fun w => G w - c) := by
            set d : ℝ := min (r_agr - dist z z₀) (dist z z₀ / 2) with hd_def
            have hd_pos : 0 < d := by
              have hz_agr : dist z z₀ < r_agr := lt_of_lt_of_le (by rwa [dist_eq_norm]) hr_le_agr
              have hz_pos : 0 < dist z z₀ := dist_pos.mpr hz_ne
              have h1 : 0 < r_agr - dist z z₀ := by linarith
              have h2 : 0 < dist z z₀ / 2 := by positivity
              simpa [hd_def] using lt_min h1 h2
            exact Filter.eventually_of_mem (Metric.ball_mem_nhds z hd_pos) (fun w hw => by
              have hw_dist : dist w z < d := Metric.mem_ball.mp hw
              have hw_agr : dist w z₀ < r_agr := by
                have hlt : dist w z < r_agr - dist z z₀ := lt_of_lt_of_le hw_dist (min_le_left _ _)
                linarith [dist_triangle w z z₀]
              have hw_ne : w ≠ z₀ := by
                intro hw0
                subst hw0
                have : dist z z₀ < dist z z₀ / 2 := by
                  have hw_dist' : dist z z₀ < d := by simpa [dist_comm] using hw_dist
                  exact lt_of_lt_of_le hw_dist' (min_le_right _ _)
                have hnonneg : 0 ≤ dist z z₀ := dist_nonneg
                linarith
              have hw_eq : chartRep (RS := RS) f q w = G w :=
                h_agree_ball hw_agr (Set.mem_compl_singleton_iff.mpr hw_ne)
              simpa [g] using congrArg (fun t => t - c) hw_eq)
          exact h_eq_nhds.filter_mono nhdsWithin_le_nhds
        have h_ord_g : meromorphicOrderAt (fun w => g w - c) z = 1 := by
          rw [meromorphicOrderAt_congr h_congrz]
          exact h_ord_G
        exact congrArg (fun t : WithTop ℤ => t.getD 0) h_ord_g
      have hsum_T :
          hT_finite.toFinset.sum (fun z => (meromorphicOrderAt (fun w => g w - c) z).getD 0) = (k : ℤ) := by
        calc
          hT_finite.toFinset.sum (fun z => (meromorphicOrderAt (fun w => g w - c) z).getD 0)
              = hT_finite.toFinset.sum (fun _ => (1 : ℤ)) := by
                refine Finset.sum_congr rfl ?_
                intro z hz
                exact h_each_one z hz
          _ = (hT_finite.toFinset.card : ℤ) := by simp
          _ = (k : ℤ) := by
              have hcard : hT_finite.toFinset.card = k := by
                calc
                  hT_finite.toFinset.card = T.ncard := by
                    symm
                    exact Set.ncard_eq_toFinset_card T hT_finite
                  _ = k := hT_ncard
              exact_mod_cast hcard
      have h_rhs : (chartOrderAt (RS := RS) (fun x => f x - c₀) q).getD 0 = (k : ℤ) := by
        have hco : chartOrderAt (RS := RS) (fun x => f x - c₀) q = (k : WithTop ℤ) := by
          simpa [g, z₀, chartOrderAt, chartRep_sub_const] using hzero_mord_eq
        exact congrArg (fun t : WithTop ℤ => t.getD 0) hco
      have hsum_goal :
          hT_finite.toFinset.sum (fun z => (meromorphicOrderAt (fun w => g w - c) z).getD 0) =
            (chartOrderAt (RS := RS) (fun x => f x - c₀) q).getD 0 := by
        calc
          hT_finite.toFinset.sum (fun z => (meromorphicOrderAt (fun w => g w - c) z).getD 0)
              = (k : ℤ) := hsum_T
          _ = (chartOrderAt (RS := RS) (fun x => f x - c₀) q).getD 0 := by
              simpa using h_rhs.symm
      simpa [g] using hsum_goal

/-- Unified local constancy datum at a support point of `f - c₀`.

    If `q` is a pole of `f`, use `pole_local_chart_sum_constant`.
    Otherwise `f` is non-polar at `q`, and support membership of `f - c₀`
    forces a positive finite order, so `zero_local_chart_sum_constant` applies. -/
theorem support_local_chart_sum_constant
    {f : RS.carrier → ℂ} {q : RS.carrier} (c₀ : ℂ) {ρ : ℝ}
    (hf : IsChartMeromorphic (RS := RS) f)
    (hne_top : chartOrderAt (RS := RS) f q ≠ ⊤)
    (hord_ne_zero : chartOrderAt (RS := RS) (fun x => f x - c₀) q ≠ 0)
    (hord_ne_top : chartOrderAt (RS := RS) (fun x => f x - c₀) q ≠ ⊤)
    (hρ : 0 < ρ) :
    ∃ r > 0, r ≤ ρ ∧ ∃ ε > 0, ∀ c : ℂ, ‖c - c₀‖ < ε →
      ∃ S : Finset ℂ,
        (∀ z ∈ S, ‖z - chartPt (RS := RS) q‖ < r) ∧
        (∀ z, ‖z - chartPt (RS := RS) q‖ < r →
          meromorphicOrderAt (fun w => chartRep (RS := RS) f q w - c) z ≠ 0 →
          meromorphicOrderAt (fun w => chartRep (RS := RS) f q w - c) z ≠ ⊤ →
          z ∈ S) ∧
        S.sum (fun z => (meromorphicOrderAt
          (fun w => chartRep (RS := RS) f q w - c) z).getD 0) =
          (chartOrderAt (RS := RS) (fun x => f x - c₀) q).getD 0 := by
  by_cases hpole : chartOrderAt (RS := RS) f q < 0
  · exact pole_local_chart_sum_constant (RS := RS) c₀ hf hpole hρ
  · have hnonneg_f : (0 : WithTop ℤ) ≤ chartOrderAt (RS := RS) f q := le_of_not_gt hpole
    have hnonneg_sub : (0 : WithTop ℤ) ≤ chartOrderAt (RS := RS) (fun x => f x - c₀) q :=
      (chartOrderAt_sub_const_nonneg_iff (RS := RS) (f := f) (p := q) c₀).2 hnonneg_f
    have hpos_sub : (0 : WithTop ℤ) < chartOrderAt (RS := RS) (fun x => f x - c₀) q :=
      lt_of_le_of_ne hnonneg_sub (by simpa using hord_ne_zero.symm)
    exact zero_local_chart_sum_constant (RS := RS) c₀ hf hne_top hnonneg_f hpos_sub hord_ne_top hρ
