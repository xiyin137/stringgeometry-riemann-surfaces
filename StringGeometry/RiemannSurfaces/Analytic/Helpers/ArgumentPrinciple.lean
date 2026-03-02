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

/-- **Constancy of fiber multiplicity.**

On a compact RS, for a nonconstant chart-meromorphic function, the fiber
multiplicity N(c) is the same for all c ∈ ℂ. This is the degree of f
as a map to ℙ¹.

**Proof idea:**
1. N is locally constant: By the local mapping theorem, near each preimage
   of c₀, the contribution to N is constant for c near c₀. By compactness,
   no extra preimages appear.
2. N is defined on ℂ \ (finite branch set), which is connected.
3. A locally constant function on a connected set is constant.
4. N extends continuously to the branch values (by the LMT), so N is constant
   on all of ℂ. -/
theorem fiberMultiplicity_constant (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hsupp : (chartOrderSupport (RS := CRS.toRiemannSurface) f).Finite)
    (hne : ∃ p, f p ≠ 0)
    -- We need f to be "nonconstant on the regular locus"
    (hnc : ¬ ∀ p q, p ∈ regularLocus (RS := CRS.toRiemannSurface) f →
      q ∈ regularLocus (RS := CRS.toRiemannSurface) f → f p = f q) :
    -- For any c₁, c₂ with finite fibers, N(c₁) = N(c₂)
    ∀ (c₁ c₂ : ℂ)
      (hfib₁ : {p : CRS.toRiemannSurface.carrier |
        f p = c₁ ∧ (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p}.Finite)
      (hfib₂ : {p : CRS.toRiemannSurface.carrier |
        f p = c₂ ∧ (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p}.Finite),
      fiberMultiplicity CRS f c₁ hfib₁ = fiberMultiplicity CRS f c₂ hfib₂ := by
  sorry

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
  sorry
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
  sorry

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
  sorry

/-- chartOrderSum(f - c) is locally constant as a function of c ∈ ℂ.

    This is the hardest part of the degree theory proof. The proof uses:
    - LMT (local_mapping_theorem, proven) at zeros
    - Pole invariance (chartOrderAt_sub_const_at_pole, proven) at poles
    - Compactness (CompactSpace) for uniform bounds
    - T2 separation for pairwise disjoint neighborhoods -/
theorem chartOrderSum_locally_constant (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hne_top : ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) f q ≠ ⊤) :
    IsLocallyConstant (fun c : ℂ =>
      chartOrderSum CRS (fun x => f x - c)
        (chartMeromorphic_sub_const c hf)
        (chartOrderSupport_sub_const_finite CRS f c hf)) := by
  sorry
/-- If G is analytic at w and G(w) ≠ c, then meromorphicOrderAt(G - c, w) = 0. -/
private theorem meromorphicOrderAt_analytic_sub_const_eq_zero {G : ℂ → ℂ} {w c : ℂ}
    (hG : AnalyticAt ℂ G w) (hne : G w ≠ c) :
    meromorphicOrderAt (fun z => G z - c) w = 0 := by
  have h_ana : AnalyticAt ℂ (fun z => G z - c) w := hG.sub analyticAt_const
  have h_ne : G w - c ≠ 0 := sub_ne_zero.mpr hne
  exact (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero h_ana.meromorphicAt).mp
    ⟨G w - c, h_ne, h_ana.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩

/-- At a non-pole point, there exists a chart neighborhood where chartOrderAt(f-c, r) = 0
    for all r in the neighborhood, when |c| exceeds a bound.

    The proof uses the analytic extension of chartRep f q in q's chart. For r near q,
    chartOrderAt_eq_in_chart computes the order in q's chart, and the analytic extension
    G_q is bounded on a neighborhood, so G_q(w) ≠ c for large |c|. -/
private theorem chartOrderAt_sub_const_eq_zero_near_nonneg
    {f : RS.carrier → ℂ} {q : RS.carrier}
    (hf : IsChartMeromorphic (RS := RS) f)
    (hne_top : chartOrderAt (RS := RS) f q ≠ ⊤)
    (hord : (0 : WithTop ℤ) ≤ chartOrderAt (RS := RS) f q) :
    ∃ V ∈ @nhds _ RS.topology q, ∃ M : ℝ, 0 < M ∧
      ∀ r ∈ V, ∀ c : ℂ, M < ‖c‖ →
        chartOrderAt (RS := RS) (fun x => f x - c) r = 0 := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  -- Get analytic extension G of chartRep f q at z₀ = chartPt q
  obtain ⟨G, hG_ana, hG_agree, _⟩ :=
    exists_analyticExtension_of_nonneg_order (hf q) hne_top hord
  set z₀ := chartPt (RS := RS) q
  set e_q := extChartAt 𝓘(ℂ, ℂ) q
  set M := ‖G z₀‖ + 1 with hM_def
  -- Build filter: G analytic, bounded, agrees with chartRep f q
  have h_evt : ∀ᶠ w in nhds z₀,
      AnalyticAt ℂ G w ∧ ‖G w‖ < M ∧ (w ≠ z₀ → chartRep (RS := RS) f q w = G w) := by
    refine (hG_ana.eventually_analyticAt).and ((?_ : ∀ᶠ w in nhds z₀, ‖G w‖ < M).and ?_)
    · exact hG_ana.continuousAt.norm.preimage_mem_nhds
        (Iio_mem_nhds (by linarith : ‖G z₀‖ < M))
    · exact (eventually_nhdsWithin_iff.mp hG_agree).mono fun w hw hne => hw hne
  -- Extract open set in ℂ
  obtain ⟨U, hU_sub, hU_open, hz₀_U⟩ := eventually_nhds_iff.mp h_evt
  -- Pull back to manifold
  have he_src : e_q.source ∈ nhds q :=
    (isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) q).mem_nhds (mem_extChartAt_source q)
  have he_pull : e_q ⁻¹' U ∈ nhds q :=
    (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) q).preimage_mem_nhds (hU_open.mem_nhds hz₀_U)
  refine ⟨e_q.source ∩ e_q ⁻¹' U, Filter.inter_mem he_src he_pull, M,
    by positivity, ?_⟩
  intro r ⟨hr_src, hr_U⟩ c hc
  obtain ⟨hG_ana_w, hG_bound_w, hG_agree_w⟩ := hU_sub (e_q r) hr_U
  -- G(e_q r) ≠ c (since ‖G(e_q r)‖ < M < ‖c‖)
  have hG_ne_c : G (e_q r) ≠ c := fun h => by rw [h] at hG_bound_w; linarith
  -- Express chartOrderAt in q's chart
  rw [chartOrderAt_eq_in_chart (fun x => f x - c) q r
      (chartMeromorphic_sub_const c hf) hr_src, chartRep_sub_const]
  -- Transfer to G - c via meromorphicOrderAt_congr
  have h_congr : (fun z => chartRep (RS := RS) f q z - c)
      =ᶠ[nhdsWithin (e_q r) {e_q r}ᶜ] (fun z => G z - c) := by
    by_cases hrq : r = q
    · -- r = q: e_q r = z₀, use original agreement
      subst hrq
      filter_upwards [hG_agree] with z hz
      rw [hz]
    · -- r ≠ q: e_q r ≠ z₀, agreement holds on neighborhood of e_q r
      have hne_z₀ : e_q r ≠ z₀ := by
        intro h
        exact hrq (e_q.injOn hr_src (mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) q) h)
      -- On U ∩ {z₀}ᶜ (open, contains e_q r), chartRep f q = G
      have h_agree_nhd : ∀ᶠ w in nhds (e_q r),
          chartRep (RS := RS) f q w = G w :=
        Filter.eventually_of_mem
          ((hU_open.inter (isClosed_singleton (x := z₀)).isOpen_compl).mem_nhds
            ⟨hr_U, show e_q r ∈ ({z₀} : Set ℂ)ᶜ from fun h => hne_z₀ h⟩)
          (fun w ⟨hw_U, hw_ne⟩ => (hU_sub w hw_U).2.2
            (show w ≠ z₀ from fun h => hw_ne (Set.mem_singleton_iff.mpr h)))
      filter_upwards [h_agree_nhd.filter_mono nhdsWithin_le_nhds] with z hz
      rw [hz]
  rw [meromorphicOrderAt_congr h_congr]
  exact meromorphicOrderAt_analytic_sub_const_eq_zero hG_ana_w hG_ne_c

/-- On a compact subset of a Riemann surface disjoint from all poles,
    for large |c|, chartOrderAt(f-c, q) = 0 for all q in the subset.

    Uses `chartOrderAt_sub_const_eq_zero_near_nonneg` at each point of K,
    then compactness to extract a finite subcover and uniform bound. -/
theorem no_support_on_compact_away_from_poles (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hne_top : ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) f q ≠ ⊤)
    (K : Set CRS.toRiemannSurface.carrier)
    (hK : @IsCompact CRS.toRiemannSurface.carrier CRS.toRiemannSurface.topology K)
    (hK_no_pole : ∀ q ∈ K,
      (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f q) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℂ, C < ‖c‖ → ∀ q ∈ K,
      chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) q = 0 := by
  letI := CRS.toRiemannSurface.topology
  letI := CRS.toRiemannSurface.chartedSpace
  haveI := CRS.toRiemannSurface.isManifold
  haveI := CRS.toRiemannSurface.t2
  haveI : CompactSpace CRS.toRiemannSurface.carrier := CRS.compact
  -- For each point (K or not), define an open neighborhood and bound
  -- For q ∈ K: use chartOrderAt_sub_const_eq_zero_near_nonneg
  -- For q ∉ K: use trivial Set.univ
  have h_local_data : ∀ q, ∃ V ∈ nhds q, ∃ Mb : ℝ, 0 < Mb ∧
      (q ∈ K → ∀ r ∈ V, ∀ c : ℂ, Mb < ‖c‖ →
        chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) r = 0) := by
    intro q
    by_cases hq : q ∈ K
    · obtain ⟨V, hV, Mb, hMb_pos, hMb_bound⟩ :=
        chartOrderAt_sub_const_eq_zero_near_nonneg hf (hne_top q) (hK_no_pole q hq)
      exact ⟨V, hV, Mb, hMb_pos, fun _ => hMb_bound⟩
    · exact ⟨Set.univ, Filter.univ_mem, 1, one_pos, fun h => absurd h hq⟩
  choose V hV_nhds Mb hMb_pos hMb_prop using h_local_data
  -- Extract finite subcover of K
  obtain ⟨t, ht_sub, ht_cover⟩ := hK.elim_nhds_subcover V (fun q _ => hV_nhds q)
  -- Handle empty K
  by_cases hK_emp : K = ∅
  · subst hK_emp; exact ⟨1, one_pos, fun _ _ _ hq => absurd hq (Set.mem_empty_iff_false _).mp⟩
  -- K nonempty → t nonempty
  have hK_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_emp
  have ht_ne : t.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    obtain ⟨q, hq⟩ := hK_ne
    have := ht_cover hq
    rw [h] at this; simp at this
  -- Take C = max bound over t + 1
  set C := t.sup' ht_ne Mb + 1
  have ⟨i₀, hi₀⟩ := ht_ne
  refine ⟨C, by linarith [t.le_sup' Mb hi₀, hMb_pos i₀], ?_⟩
  intro c hc q hq
  -- q ∈ K ⊆ ⋃ i ∈ t, V i
  obtain ⟨i, hi_t, hq_Vi⟩ := Set.mem_iUnion₂.mp (ht_cover hq)
  -- Mb i ≤ sup < C < ‖c‖
  have hc_bound : Mb i < ‖c‖ :=
    lt_of_le_of_lt (le_of_lt (lt_of_le_of_lt (t.le_sup' Mb hi_t) (by linarith))) hc
  exact hMb_prop i (ht_sub i hi_t) q hq_Vi c hc_bound

/-- chartOrderSum(f - c) = 0 for sufficiently large |c|.

    Near each pole of f of order -n, LMT on the inverse function 1/f shows
    that f takes value c exactly n times (each simple), contributing +n to zeros
    and -n from the pole. Away from poles, f is bounded so f ≠ c for large c.
    Total: 0. -/
theorem chartOrderSum_zero_large_c (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hne_top : ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) f q ≠ ⊤) :
    ∃ c₀ : ℂ, chartOrderSum CRS (fun x => f x - c₀)
      (chartMeromorphic_sub_const c₀ hf)
      (chartOrderSupport_sub_const_finite CRS f c₀ hf) = 0 := by
  sorry
/-- **Degree theory**: chartOrderSum = 0 for nonconstant chart-meromorphic functions.

    Uses:
    - `chartOrderSum_locally_constant`: N(c) = chartOrderSum(f-c) is locally constant
    - `chartOrderSum_zero_large_c`: N(c₀) = 0 for some c₀
    - ℂ connected: locally constant + connected → constant
    - N(0) = chartOrderSum(f): by extensionality (f - 0 = f) -/
theorem chartOrderSum_eq_zero_of_nonconstant (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hsupp : (chartOrderSupport (RS := CRS.toRiemannSurface) f).Finite)
    (hne_top : ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) f q ≠ ⊤) :
    chartOrderSum CRS f hf hsupp = 0 := by
  -- Define N(c) = chartOrderSum(f - c)
  set N : ℂ → ℤ := fun c =>
    chartOrderSum CRS (fun x => f x - c)
      (chartMeromorphic_sub_const c hf)
      (chartOrderSupport_sub_const_finite CRS f c hf) with hN_def
  -- Step 1: N is locally constant
  have hN_lc : IsLocallyConstant N :=
    chartOrderSum_locally_constant CRS f hf hne_top
  -- Step 2: ∃ c₀ with N(c₀) = 0
  obtain ⟨c₀, hc₀⟩ := chartOrderSum_zero_large_c CRS f hf hne_top
  -- Step 3: N is constant (ℂ is connected, N locally constant → N constant on connected sets)
  have hN_eq : N 0 = N c₀ :=
    hN_lc.apply_eq_of_isPreconnected isPreconnected_univ
      (Set.mem_univ _) (Set.mem_univ _)
  -- Step 4: N(0) = chartOrderSum(f)
  have hN_zero : N 0 = chartOrderSum CRS f hf hsupp :=
    chartOrderSum_sub_zero CRS f hf hsupp _ _
  -- Conclude
  linarith [hN_eq, hc₀, hN_zero]

/-- **Degree theory**: On a compact RS, the total zero order equals the total pole order
    for any nonconstant chart-meromorphic function. This is the core degree theory statement.

    **Proof sketch** (degree theory / fiber multiplicity constancy):
    1. Define N(c) = total multiplicity of "zeros of f - c" (via chartOrderAt)
    2. N(c) is locally constant in c:
       - At each zero of f - c₀: the local mapping theorem gives exactly k zeros
         of f - c near that zero for c near c₀
       - At regular non-zeros: the meromorphic normal form (via
         `tendsto_nhds_of_meromorphicOrderAt_nonneg`) shows no zeros of f - c appear nearby
       - At poles: pole invariance (`chartOrderAt_sub_const_at_pole`) shows f - c
         still has a pole, contributing nothing to N
       - Compactness of RS gives a uniform ε
    3. N is constant on ℂ (ℂ is connected)
    4. N(0) = totalZeroOrder(f), and N(c) = totalPoleOrder(f) for |c| sufficiently large
       (when all preimages of c are near poles, by `tendsto_cobounded_of_meromorphicOrderAt_neg`)
    5. Therefore totalZeroOrder(f) = totalPoleOrder(f) -/
theorem totalZeroOrder_eq_totalPoleOrder (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hsupp : (chartOrderSupport (RS := CRS.toRiemannSurface) f).Finite)
    (_hne : ∃ p, f p ≠ 0) :
    totalZeroOrder CRS f (zeroSet_finite CRS f hf hsupp) =
    totalPoleOrder CRS f (poleSet_finite CRS f hf hsupp) := by
  letI := CRS.toRiemannSurface.topology
  letI := CRS.toRiemannSurface.chartedSpace
  haveI := CRS.toRiemannSurface.isManifold
  haveI := CRS.toRiemannSurface.connected
  haveI := CRS.toRiemannSurface.t2
  haveI : CompactSpace CRS.toRiemannSurface.carrier := CRS.compact
  -- Case 1: All chart orders are ⊤ → both TZO and TPO are 0 (trivial)
  by_cases h_trivial : ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) f q = ⊤
  · -- zeroSet is empty: order = ⊤ ≠ (⊤ : WithTop ℤ) fails (tautologically false)
    have hzero_empty : (zeroSet (RS := CRS.toRiemannSurface) f) = ∅ := by
      ext p; simp only [zeroSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _; exact absurd (h_trivial p)
    -- poleSet is empty: ⊤ is not < 0
    have hpole_empty : (poleSet (RS := CRS.toRiemannSurface) f) = ∅ := by
      ext p; simp only [poleSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rw [h_trivial p]; exact not_lt.mpr le_top
    simp only [totalZeroOrder, totalPoleOrder]
    rw [show (zeroSet_finite CRS f hf hsupp).toFinset = ∅ from by
          rw [← Finset.val_eq_zero]; ext x
          simp [hzero_empty],
        show (poleSet_finite CRS f hf hsupp).toFinset = ∅ from by
          rw [← Finset.val_eq_zero]; ext x
          simp [hpole_empty]]
    simp
  -- Case 2: Nontrivial — some order is not ⊤
  push_neg at h_trivial
  obtain ⟨p₀, hp₀⟩ := h_trivial
  have hne_top : ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) f q ≠ ⊤ :=
    fun q => chartOrderAt_ne_top_of_ne_top_somewhere f hf p₀ hp₀ q
  -- Reduce to: chartOrderSum = 0 (which gives TZO - TPO = 0 by chartOrderSum_split)
  suffices hsum0 : chartOrderSum CRS f hf hsupp = 0 by
    have hsplit := chartOrderSum_split CRS f hf hsupp
    -- Bridge: totalZeroOrder is definitionally the Finset.sum in chartOrderSum_split
    have hdef : totalZeroOrder CRS f (zeroSet_finite CRS f hf hsupp) =
      (zeroSet_finite CRS f hf hsupp).toFinset.sum
        (fun p => (chartOrderAt (RS := CRS.toRiemannSurface) f p).getD 0) := rfl
    linarith
  exact chartOrderSum_eq_zero_of_nonconstant CRS f hf hsupp hne_top

/-- **The argument principle for chart-meromorphic functions.**

On a compact Riemann surface, the total zero order equals the total pole order
for any nonconstant chart-meromorphic function. Equivalently, chartOrderSum = 0.

**Proof sketch:**
1. Define N(c) = fiber multiplicity at c (sum of local orders over preimages)
2. N(c) is constant (local mapping theorem + compactness + connectedness)
3. N(0) = total zero order
4. For large |c|, preimages of c are all near poles, giving N(c) = total pole order
5. Total zero order = N(0) = N(large c) = total pole order
6. chartOrderSum = total zero order - total pole order = 0 -/
theorem chartOrderSum_eq_zero (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hsupp : (chartOrderSupport (RS := CRS.toRiemannSurface) f).Finite)
    (hne : ∃ p, f p ≠ 0) :
    chartOrderSum CRS f hf hsupp = 0 := by
  rw [chartOrderSum_split CRS f hf hsupp]
  have h := totalZeroOrder_eq_totalPoleOrder CRS f hf hsupp hne
  simp only [totalZeroOrder] at h
  linarith

/-- **The argument principle for chart-meromorphic functions on compact surfaces.**

    For any nonzero chart-meromorphic function on a compact Riemann surface,
    the sum of orders over all points is zero.

    This wraps `chartOrderSum_eq_zero` with the canonical name used by downstream
    consumers (e.g., `zero_counting_linear_combination` in RiemannRoch.lean). -/
theorem chartMeromorphic_argument_principle (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hsupp : (chartOrderSupport (RS := CRS.toRiemannSurface) f).Finite)
    (hne : ∃ p, f p ≠ 0) :
    chartOrderSum CRS f hf hsupp = 0 :=
  chartOrderSum_eq_zero CRS f hf hsupp hne

end RiemannSurfaces.Analytic
