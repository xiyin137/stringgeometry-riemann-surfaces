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
      rw [dist_zero_right]
      exact (hroot_small ζ hζ).trans_le (min_le_right _ _)
    -- R.symm(ζ) ∈ B(z₀, r) for each root ζ (δ₁ → R.symm lands in B(z₀, r))
    have hroot_ball : ∀ ζ : ℂ, ζ ^ k = w → dist (R.symm ζ) z₀ < r := by
      intro ζ hζ
      apply hδ₁_sub
      rw [dist_zero_right]
      exact (hroot_small ζ hζ).trans_le (min_le_left _ _)
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
    rw [h_preim_eq, Set.ncard_image_of_injOn hR_symm_inj]
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
  haveI : CompactSpace CRS.toRiemannSurface.carrier := CRS.compact
  -- Proof by contradiction: assume the fiber is infinite
  by_contra h_inf
  rw [Set.not_finite] at h_inf
  -- Step 1: The infinite set has an accumulation point p₀ (compact + infinite)
  obtain ⟨p₀, hacc⟩ := h_inf.exists_accPt_principal
  -- Step 2: p₀ cannot be a pole
  have h_not_pole : (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p₀ := by
    by_contra h_pole
    push_neg at h_pole
    have h_ev_ne := eventually_ne_const_at_pole
      (RS := CRS.toRiemannSurface) f hf p₀ h_pole c
    rw [accPt_iff_frequently_nhdsNE] at hacc
    have h_freq_eq : ∃ᶠ z in nhdsWithin p₀ {p₀}ᶜ, f z = c :=
      hacc.mono (fun z hz => hz.1)
    exact (h_freq_eq.and_eventually h_ev_ne).exists.elim (fun z ⟨heq, hne'⟩ => hne' heq)
  -- Step 3: By AnalyticAt and identity principle, f ≡ c near p₀
  have h_ana := hreg p₀ h_not_pole
  have h_ana_sub : AnalyticAt ℂ (fun z =>
      chartRep (RS := CRS.toRiemannSurface) f p₀ z - c)
      (chartPt (RS := CRS.toRiemannSurface) p₀) :=
    h_ana.sub analyticAt_const
  -- S accumulates at p₀: chartRep f p₀ - c = 0 frequently in punctured chart nhd
  have h_freq_chart : ∃ᶠ z in nhdsWithin
      (chartPt (RS := CRS.toRiemannSurface) p₀)
      {chartPt (RS := CRS.toRiemannSurface) p₀}ᶜ,
      chartRep (RS := CRS.toRiemannSurface) f p₀ z - c = 0 := by
    rw [Filter.Frequently]
    intro h_ev
    rw [accPt_iff_frequently_nhdsNE] at hacc
    apply hacc
    have h_ne := eventually_of_chartRep (RS := CRS.toRiemannSurface)
      (P := fun v => v - c ≠ 0) f p₀ h_ev
    exact h_ne.mono fun q hq hqS => hq (show f q - c = 0 by rw [hqS.1]; ring)
  -- By identity principle: chartRep f p₀ - c ≡ 0 near chartPt p₀
  have h_ev_zero : ∀ᶠ z in nhds (chartPt (RS := CRS.toRiemannSurface) p₀),
      chartRep (RS := CRS.toRiemannSurface) f p₀ z - c = 0 :=
    h_ana_sub.frequently_zero_iff_eventually_zero.mp h_freq_chart
  -- So f ≡ c in a manifold neighborhood of p₀
  have h_f_eq_c_nhd : ∀ᶠ q in nhds p₀, f q = c := by
    -- Convert h_ev_zero: chartRep f p₀ z = c near chartPt p₀
    have h_ev_c : ∀ᶠ z in nhds (chartPt (RS := CRS.toRiemannSurface) p₀),
        chartRep (RS := CRS.toRiemannSurface) f p₀ z = c :=
      h_ev_zero.mono (fun z hz => sub_eq_zero.mp hz)
    -- Pull back through extChartAt p₀ (continuous at p₀, maps p₀ to chartPt p₀)
    have h_pulled := (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) p₀).eventually h_ev_c
    -- h_pulled : ∀ᶠ q in nhds p₀, chartRep f p₀ (extChartAt p₀ q) = c
    -- Combined with left_inv: chartRep f p₀ (extChartAt p₀ q) = f q for q ∈ source
    have hsrc : (extChartAt 𝓘(ℂ, ℂ) p₀).source ∈ nhds p₀ :=
      (isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) p₀).mem_nhds (mem_extChartAt_source p₀)
    exact (h_pulled.and hsrc).mono fun q ⟨hq, hq_src⟩ => by
      simp only [chartRep, Function.comp_apply,
        (extChartAt 𝓘(ℂ, ℂ) p₀).left_inv hq_src] at hq
      exact hq
  -- Step 4: By identity principle on RS, f - c has order ⊤ everywhere
  have hg_cm : IsChartMeromorphic (RS := CRS.toRiemannSurface) (fun x => f x - c) := by
    have heq : (fun x => f x - c) = fun x => f x + (-c) := by ext x; ring
    rw [heq]; exact chartMeromorphic_add hf (chartMeromorphic_const (-c))
  have hg_top : chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p₀ = ⊤ := by
    apply chartOrderAt_eq_top_of_zero_on_nhd
    exact h_f_eq_c_nhd.mono (fun q hq => show f q - c = 0 by rw [hq]; ring)
  -- By identity principle: ∀ q, chartOrderAt (f - c) q = ⊤
  have hg_all_top : ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) q = ⊤ := by
    intro q; by_contra h_ne_top
    exact absurd hg_top (chartOrderAt_ne_top_of_ne_top_somewhere _ hg_cm q h_ne_top p₀)
  -- Step 5: f has no poles (at a pole, f → ∞ but f ≡ c in punctured nhd)
  have h_no_poles : ∀ q, (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f q := by
    intro q; by_contra h_pole; push_neg at h_pole
    -- chartRep (f - c) q ≡ 0 in punctured nhd
    have hg_ev_zero := meromorphicOrderAt_eq_top_iff.mp (hg_all_top q)
    -- chartRep (f - c) q z = chartRep f q z - c (definitional)
    have hg_rep : ∀ z, chartRep (RS := CRS.toRiemannSurface) (fun x => f x - c) q z =
        chartRep (RS := CRS.toRiemannSurface) f q z - c := by
      intro z; simp [chartRep, Function.comp_apply]
    -- So chartRep f q ≡ c in punctured nhd
    have hf_ev_c : ∀ᶠ z in nhdsWithin (chartPt (RS := CRS.toRiemannSurface) q)
        {chartPt (RS := CRS.toRiemannSurface) q}ᶜ,
        chartRep (RS := CRS.toRiemannSurface) f q z = c :=
      hg_ev_zero.mono (fun z hz => sub_eq_zero.mp (hg_rep z ▸ hz))
    -- But chartRep f q → ∞ at the pole
    have htend := tendsto_cobounded_of_meromorphicOrderAt_neg h_pole
    rw [← tendsto_norm_atTop_iff_cobounded] at htend
    -- Contradiction: ‖chartRep f q z‖ → ∞ but ‖chartRep f q z‖ ≤ ‖c‖ eventually
    have h_bdd : ∀ᶠ z in nhdsWithin (chartPt (RS := CRS.toRiemannSurface) q)
        {chartPt (RS := CRS.toRiemannSurface) q}ᶜ,
        ‖chartRep (RS := CRS.toRiemannSurface) f q z‖ ≤ ‖c‖ :=
      hf_ev_c.mono (fun z hz => by rw [hz])
    have h_big := htend.eventually (Filter.eventually_ge_atTop (‖c‖ + 1))
    obtain ⟨z, hz_bdd, hz_big⟩ := (h_bdd.and h_big).exists; linarith
  -- Step 6: f = c at every point (by continuity of analytic functions)
  have h_f_eq_c : ∀ q, f q = c := by
    intro q
    have h_ana_q := hreg q (h_no_poles q)
    have h_cont := h_ana_q.continuousAt
    have hg_ev_zero := meromorphicOrderAt_eq_top_iff.mp (hg_all_top q)
    have hg_rep : ∀ z, chartRep (RS := CRS.toRiemannSurface) (fun x => f x - c) q z =
        chartRep (RS := CRS.toRiemannSurface) f q z - c := by
      intro z; simp [chartRep, Function.comp_apply]
    have hf_ev_c : ∀ᶠ z in nhdsWithin (chartPt (RS := CRS.toRiemannSurface) q)
        {chartPt (RS := CRS.toRiemannSurface) q}ᶜ,
        chartRep (RS := CRS.toRiemannSurface) f q z = c :=
      hg_ev_zero.mono (fun z hz => sub_eq_zero.mp (hg_rep z ▸ hz))
    -- chartRep f q → c in punctured nhd (from hf_ev_c)
    -- chartRep f q → chartRep f q (chartPt q) = f q (from ContinuousAt)
    -- Uniqueness of limits: f q = c
    haveI := rs_nhdsNE_neBot (RS := CRS.toRiemannSurface) q
    have h_lim1 : Filter.Tendsto (chartRep (RS := CRS.toRiemannSurface) f q)
        (nhdsWithin (chartPt (RS := CRS.toRiemannSurface) q)
          {chartPt (RS := CRS.toRiemannSurface) q}ᶜ) (nhds c) :=
      tendsto_nhds_of_eventually_eq hf_ev_c
    have h_lim2 : Filter.Tendsto (chartRep (RS := CRS.toRiemannSurface) f q)
        (nhdsWithin (chartPt (RS := CRS.toRiemannSurface) q)
          {chartPt (RS := CRS.toRiemannSurface) q}ᶜ)
        (nhds (chartRep (RS := CRS.toRiemannSurface) f q
          (chartPt (RS := CRS.toRiemannSurface) q))) :=
      h_cont.tendsto.mono_left nhdsWithin_le_nhds
    have h_val := tendsto_nhds_unique h_lim2 h_lim1
    rw [chartRep_apply_chartPt] at h_val; exact h_val
  -- Step 7: Contradiction with ∃ p, f p ≠ c
  obtain ⟨p, hp⟩ := hne
  exact hp (h_f_eq_c p)

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
  exact ⟨fun h0 => by rw [h0] at hp; exact (lt_irrefl 0) (by exact_mod_cast hp.1), hp.2⟩

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
      · right; exact_mod_cast hm_neg
      · left; exact ⟨by exact_mod_cast hm_pos, WithTop.coe_ne_top⟩
  · intro h
    rcases h with ⟨hpos, hne_top⟩ | hneg
    · exact ⟨ne_of_gt hpos, hne_top⟩
    · constructor
      · exact fun h0 => absurd (h0 ▸ hneg : (0 : WithTop ℤ) < 0) (lt_irrefl 0)
      · exact fun htop => absurd (htop ▸ hneg) (not_lt.mpr le_top)

/-- zeroSet and poleSet are disjoint. -/
theorem zeroSet_poleSet_disjoint (f : RS.carrier → ℂ) :
    Disjoint (zeroSet (RS := RS) f) (poleSet (RS := RS) f) := by
  rw [Set.disjoint_iff]
  intro p ⟨hz, hp⟩
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
  -- Step 1: Extract pole order n ≥ 1
  have hne_top : meromorphicOrderAt g z₀ ≠ ⊤ := by
    intro h; rw [h] at hpole; exact absurd le_top (not_le.mpr hpole)
  set m : ℤ := (meromorphicOrderAt g z₀).untop₀ with hm_def
  have hm_coe : meromorphicOrderAt g z₀ = (m : WithTop ℤ) :=
    (WithTop.coe_untop₀_of_ne_top hne_top).symm
  have hm_neg : m < 0 := by
    have h := hpole; rw [hm_coe] at h; exact_mod_cast h
  have hm_pos : 0 < -m := neg_pos.mpr hm_neg
  set n := (-m).toNat with hn_def
  have hn_eq : (n : ℤ) = -m := Int.toNat_of_nonneg (le_of_lt hm_pos)
  have hn_pos : 1 ≤ n := by omega
  have hm_eq : meromorphicOrderAt g z₀ = (-(n : ℤ) : WithTop ℤ) := by
    rw [hm_coe]; congr 1; linarith [hn_eq]
  -- Step 2: Construct analytic reciprocal H of g⁻¹
  have hg_inv : MeromorphicAt g⁻¹ z₀ := hg.inv
  have hg_inv_ord : meromorphicOrderAt g⁻¹ z₀ = (n : ℤ) := by
    rw [meromorphicOrderAt_inv, hm_eq]
    simp
  have hg_inv_nonneg : (0 : WithTop ℤ) ≤ meromorphicOrderAt g⁻¹ z₀ := by
    rw [hg_inv_ord]; exact_mod_cast Nat.zero_le n
  have hg_inv_ne_top : meromorphicOrderAt g⁻¹ z₀ ≠ ⊤ := by
    rw [hg_inv_ord]; exact WithTop.coe_ne_top
  obtain ⟨H, hH_ana, hH_agree, hH_mord⟩ :=
    exists_analyticExtension_of_nonneg_order hg_inv hg_inv_ne_top hg_inv_nonneg
  -- Step 3: Get analytic order of H
  have hH_mord_eq : meromorphicOrderAt H z₀ = (n : ℤ) := by rw [← hg_inv_ord, ← hH_mord]
  have hH_aord : analyticOrderAt H z₀ = n := by
    have h := hH_ana.meromorphicOrderAt_eq
    rw [hH_mord_eq] at h
    -- h : (n : WithTop ℤ) = (analyticOrderAt H z₀).map (↑)
    cases hn : analyticOrderAt H z₀ with
    | top => simp [hn] at h
    | coe k =>
      simp [hn] at h
      exact_mod_cast h.symm
  have hH0 : H z₀ = 0 := by
    rw [← hH_ana.analyticOrderAt_ne_zero]
    rw [hH_aord]; exact_mod_cast Nat.one_le_iff_ne_zero.mp hn_pos
  -- Step 3.5: Extract agreement ball: (g z)⁻¹ = H z for z near z₀, z ≠ z₀
  have hH_agree_ev : ∀ᶠ z in nhds z₀, z ∈ ({z₀} : Set ℂ)ᶜ → (g z)⁻¹ = H z := by
    rw [← eventually_nhdsWithin_iff]; exact hH_agree
  obtain ⟨r_a, hr_a, hagree_ball⟩ := Metric.eventually_nhds_iff.mp hH_agree_ev
  -- Step 3.6: Extract analyticity ball: H is analytic at all points near z₀
  obtain ⟨r_ana, hr_ana, hH_ana_ball⟩ := Metric.eventually_nhds_iff.mp hH_ana.eventually_analyticAt
  -- Step 4: Apply LMT to H with r_bound = min (min r_a r_ana) ρ
  obtain ⟨r, hr_pos, hr_le, ε₁, hε₁, h_iso, h_ncard, h_lmt_deriv⟩ :=
    local_mapping_theorem hn_pos hH_ana hH0 hH_aord (lt_min (lt_min hr_a hr_ana) hρ)
  have hr_le_ra : r ≤ r_a := le_trans hr_le (le_trans (min_le_left _ _) (min_le_left _ _))
  have hr_le_rana : r ≤ r_ana := le_trans hr_le (le_trans (min_le_left _ _) (min_le_right _ _))
  have hr_le_ρ : r ≤ ρ := le_trans hr_le (min_le_right _ _)
  -- Step 5: Choose C = 1/ε₁
  refine ⟨r, hr_pos, hr_le_ρ, 1 / ε₁, div_pos one_pos hε₁, fun c hc => ?_⟩
  -- Step 6: For ‖c‖ > 1/ε₁, we have ‖c⁻¹‖ < ε₁
  have hc_ne : c ≠ 0 := by
    intro h; subst h; simp at hc; linarith [div_pos one_pos hε₁]
  have hc_pos : 0 < ‖c‖ := by positivity
  have h_inv_small : ‖c⁻¹‖ < ε₁ := by
    rw [norm_inv]; exact inv_lt_of_inv_lt₀ hε₁ (by rwa [← one_div])
  have h_inv_pos : 0 < ‖c⁻¹‖ := by rw [norm_inv]; exact inv_pos_of_pos hc_pos
  have hcinv_ne : c⁻¹ ≠ 0 := inv_ne_zero hc_ne
  -- Step 7: Preimage set P = {z | ‖z - z₀‖ < r ∧ H z = c⁻¹}
  set P : Set ℂ := {z : ℂ | ‖z - z₀‖ < r ∧ H z = c⁻¹}
  have hP_ncard : P.ncard = n := h_ncard c⁻¹ h_inv_pos h_inv_small
  have hP_fin : P.Finite := by
    by_contra h_inf; rw [Set.not_finite] at h_inf
    have := h_inf.ncard; rw [hP_ncard] at this; exact absurd this (by omega)
  -- Step 8: Convert to Finset
  set PF := hP_fin.toFinset with hPF_def
  have hPF_card : PF.card = n := by
    rw [hPF_def, ← Set.ncard_eq_toFinset_card P hP_fin]; exact hP_ncard
  -- Step 9: z₀ ∉ PF (since H(z₀) = 0 ≠ c⁻¹)
  have hz₀_notin : z₀ ∉ PF := by
    rw [Set.Finite.mem_toFinset]; intro ⟨_, h⟩; exact hcinv_ne (hH0 ▸ h.symm)
  -- Helper: for z ∈ B(z₀, r) with z ≠ z₀, establish g = H⁻¹ on a neighborhood of z
  have g_eq_Hinv_near (z : ℂ) (hz_ball : ‖z - z₀‖ < r) (hz_ne : z ≠ z₀) :
      g =ᶠ[nhds z] fun w => (H w)⁻¹ := by
    have hz_ra : dist z z₀ < r_a := lt_of_lt_of_le (by rwa [dist_eq_norm]) hr_le_ra
    set δ := min (r_a - dist z z₀) (dist z z₀ / 2) with hδ_def
    have hδ_pos : 0 < δ := lt_min (by linarith) (half_pos (dist_pos.mpr hz_ne))
    apply Filter.eventually_of_mem (Metric.ball_mem_nhds z hδ_pos)
    intro w hw
    have hw_dist : dist w z < δ := Metric.mem_ball.mp hw
    have hw_ra : dist w z₀ < r_a := by
      linarith [dist_triangle w z z₀, min_le_left (r_a - dist z z₀) (dist z z₀ / 2)]
    have hw_ne : w ≠ z₀ := by
      intro heq; rw [heq] at hw_dist
      linarith [min_le_right (r_a - dist z z₀) (dist z z₀ / 2), dist_comm z z₀,
        (dist_nonneg : 0 ≤ dist z₀ z)]
    calc g w = ((g w)⁻¹)⁻¹ := (inv_inv _).symm
      _ = (H w)⁻¹ := by rw [hagree_ball hw_ra (Set.mem_compl_singleton_iff.mpr hw_ne)]
  -- Step 10: Elements of PF are simple zeros of g - c
  have hPF_order : ∀ z ∈ PF, meromorphicOrderAt (fun w => g w - c) z = 1 := by
    intro z hz
    rw [Set.Finite.mem_toFinset] at hz; obtain ⟨hz_ball, hz_eq⟩ := hz
    have hz_ne : z ≠ z₀ := by intro h; subst h; exact hcinv_ne (hH0 ▸ hz_eq.symm)
    have hz_rana : dist z z₀ < r_ana := lt_of_lt_of_le (by rwa [dist_eq_norm]) hr_le_rana
    have hH_ana_z : AnalyticAt ℂ H z := hH_ana_ball hz_rana
    have hHz_ne : H z ≠ 0 := h_iso z hz_ball hz_ne
    have hderiv_z : deriv H z ≠ 0 := h_lmt_deriv z hz_ball hz_ne
    have hg_eq : g =ᶠ[nhds z] fun w => (H w)⁻¹ := g_eq_Hinv_near z hz_ball hz_ne
    -- g z = c (from H z = c⁻¹ and (g z)⁻¹ = H z)
    have hz_ra : dist z z₀ < r_a := lt_of_lt_of_le (by rwa [dist_eq_norm]) hr_le_ra
    have hg_inv_z : (g z)⁻¹ = H z :=
      hagree_ball hz_ra (Set.mem_compl_singleton_iff.mpr hz_ne)
    have hgz_eq_c : g z = c := inv_injective (by rw [hg_inv_z, hz_eq])
    -- g - c is analytic at z with (g-c)(z) = 0
    have hg_ana_z : AnalyticAt ℂ g z := (hH_ana_z.inv hHz_ne).congr hg_eq.symm
    have hgc_ana : AnalyticAt ℂ (fun w => g w - c) z := hg_ana_z.sub analyticAt_const
    have hgc_zero : (fun w => g w - c) z = 0 := by simp [hgz_eq_c]
    -- deriv(g - c)(z) ≠ 0
    have hgc'_ne : deriv (fun w => g w - c) z ≠ 0 := by
      have hg_deriv : deriv g z = -deriv H z / (H z) ^ 2 := by
        rw [Filter.EventuallyEq.deriv_eq hg_eq]
        exact (hH_ana_z.differentiableAt.hasDerivAt.inv hHz_ne).deriv
      rw [(hg_ana_z.differentiableAt.hasDerivAt.sub_const c).deriv, hg_deriv]
      exact div_ne_zero (neg_ne_zero.mpr hderiv_z) (pow_ne_zero 2 hHz_ne)
    exact meromorphicOrderAt_eq_one_of_simple_zero hgc_ana hgc_zero hgc'_ne
  -- Step 11: Construct S = {z₀} ∪ PF
  refine ⟨Finset.cons z₀ PF hz₀_notin, ?_, ?_, ?_⟩
  · -- Condition 1: S ⊆ B(z₀, r)
    intro z hz; rw [Finset.mem_cons] at hz
    rcases hz with rfl | hz
    · simp [hr_pos]
    · rw [Set.Finite.mem_toFinset] at hz; exact hz.1
  · -- Condition 2: S contains all nonzero-finite-order points
    intro z hz_ball hord_ne_zero hord_ne_top
    rw [Finset.mem_cons]
    by_cases hzz : z = z₀
    · left; exact hzz
    · right
      have hz_ra : dist z z₀ < r_a := lt_of_lt_of_le (by rwa [dist_eq_norm]) hr_le_ra
      have hz_rana : dist z z₀ < r_ana := lt_of_lt_of_le (by rwa [dist_eq_norm]) hr_le_rana
      have hH_ana_z : AnalyticAt ℂ H z := hH_ana_ball hz_rana
      have hHz_ne : H z ≠ 0 := h_iso z hz_ball hzz
      have hg_inv_z : (g z)⁻¹ = H z :=
        hagree_ball hz_ra (Set.mem_compl_singleton_iff.mpr hzz)
      have hg_eq : g =ᶠ[nhds z] fun w => (H w)⁻¹ := g_eq_Hinv_near z hz_ball hzz
      -- If g z ≠ c, then (g - c)(z) ≠ 0 and analytic → order 0, contradiction
      by_contra h_notin
      have hgz_ne_c : g z ≠ c := by
        intro hgc; apply h_notin; rw [Set.Finite.mem_toFinset]
        exact ⟨hz_ball, by rw [← hg_inv_z, hgc]⟩
      have hg_ana_z : AnalyticAt ℂ g z := (hH_ana_z.inv hHz_ne).congr hg_eq.symm
      have hgc_ana : AnalyticAt ℂ (fun w => g w - c) z := hg_ana_z.sub analyticAt_const
      have hgc_ne : (fun w => g w - c) z ≠ 0 := sub_ne_zero.mpr hgz_ne_c
      have hord_zero : meromorphicOrderAt (fun w => g w - c) z = 0 := by
        rw [hgc_ana.meromorphicOrderAt_eq]
        have : analyticOrderAt (fun w => g w - c) z = 0 := by
          by_contra h; exact hgc_ne (hgc_ana.analyticOrderAt_ne_zero.mp h)
        simp [this]
      exact hord_ne_zero hord_zero
  · -- Condition 3: sum = 0
    rw [Finset.sum_cons]
    -- Pole contribution at z₀: order = -n
    have h_pole_val : (meromorphicOrderAt (fun w => g w - c) z₀).getD 0 = -(n : ℤ) := by
      rw [meromorphicOrderAt_sub_const_at_pole_loc c hpole, hm_eq]
      rfl
    rw [h_pole_val]
    -- Zero contributions: each element of PF contributes 1, so sum = n
    have h_zero_sum : PF.sum (fun z => (meromorphicOrderAt (fun w => g w - c) z).getD 0) =
        (n : ℤ) := by
      have hsub : PF.sum (fun z => (meromorphicOrderAt (fun w => g w - c) z).getD 0) =
          PF.sum (fun _ => (1 : ℤ)) := Finset.sum_congr rfl (fun z hz => by
        rw [hPF_order z hz]; rfl)
      rw [hsub, Finset.sum_const, Nat.smul_one_eq_cast, hPF_card]
    rw [h_zero_sum]; omega

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
  have hm_neg : m < 0 := by rw [hm_coe] at hpole_z; exact_mod_cast hpole_z
  set n := (-m).toNat with hn_def
  have hn_eq : (n : ℤ) = -m := Int.toNat_of_nonneg (le_of_lt (neg_pos.mpr hm_neg))
  have hn_pos : 1 ≤ n := by omega
  have hm_eq : meromorphicOrderAt g z₀ = (-(n : ℤ) : WithTop ℤ) := by
    rw [hm_coe]; congr 1; linarith [hn_eq]
  have hg_inv : MeromorphicAt g⁻¹ z₀ := (hf q).inv
  have hg_inv_ord : meromorphicOrderAt g⁻¹ z₀ = (n : ℤ) := by
    rw [meromorphicOrderAt_inv, hm_eq]; simp
  have hg_inv_nonneg : (0 : WithTop ℤ) ≤ meromorphicOrderAt g⁻¹ z₀ := by
    rw [hg_inv_ord]; exact_mod_cast Nat.zero_le n
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
    have h_tend : Tendsto H (nhds z₀) (nhds 0) := by rw [← hH0]; exact hH_ana.continuousAt
    have h_norm : Tendsto (fun z => ‖H z‖) (nhds z₀) (nhds 0) := by
      simpa [norm_zero] using h_tend.norm
    exact h_norm.eventually (Iio_mem_nhds hδ_pos)
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
  -- Step 1: Get analytic extension G and extract order k
  obtain ⟨G, hG_ana, hG_agree, hG_mord⟩ :=
    exists_analyticExtension_of_nonneg_order (hf q) hne_top hord_nonneg
  -- Order of G - c₀ at z₀ matches chartOrderAt(f - c₀, q)
  have hGc₀_mord : meromorphicOrderAt (fun z => G z - c₀) z₀ =
      chartOrderAt (RS := RS) (fun x => f x - c₀) q := by
    have h_congr : (fun z => g z - c₀) =ᶠ[nhdsWithin z₀ {z₀}ᶜ] (fun z => G z - c₀) := by
      filter_upwards [hG_agree] with z hz; exact congr_arg (· - c₀) hz
    simp only [chartOrderAt, chartRep_sub_const]
    exact (meromorphicOrderAt_congr h_congr).symm
  -- Extract k as a natural number
  have hGc₀_pos : (0 : WithTop ℤ) < meromorphicOrderAt (fun z => G z - c₀) z₀ := by
    rw [hGc₀_mord]; exact hzero
  have hGc₀_ne_top : meromorphicOrderAt (fun z => G z - c₀) z₀ ≠ ⊤ := by
    rw [hGc₀_mord]; exact hzero_ne_top
  set ord_val : ℤ := (meromorphicOrderAt (fun z => G z - c₀) z₀).untop₀
  have hord_coe : meromorphicOrderAt (fun z => G z - c₀) z₀ = (ord_val : WithTop ℤ) :=
    (WithTop.coe_untop₀_of_ne_top hGc₀_ne_top).symm
  have hord_pos : 0 < ord_val := by rw [hord_coe] at hGc₀_pos; exact_mod_cast hGc₀_pos
  set k := ord_val.toNat
  have hk_eq : (k : ℤ) = ord_val := Int.toNat_of_nonneg (le_of_lt hord_pos)
  have hk_pos : 1 ≤ k := by omega
  -- Step 2: G - c₀ is analytic with G(z₀) = c₀ (vanishes)
  have hGc₀_ana : AnalyticAt ℂ (fun z => G z - c₀) z₀ := hG_ana.sub analyticAt_const
  have hGc₀_zero : (fun z => G z - c₀) z₀ = 0 := by
    have h_aord_ne : analyticOrderAt (fun z => G z - c₀) z₀ ≠ 0 := by
      intro h
      have h_eq := hGc₀_ana.meromorphicOrderAt_eq
      rw [h] at h_eq; simp at h_eq
      rw [h_eq] at hGc₀_pos; exact absurd hGc₀_pos (lt_irrefl _)
    exact hGc₀_ana.analyticOrderAt_ne_zero.mp h_aord_ne
  -- Step 3: Get analyticOrderAt = k
  have hGc₀_aord : analyticOrderAt (fun z => G z - c₀) z₀ = k := by
    have h_eq := hGc₀_ana.meromorphicOrderAt_eq
    rw [hord_coe] at h_eq
    cases h : analyticOrderAt (fun z => G z - c₀) z₀ with
    | top => simp [h] at h_eq
    | coe j =>
      simp [h] at h_eq
      have : (j : ℤ) = ord_val := by exact_mod_cast h_eq.symm
      exact_mod_cast (show (j : ℤ) = (k : ℤ) by rw [this, ← hk_eq])
  -- Step 4: Get agreement and analyticity balls FIRST (so we can pass them as LMT bound)
  obtain ⟨r_agr, hr_agr, h_agree_ball⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp hG_agree)
  obtain ⟨r_ana, hr_ana, hG_ana_ball⟩ :=
    Metric.eventually_nhds_iff.mp hG_ana.eventually_analyticAt
  -- Step 5: Apply LMT with combined bound so r ≤ r_agr, r_ana, ρ
  obtain ⟨r, hr_pos, hr_le_bound, ε_lmt, hε_lmt, h_iso, h_ncard, h_deriv⟩ :=
    local_mapping_theorem hk_pos hGc₀_ana hGc₀_zero hGc₀_aord
      (show (0 : ℝ) < min (min r_agr r_ana) ρ from lt_min (lt_min hr_agr hr_ana) hρ)
  -- Extract useful bounds
  have hr_le_agr : r ≤ r_agr :=
    le_trans hr_le_bound (le_trans (min_le_left _ _) (min_le_left _ _))
  have hr_le_ana : r ≤ r_ana :=
    le_trans hr_le_bound (le_trans (min_le_left _ _) (min_le_right _ _))
  have hr_le : r ≤ ρ := le_trans hr_le_bound (min_le_right _ _)
  -- Convenience: norm bound → dist bound
  have h_in_agr (z : ℂ) (hz : ‖z - z₀‖ < r) : dist z z₀ < r_agr :=
    lt_of_lt_of_le (by rwa [dist_eq_norm]) hr_le_agr
  have h_in_ana (z : ℂ) (hz : ‖z - z₀‖ < r) : dist z z₀ < r_ana :=
    lt_of_lt_of_le (by rwa [dist_eq_norm]) hr_le_ana
  -- Agreement transfer: g = G on nhds of z for z ≠ z₀ in ball
  have g_eq_G_near (z : ℂ) (hz_ball : ‖z - z₀‖ < r) (hz_ne : z ≠ z₀) :
      g =ᶠ[nhds z] G := by
    set d := min (r_agr - dist z z₀) (dist z z₀ / 2)
    have hd_pos : 0 < d :=
      lt_min (by linarith [h_in_agr z hz_ball]) (half_pos (dist_pos.mpr hz_ne))
    exact Filter.eventually_of_mem (Metric.ball_mem_nhds z hd_pos) fun w hw => by
      have hw_dist : dist w z < d := Metric.mem_ball.mp hw
      have hw_agr : dist w z₀ < r_agr := by
        linarith [dist_triangle w z z₀, min_le_left (r_agr - dist z z₀) (dist z z₀ / 2)]
      have hw_ne : w ≠ z₀ := by
        intro heq; rw [heq] at hw_dist
        linarith [min_le_right (r_agr - dist z z₀) (dist z z₀ / 2), dist_comm z z₀,
          (dist_nonneg : 0 ≤ dist z₀ z)]
      exact h_agree_ball hw_agr (Set.mem_compl_singleton_iff.mpr hw_ne)
  -- Step 6: Choose ε = ε_lmt
  refine ⟨r, hr_pos, hr_le, ε_lmt, hε_lmt, fun c hc => ?_⟩
  -- Transfer order value: chartOrderAt(f - c₀, q).getD 0 = k
  have hord_getD : (chartOrderAt (RS := RS) (fun x => f x - c₀) q).getD 0 = (k : ℤ) := by
    rw [← hGc₀_mord, hord_coe]; exact hk_eq.symm
  rw [hord_getD]
  -- Case split: c = c₀ or c ≠ c₀
  by_cases hc_eq : c = c₀
  · -- Case c = c₀: S = {z₀}, zero of order k
    refine ⟨{z₀}, ?_, ?_, ?_⟩
    · intro z hz; simp only [Finset.mem_singleton] at hz; subst hz
      simp [hr_pos]
    · intro z hz hord_ne0 hord_ne_top
      simp only [Finset.mem_singleton]
      by_contra hne
      have h_ne_zero : (fun w => G w - c₀) z ≠ 0 := h_iso z hz hne
      have h_congr : (fun w => g w - c) =ᶠ[nhdsWithin z {z}ᶜ] (fun w => G w - c) :=
        ((g_eq_G_near z hz hne).mono fun w hw => by
          show g w - c = G w - c; rw [hw]).filter_mono nhdsWithin_le_nhds
      rw [meromorphicOrderAt_congr h_congr] at hord_ne0
      -- h_ne_zero : G z - c₀ ≠ 0, and c = c₀, so G z ≠ c
      have hGz_ne_c : G z ≠ c := by rw [hc_eq]; exact sub_ne_zero.mp h_ne_zero
      exact hord_ne0 (meromorphicOrderAt_analytic_sub_const_eq_zero'
        (hG_ana_ball (h_in_ana z hz)) hGz_ne_c)
    · simp only [Finset.sum_singleton]
      have h_congr : (fun w => g w - c₀) =ᶠ[nhdsWithin z₀ {z₀}ᶜ] (fun w => G w - c₀) := by
        filter_upwards [hG_agree] with z hz
        exact congr_arg (· - c₀) hz
      rw [hc_eq, meromorphicOrderAt_congr h_congr, hord_coe]; exact hk_eq.symm
  · -- Case c ≠ c₀: LMT gives k simple zeros of G - c₀ = c - c₀
    have hc_ne : c - c₀ ≠ 0 := sub_ne_zero.mpr hc_eq
    have hc_pos : 0 < ‖c - c₀‖ := norm_pos_iff.mpr hc_ne
    -- Preimage set P = {z | ‖z - z₀‖ < r ∧ G(z) - c₀ = c - c₀}
    set P : Set ℂ := {z : ℂ | ‖z - z₀‖ < r ∧ (fun w => G w - c₀) z = c - c₀}
    have hP_ncard : P.ncard = k := h_ncard (c - c₀) hc_pos hc
    have hP_fin : P.Finite := by
      by_contra h_inf; rw [Set.not_finite] at h_inf
      have := h_inf.ncard; rw [hP_ncard] at this; exact absurd this (by omega)
    set PF := hP_fin.toFinset
    have hPF_card : PF.card = k := by
      rw [← Set.ncard_eq_toFinset_card P hP_fin]; exact hP_ncard
    -- z₀ ∉ PF (since (G - c₀)(z₀) = 0 ≠ c - c₀)
    have hz₀_notin : z₀ ∉ PF := by
      rw [Set.Finite.mem_toFinset]; intro ⟨_, h⟩
      exact hc_ne (show c - c₀ = 0 from h.symm.trans hGc₀_zero)
    -- Each z ∈ PF satisfies G(z) = c, so (G - c)(z) = 0 with simple zero
    have hPF_order : ∀ z ∈ PF, meromorphicOrderAt (fun w => G w - c) z = 1 := by
      intro z hz_mem
      rw [Set.Finite.mem_toFinset] at hz_mem; obtain ⟨hz_ball, hz_eq⟩ := hz_mem
      have hz_ne : z ≠ z₀ := by
        intro heq; subst heq; exact hc_ne (show c - c₀ = 0 from hz_eq.symm.trans hGc₀_zero)
      have hG_ana_z : AnalyticAt ℂ G z := hG_ana_ball (h_in_ana z hz_ball)
      -- G(z) = c from membership: G z - c₀ = c - c₀ implies G z = c
      have hGz_eq_c : G z = c := by
        have h : G z - c₀ = c - c₀ := hz_eq; linear_combination h
      -- (G - c) is analytic with (G - c)(z) = 0
      have hGc_ana : AnalyticAt ℂ (fun w => G w - c) z := hG_ana_z.sub analyticAt_const
      have hGc_zero : (fun w => G w - c) z = 0 := by simp [hGz_eq_c]
      -- deriv(G - c)(z) ≠ 0, using HasDerivAt.sub_const pattern (from pole helper)
      have hGc'_ne : deriv (fun w => G w - c) z ≠ 0 := by
        rw [(hG_ana_z.differentiableAt.hasDerivAt.sub_const c).deriv]
        have hd := h_deriv z hz_ball hz_ne
        rwa [(hG_ana_z.differentiableAt.hasDerivAt.sub_const c₀).deriv] at hd
      exact meromorphicOrderAt_eq_one_of_simple_zero hGc_ana hGc_zero hGc'_ne
    -- Build the result: PF is the support set with sum = k
    refine ⟨PF, ?_, ?_, ?_⟩
    · -- All elements of PF are in the ball
      intro z hz; rw [Set.Finite.mem_toFinset] at hz; exact hz.1
    · -- Capture: any z in ball with nonzero non-⊤ order is in PF
      intro z hz hord_ne0 hord_ne_top
      by_cases hz_ne : z = z₀
      · -- z = z₀: G(z₀) = c₀ ≠ c, so order of (G - c) at z₀ is 0 → contradiction
        subst hz_ne
        have hG_ne_c : G z₀ ≠ c := by
          intro h_eq; apply hc_eq
          have h₁ : G z₀ - c₀ = 0 := hGc₀_zero
          linear_combination h_eq.symm + h₁
        have h_congr : (fun w => g w - c) =ᶠ[nhdsWithin z₀ {z₀}ᶜ] (fun w => G w - c) := by
          filter_upwards [hG_agree] with w hw
          exact congr_arg (· - c) hw
        rw [meromorphicOrderAt_congr h_congr] at hord_ne0
        exact absurd (meromorphicOrderAt_analytic_sub_const_eq_zero'
          (hG_ana_ball (h_in_ana z₀ hz)) hG_ne_c) hord_ne0
      · -- z ≠ z₀: if G(z) ≠ c then order = 0, contradiction; so G(z) = c, hence z ∈ PF
        have h_congr : (fun w => g w - c) =ᶠ[nhdsWithin z {z}ᶜ] (fun w => G w - c) :=
          ((g_eq_G_near z hz hz_ne).mono fun w hw => by
            show g w - c = G w - c; rw [hw]).filter_mono nhdsWithin_le_nhds
        rw [meromorphicOrderAt_congr h_congr] at hord_ne0 hord_ne_top
        by_contra h_notin
        have hGz_ne_c : G z ≠ c := by
          intro hGz_eq; apply h_notin
          rw [Set.Finite.mem_toFinset]
          exact ⟨hz, show G z - c₀ = c - c₀ by linear_combination hGz_eq⟩
        exact hord_ne0 (meromorphicOrderAt_analytic_sub_const_eq_zero'
          (hG_ana_ball (h_in_ana z hz)) hGz_ne_c)
    · -- Sum = k: each z ∈ PF contributes order 1 for g - c
      have hPF_g_order :
          ∀ z ∈ PF, (meromorphicOrderAt (fun w => g w - c) z).getD 0 = 1 := by
        intro z hz_mem
        have hz_P : z ∈ P := hP_fin.mem_toFinset.mp hz_mem
        have hz_ball := hz_P.1
        have hz_ne : z ≠ z₀ := by
          intro heq; subst heq; exact hz₀_notin hz_mem
        have h_congr : (fun w => g w - c) =ᶠ[nhdsWithin z {z}ᶜ] (fun w => G w - c) :=
          ((g_eq_G_near z hz_ball hz_ne).mono fun w hw => by
            show g w - c = G w - c; rw [hw]).filter_mono nhdsWithin_le_nhds
        rw [meromorphicOrderAt_congr h_congr, hPF_order z hz_mem]; rfl
      rw [show (k : ℤ) = PF.sum (fun _ => (1 : ℤ)) from by simp [hPF_card]]
      exact Finset.sum_congr rfl hPF_g_order

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
  rw [IsLocallyConstant.iff_eventually_eq]
  intro c₀
  rw [Metric.eventually_nhds_iff]
  letI := CRS.toRiemannSurface.topology
  letI := CRS.toRiemannSurface.chartedSpace
  haveI := CRS.toRiemannSurface.isManifold
  haveI := CRS.toRiemannSurface.t2
  haveI : CompactSpace CRS.toRiemannSurface.carrier := CRS.compact
  -- === Step 1: Support set K₀ of f - c₀ ===
  have hsupp_fin := chartOrderSupport_sub_const_finite CRS f c₀ hf
  set K₀ := hsupp_fin.toFinset
  -- Handle empty K₀
  by_cases hK₀_empty : K₀ = ∅
  · -- Empty support: chartOrderSum(f-c₀) = sum over ∅ = 0
    -- All orders are 0 or ⊤ for f-c₀.
    -- By compactness (the whole surface is compact with no support), get ε for no support.
    -- First: no poles (at a pole, chartOrderAt(f-c₀) = chartOrderAt(f) < 0 ≠ 0 and ≠ ⊤,
    -- so q would be in K₀ = ∅, contradiction)
    have hK₀_nonneg : ∀ q,
        (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f q := by
      intro q
      by_contra h_neg; push_neg at h_neg
      have h_eq := chartOrderAt_sub_const_at_pole c₀ h_neg
      have hq_supp : q ∈ K₀ := by
        rw [Set.Finite.mem_toFinset]; constructor
        · rw [h_eq]; exact ne_of_lt h_neg
        · rw [h_eq]; exact hne_top q
      rw [hK₀_empty] at hq_supp; simp at hq_supp
    -- Case split: either f ≡ c₀ (all orders ⊤) or some order of f-c₀ is ≠ ⊤
    by_cases h_all_top : ∀ q, chartOrderAt (RS := CRS.toRiemannSurface)
        (fun x => f x - c₀) q = ⊤
    · -- f ≡ c₀ locally everywhere: for any c, chartRep(f,q) = c₀ near chartPt q
      -- so chartRep(f-c,q) = c₀-c. If c=c₀ order=⊤, if c≠c₀ order=0. Support always empty.
      refine ⟨1, one_pos, fun c hc => ?_⟩
      simp only [chartOrderSum]
      have hsupp_c₀_empty : hsupp_fin.toFinset = ∅ := hK₀_empty
      have hsupp_c_empty : (chartOrderSupport_sub_const_finite CRS f c hf).toFinset = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro q hq; rw [Set.Finite.mem_toFinset] at hq
        obtain ⟨hq_ne_zero, hq_ne_top⟩ := hq
        -- From h_all_top: chartRep(f,q) - c₀ ≡ 0 near chartPt q
        have h_top_q : meromorphicOrderAt
            (fun z => chartRep (RS := CRS.toRiemannSurface) f q z - c₀)
            (chartPt (RS := CRS.toRiemannSurface) q) = ⊤ := by
          have := h_all_top q; simp only [chartOrderAt, chartRep_sub_const] at this
          exact this
        have h_ev := meromorphicOrderAt_eq_top_iff.mp h_top_q
        -- chartRep f q z = c₀ eventually, so chartRep(f-c, q) = c₀-c eventually
        have h_ev_c : (fun z => chartRep (RS := CRS.toRiemannSurface) f q z - c)
            =ᶠ[nhdsWithin (chartPt (RS := CRS.toRiemannSurface) q)
              {chartPt (RS := CRS.toRiemannSurface) q}ᶜ]
            (fun _ => c₀ - c) := by
          filter_upwards [h_ev] with z hz
          rw [show chartRep (RS := CRS.toRiemannSurface) f q z = c₀ from sub_eq_zero.mp hz]
        -- Transfer to chartOrderAt level
        have h_order_eq : chartOrderAt (RS := CRS.toRiemannSurface)
            (fun x => f x - c) q =
            meromorphicOrderAt (fun _ => c₀ - c)
              (chartPt (RS := CRS.toRiemannSurface) q) := by
          simp only [chartOrderAt, chartRep_sub_const]
          exact meromorphicOrderAt_congr h_ev_c
        rw [h_order_eq] at hq_ne_zero hq_ne_top
        by_cases hc_eq : c = c₀
        · subst hc_eq; simp only [sub_self] at hq_ne_top
          exact hq_ne_top (meromorphicOrderAt_eq_top_iff.mpr
            (Filter.Eventually.of_forall fun _ => rfl))
        · have hne : (fun _ : ℂ => c₀ - c)
              (chartPt (RS := CRS.toRiemannSurface) q) ≠ 0 :=
            sub_ne_zero.mpr fun h => hc_eq h.symm
          have ha : AnalyticAt ℂ (fun _ => c₀ - c)
              (chartPt (RS := CRS.toRiemannSurface) q) := analyticAt_const
          rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr hne] at hq_ne_zero
          exact hq_ne_zero rfl
      rw [hsupp_c_empty, hsupp_c₀_empty, Finset.sum_empty, Finset.sum_empty]
    · -- Not all orders ⊤: by identity principle, ALL orders ≠ ⊤. With K₀ = ∅: all = 0.
      push_neg at h_all_top; obtain ⟨q₀, hq₀⟩ := h_all_top
      have hK₀_all_zero : ∀ q,
          chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c₀) q = 0 := by
        intro q; by_contra h_ne
        have h_ne_top := chartOrderAt_ne_top_of_ne_top_somewhere _
          (chartMeromorphic_sub_const c₀ hf) q₀ hq₀ q
        have hq_supp : q ∈ K₀ := by
          rw [Set.Finite.mem_toFinset]; exact ⟨h_ne, h_ne_top⟩
        rw [hK₀_empty] at hq_supp; simp at hq_supp
      obtain ⟨ε, hε_pos, hε_bound⟩ :=
        no_support_on_compact_near_c₀ CRS f hf hne_top c₀ Set.univ
          isCompact_univ (fun q _ => hK₀_nonneg q) (fun q _ => hK₀_all_zero q)
      refine ⟨ε, hε_pos, fun c hc => ?_⟩
      simp only [chartOrderSum]
      have hsupp_c_empty : (chartOrderSupport_sub_const_finite CRS f c hf).toFinset = ∅ :=
        Finset.eq_empty_iff_forall_notMem.mpr (fun q hq => by
          rw [Set.Finite.mem_toFinset] at hq
          exact hq.1 (hε_bound c (by rwa [dist_eq_norm] at hc) q (Set.mem_univ _)))
      have hsupp_c₀_empty : hsupp_fin.toFinset = ∅ := hK₀_empty
      rw [hsupp_c_empty, hsupp_c₀_empty, Finset.sum_empty, Finset.sum_empty]
  -- === K₀ nonempty ===
  have hK₀_ne : K₀.Nonempty := Finset.nonempty_iff_ne_empty.mpr hK₀_empty
  -- === Step 2: T2 separation ===
  obtain ⟨W, hW_prop, hW_disj⟩ := hsupp_fin.t2_separation
  -- No point has chartOrderAt(f-c₀) = ⊤ when K₀ is nonempty
  -- (would require f ≡ c₀ by identity theorem, contradicting K₀ nonempty)
  have h_no_top_at : ∀ r,
      chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c₀) r ≠ ⊤ := by
    obtain ⟨q₀, hq₀⟩ := hK₀_ne
    exact fun r => chartOrderAt_ne_top_of_ne_top_somewhere _
      (chartMeromorphic_sub_const c₀ hf) q₀ (hsupp_fin.mem_toFinset.mp hq₀).2 r
  -- Subtracting constant preserves nonneg order
  have h_nonneg_sub : ∀ q, (0 : WithTop ℤ) ≤
      chartOrderAt (RS := CRS.toRiemannSurface) f q →
      (0 : WithTop ℤ) ≤
        chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c₀) q := by
    intro q hord
    obtain ⟨G, hG_ana, hG_agree, _⟩ :=
      exists_analyticExtension_of_nonneg_order (hf q) (hne_top q) hord
    have h_congr : (fun z => chartRep (RS := CRS.toRiemannSurface) f q z - c₀)
        =ᶠ[nhdsWithin (chartPt (RS := CRS.toRiemannSurface) q)
          {chartPt (RS := CRS.toRiemannSurface) q}ᶜ]
        (fun z => G z - c₀) := by
      filter_upwards [hG_agree] with z hz
      exact congr_arg (· - c₀) hz
    simp only [chartOrderAt, chartRep_sub_const]
    rw [meromorphicOrderAt_congr h_congr]
    have hGc₀_ana : AnalyticAt ℂ (fun z => G z - c₀)
        (chartPt (RS := CRS.toRiemannSurface) q) :=
      hG_ana.sub analyticAt_const
    rw [hGc₀_ana.meromorphicOrderAt_eq]
    cases analyticOrderAt (fun z => G z - c₀)
        (chartPt (RS := CRS.toRiemannSurface) q) with
    | top => exact le_top
    | coe n =>
      show (0 : WithTop ℤ) ≤ (↑(n : ℤ) : WithTop ℤ)
      exact_mod_cast Nat.zero_le n
  -- === Step 3: For each q ∈ K₀, get chart ball data ===
  -- Use ∀ q (not ∀ q ∈ K₀) so choose gives non-dependent functions
  have h_local_data : ∀ q : CRS.toRiemannSurface.carrier, ∃ (rq' εq' : ℝ),
      q ∈ K₀ → 0 < rq' ∧ 0 < εq' ∧
      (∀ z, ‖z - chartPt (RS := CRS.toRiemannSurface) q‖ < rq' →
        z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target ∧
        (extChartAt 𝓘(ℂ, ℂ) q).symm z ∈ W q) ∧
      (∀ c : ℂ, ‖c - c₀‖ < εq' → ∃ S : Finset ℂ,
        (∀ z ∈ S, ‖z - chartPt (RS := CRS.toRiemannSurface) q‖ < rq') ∧
        (∀ z, ‖z - chartPt (RS := CRS.toRiemannSurface) q‖ < rq' →
          meromorphicOrderAt (fun w =>
            chartRep (RS := CRS.toRiemannSurface) f q w - c) z ≠ 0 →
          meromorphicOrderAt (fun w =>
            chartRep (RS := CRS.toRiemannSurface) f q w - c) z ≠ ⊤ →
          z ∈ S) ∧
        S.sum (fun z => (meromorphicOrderAt
          (fun w => chartRep (RS := CRS.toRiemannSurface) f q w - c) z).getD 0) =
          (chartOrderAt (RS := CRS.toRiemannSurface)
            (fun x => f x - c₀) q).getD 0) := by
    intro q
    by_cases hq : q ∈ K₀
    · have hq_supp := hsupp_fin.mem_toFinset.mp hq
      have h_nhds : (extChartAt 𝓘(ℂ, ℂ) q).target ∩
          (extChartAt 𝓘(ℂ, ℂ) q).symm ⁻¹' (W q) ∈
          nhds (chartPt (RS := CRS.toRiemannSurface) q) :=
        Filter.inter_mem
          ((isOpen_extChartAt_target (I := 𝓘(ℂ, ℂ)) q).mem_nhds
            (mem_extChartAt_target (I := 𝓘(ℂ, ℂ)) q))
          ((continuousAt_extChartAt_symm''
            (mem_extChartAt_target (I := 𝓘(ℂ, ℂ)) q)).preimage_mem_nhds
            ((hW_prop q).2.mem_nhds (by
              rw [(extChartAt 𝓘(ℂ, ℂ) q).left_inv
                (mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) q)]
              exact (hW_prop q).1)))
      obtain ⟨ρ, hρ, hρ_sub⟩ := Metric.eventually_nhds_iff.mp h_nhds
      by_cases h_neg : chartOrderAt (RS := CRS.toRiemannSurface) f q < 0
      · -- Pole case: use pole_local_chart_sum_constant
        obtain ⟨r, hr, hr_le, ε, hε, hS⟩ :=
          pole_local_chart_sum_constant c₀ hf h_neg hρ
        exact ⟨r, ε, fun _ => ⟨hr, hε,
          fun z hz => hρ_sub (show dist z
            (chartPt (RS := CRS.toRiemannSurface) q) < ρ by
              rw [dist_eq_norm]; linarith [hr_le]),
          hS⟩⟩
      · -- Zero case: use zero_local_chart_sum_constant
        push_neg at h_neg
        have hzero : (0 : WithTop ℤ) <
            chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c₀) q :=
          lt_of_le_of_ne (h_nonneg_sub q h_neg) (Ne.symm hq_supp.1)
        obtain ⟨r, hr, hr_le, ε, hε, hS⟩ :=
          zero_local_chart_sum_constant c₀ hf (hne_top q) h_neg hzero
            (h_no_top_at q) hρ
        exact ⟨r, ε, fun _ => ⟨hr, hε,
          fun z hz => hρ_sub (show dist z
            (chartPt (RS := CRS.toRiemannSurface) q) < ρ by
              rw [dist_eq_norm]; linarith [hr_le]),
          hS⟩⟩
    · exact ⟨1, 1, fun h => absurd h hq⟩
  choose rq εq h_combined using h_local_data
  have hrq : ∀ q ∈ K₀, 0 < rq q := fun q hq => (h_combined q hq).1
  have hεq : ∀ q ∈ K₀, 0 < εq q := fun q hq => (h_combined q hq).2.1
  have h_ball : ∀ q ∈ K₀, ∀ z,
      ‖z - chartPt (RS := CRS.toRiemannSurface) q‖ < rq q →
      z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target ∧
      (extChartAt 𝓘(ℂ, ℂ) q).symm z ∈ W q :=
    fun q hq => (h_combined q hq).2.2.1
  have h_local : ∀ q ∈ K₀, ∀ c : ℂ, ‖c - c₀‖ < εq q → ∃ S : Finset ℂ,
      (∀ z ∈ S, ‖z - chartPt (RS := CRS.toRiemannSurface) q‖ < rq q) ∧
      (∀ z, ‖z - chartPt (RS := CRS.toRiemannSurface) q‖ < rq q →
        meromorphicOrderAt (fun w =>
          chartRep (RS := CRS.toRiemannSurface) f q w - c) z ≠ 0 →
        meromorphicOrderAt (fun w =>
          chartRep (RS := CRS.toRiemannSurface) f q w - c) z ≠ ⊤ →
        z ∈ S) ∧
      S.sum (fun z => (meromorphicOrderAt
        (fun w => chartRep (RS := CRS.toRiemannSurface) f q w - c) z).getD 0) =
        (chartOrderAt (RS := CRS.toRiemannSurface)
          (fun x => f x - c₀) q).getD 0 :=
    fun q hq => (h_combined q hq).2.2.2
  -- === Step 4: Open chart balls in the manifold ===
  set Vq : CRS.toRiemannSurface.carrier → Set CRS.toRiemannSurface.carrier :=
    fun q' => (extChartAt 𝓘(ℂ, ℂ) q').source ∩
      (extChartAt 𝓘(ℂ, ℂ) q') ⁻¹' Metric.ball
        (chartPt (RS := CRS.toRiemannSurface) q') (rq q')
  have hVq_open : ∀ q', @IsOpen _ CRS.toRiemannSurface.topology (Vq q') := by
    intro q'
    rw [isOpen_iff_mem_nhds]
    intro r ⟨hr_src, hr_ball⟩
    exact Filter.inter_mem
      ((isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) q').mem_nhds hr_src)
      (((chartAt ℂ q').continuousAt
        (by rw [← extChartAt_source (I := 𝓘(ℂ, ℂ))]; exact hr_src)).preimage_mem_nhds
        (Metric.isOpen_ball.mem_nhds hr_ball))
  have hq_Vq : ∀ q' ∈ K₀, q' ∈ Vq q' := by
    intro q' hq'
    exact ⟨mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) q',
      Metric.mem_ball_self (hrq q' hq')⟩
  -- === Step 5: Compact complement ===
  set K := (⋃ q' ∈ K₀, Vq q')ᶜ
  have hK_compact : @IsCompact _ CRS.toRiemannSurface.topology K :=
    (isOpen_biUnion fun q' _ => hVq_open q').isClosed_compl.isCompact
  have hK_no_pole : ∀ r ∈ K, (0 : WithTop ℤ) ≤
      chartOrderAt (RS := CRS.toRiemannSurface) f r := by
    intro r hr
    by_contra h_neg; push_neg at h_neg
    have hr_supp : r ∈ K₀ := by
      rw [Set.Finite.mem_toFinset]; constructor
      · rw [chartOrderAt_sub_const_at_pole c₀ h_neg]; exact ne_of_lt h_neg
      · rw [chartOrderAt_sub_const_at_pole c₀ h_neg]; exact hne_top r
    exact hr (Set.mem_iUnion₂.mpr ⟨r, hr_supp, hq_Vq r hr_supp⟩)
  have hK_all_zero : ∀ r ∈ K,
      chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c₀) r = 0 := by
    intro r hr
    by_contra h_ne
    have h_ne_top := h_no_top_at r
    have hr_supp : r ∈ K₀ := hsupp_fin.mem_toFinset.mpr ⟨h_ne, h_ne_top⟩
    exact hr (Set.mem_iUnion₂.mpr ⟨r, hr_supp, hq_Vq r hr_supp⟩)
  obtain ⟨ε_K, hε_K, hε_K_bound⟩ :=
    no_support_on_compact_near_c₀ CRS f hf hne_top c₀ K hK_compact hK_no_pole hK_all_zero
  -- === Step 6: Choose ε ===
  have hε_inf_pos : 0 < K₀.inf' hK₀_ne εq :=
    Finset.inf'_induction hK₀_ne εq
      (fun _ h₁ _ h₂ => lt_min h₁ h₂) (fun q hq => hεq q hq)
  refine ⟨min ε_K (K₀.inf' hK₀_ne εq), lt_min hε_K hε_inf_pos, fun c hc => ?_⟩
  rw [dist_eq_norm] at hc
  have hc_K : ‖c - c₀‖ < ε_K := lt_of_lt_of_le hc (min_le_left _ _)
  have hc_q : ∀ q' ∈ K₀, ‖c - c₀‖ < εq q' := by
    intro q' hq'
    calc ‖c - c₀‖ < min ε_K (K₀.inf' hK₀_ne εq) := hc
      _ ≤ K₀.inf' hK₀_ne εq := min_le_right _ _
      _ ≤ εq q' := Finset.inf'_le εq hq'
  -- === Step 7: For fixed c, get Sq and Tq ===
  have h_Sq : ∀ q' : CRS.toRiemannSurface.carrier, ∃ S : Finset ℂ,
      q' ∈ K₀ →
      (∀ z ∈ S, ‖z - chartPt (RS := CRS.toRiemannSurface) q'‖ < rq q') ∧
      (∀ z, ‖z - chartPt (RS := CRS.toRiemannSurface) q'‖ < rq q' →
        meromorphicOrderAt (fun w =>
          chartRep (RS := CRS.toRiemannSurface) f q' w - c) z ≠ 0 →
        meromorphicOrderAt (fun w =>
          chartRep (RS := CRS.toRiemannSurface) f q' w - c) z ≠ ⊤ →
        z ∈ S) ∧
      S.sum (fun z => (meromorphicOrderAt (fun w =>
        chartRep (RS := CRS.toRiemannSurface) f q' w - c) z).getD 0) =
        (chartOrderAt (RS := CRS.toRiemannSurface)
          (fun x => f x - c₀) q').getD 0 := by
    intro q'
    by_cases hq' : q' ∈ K₀
    · obtain ⟨S, hS⟩ := h_local q' hq' c (hc_q q' hq')
      exact ⟨S, fun _ => hS⟩
    · exact ⟨∅, fun h => absurd h hq'⟩
  choose Sq h_Sq_data using h_Sq
  set Tq : CRS.toRiemannSurface.carrier →
      Finset CRS.toRiemannSurface.carrier :=
    fun q' => (Sq q').image (extChartAt 𝓘(ℂ, ℂ) q').symm
  -- === Step 8: Each Tq sum = chartOrderAt(f-c₀, q).getD 0 ===
  have hTq_sum : ∀ q' ∈ K₀, (Tq q').sum (fun r =>
      (chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) r).getD 0) =
      (chartOrderAt (RS := CRS.toRiemannSurface)
        (fun x => f x - c₀) q').getD 0 := by
    intro q' hq'
    have h_inj : Set.InjOn (extChartAt 𝓘(ℂ, ℂ) q').symm ↑(Sq q') := by
      apply (extChartAt 𝓘(ℂ, ℂ) q').symm.injOn.mono
      intro z hz
      rw [PartialEquiv.symm_source]
      exact (h_ball q' hq' z ((h_Sq_data q' hq').1 z (Finset.mem_coe.mp hz))).1
    rw [show Tq q' = (Sq q').image _ from rfl, Finset.sum_image h_inj]
    have h_translate : ∀ z ∈ Sq q',
        (chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c)
          ((extChartAt 𝓘(ℂ, ℂ) q').symm z)).getD 0 =
        (meromorphicOrderAt (fun w =>
          chartRep (RS := CRS.toRiemannSurface) f q' w - c) z).getD 0 := by
      intro z hz
      have hz_tgt : z ∈ (extChartAt 𝓘(ℂ, ℂ) q').target :=
        (h_ball q' hq' z ((h_Sq_data q' hq').1 z hz)).1
      have hz_src : (extChartAt 𝓘(ℂ, ℂ) q').symm z ∈
          (extChartAt 𝓘(ℂ, ℂ) q').source :=
        (extChartAt 𝓘(ℂ, ℂ) q').map_target hz_tgt
      congr 1
      rw [chartOrderAt_eq_in_chart _ q' _
          (chartMeromorphic_sub_const c hf) hz_src,
        chartRep_sub_const]
      congr 1
      exact (extChartAt 𝓘(ℂ, ℂ) q').right_inv hz_tgt
    rw [Finset.sum_congr rfl h_translate]
    exact (h_Sq_data q' hq').2.2
  -- === Step 9: support(f-c) ⊆ K₀.biUnion Tq ===
  have h_support_sub :
      (chartOrderSupport_sub_const_finite CRS f c hf).toFinset ⊆
      K₀.biUnion Tq := by
    intro r hr
    rw [Set.Finite.mem_toFinset] at hr
    obtain ⟨hr_ne_zero, hr_ne_top⟩ := hr
    have hr_not_K : r ∉ K := by
      intro hr_K
      exact hr_ne_zero (hε_K_bound c hc_K r hr_K)
    rw [Set.mem_compl_iff, not_not] at hr_not_K
    obtain ⟨q', hq'_K₀, hr_Vq⟩ := Set.mem_iUnion₂.mp hr_not_K
    obtain ⟨hr_src, hr_ball⟩ := hr_Vq
    have hr_in_ball : ‖(extChartAt 𝓘(ℂ, ℂ) q') r -
        chartPt (RS := CRS.toRiemannSurface) q'‖ < rq q' := by
      rwa [← dist_eq_norm, ← Metric.mem_ball]
    have hr_order_chart :
        chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) r =
        meromorphicOrderAt (fun w =>
          chartRep (RS := CRS.toRiemannSurface) f q' w - c)
          ((extChartAt 𝓘(ℂ, ℂ) q') r) := by
      rw [chartOrderAt_eq_in_chart _ q' r
          (chartMeromorphic_sub_const c hf) hr_src,
        chartRep_sub_const]
    have hr_in_Sq : (extChartAt 𝓘(ℂ, ℂ) q') r ∈ Sq q' :=
      (h_Sq_data q' hq'_K₀).2.1 _ hr_in_ball
        (by rwa [← hr_order_chart]) (by rwa [← hr_order_chart])
    rw [Finset.mem_biUnion]
    exact ⟨q', hq'_K₀, Finset.mem_image.mpr
      ⟨(extChartAt 𝓘(ℂ, ℂ) q') r, hr_in_Sq,
        (extChartAt 𝓘(ℂ, ℂ) q').left_inv hr_src⟩⟩
  -- === Step 10: Tq pairwise disjoint ===
  have hTq_disj : Set.PairwiseDisjoint (↑K₀) Tq := by
    intro q₁ hq₁ q₂ hq₂ hne
    show Disjoint (Tq q₁) (Tq q₂)
    rw [Finset.disjoint_left]
    intro r hr₁ hr₂
    have hr_W₁ : r ∈ W q₁ := by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hr₁
      exact (h_ball q₁ hq₁ z ((h_Sq_data q₁ hq₁).1 z hz)).2
    have hr_W₂ : r ∈ W q₂ := by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hr₂
      exact (h_ball q₂ hq₂ z ((h_Sq_data q₂ hq₂).1 z hz)).2
    exact Set.disjoint_left.mp
      (hW_disj (hsupp_fin.mem_toFinset.mp hq₁)
        (hsupp_fin.mem_toFinset.mp hq₂) hne) hr_W₁ hr_W₂
  -- === Step 11: Final sum computation ===
  simp only [chartOrderSum]
  have h_extra_zero : ∀ r ∈ K₀.biUnion Tq,
      r ∉ (chartOrderSupport_sub_const_finite CRS f c hf).toFinset →
      (chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) r).getD 0 = 0 := by
    intro r _ hr_notin
    simp only [Set.Finite.mem_toFinset, chartOrderSupport, Set.mem_setOf_eq,
      not_and_or, not_not] at hr_notin
    rcases hr_notin with h | h <;> rw [h] <;> rfl
  rw [Finset.sum_subset h_support_sub h_extra_zero,
    Finset.sum_biUnion hTq_disj]
  exact Finset.sum_congr rfl fun q' hq' => hTq_sum q' hq'

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
  letI := CRS.toRiemannSurface.topology
  letI := CRS.toRiemannSurface.chartedSpace
  haveI := CRS.toRiemannSurface.isManifold
  haveI := CRS.toRiemannSurface.t2
  haveI : CompactSpace CRS.toRiemannSurface.carrier := CRS.compact
  -- Case split: has pole or not
  by_cases h_has_pole : ∃ q, chartOrderAt (RS := CRS.toRiemannSurface) f q < 0
  · -- Case 1: f has at least one pole — degree theory via LMT
    obtain ⟨q₀, hq₀_pole⟩ := h_has_pole
    have hsupp_fin := chartOrderSupport_finite_general CRS f hf ⟨q₀, hne_top q₀⟩
    -- === Step 1: Pole set and finiteness ===
    have hpoles_fin : {p : CRS.toRiemannSurface.carrier |
        chartOrderAt (RS := CRS.toRiemannSurface) f p < 0}.Finite :=
      hsupp_fin.subset fun p hp => ⟨ne_of_lt hp, hne_top p⟩
    set PF := hpoles_fin.toFinset
    have hPF_pole : ∀ p ∈ PF, chartOrderAt (RS := CRS.toRiemannSurface) f p < 0 :=
      fun p hp => hpoles_fin.mem_toFinset.mp hp
    have hPF_ne : PF.Nonempty := ⟨q₀, hpoles_fin.mem_toFinset.mpr hq₀_pole⟩
    -- === Step 2: T2-disjoint open neighborhoods ===
    obtain ⟨W, hW_prop, hW_disj⟩ := hpoles_fin.t2_separation
    -- === Step 3: For each pole, chart ball + local sum data ===
    -- Use ∀ p (not ∀ p ∈ PF) so choose gives non-dependent functions
    have h_pole_data : ∀ p : CRS.toRiemannSurface.carrier, ∃ (rp Cp : ℝ),
        p ∈ PF → 0 < rp ∧ 0 < Cp ∧
        (∀ z, ‖z - chartPt (RS := CRS.toRiemannSurface) p‖ < rp →
          z ∈ (extChartAt 𝓘(ℂ, ℂ) p).target ∧
          (extChartAt 𝓘(ℂ, ℂ) p).symm z ∈ W p) ∧
        (∀ c : ℂ, Cp < ‖c‖ → ∃ S : Finset ℂ,
          (∀ z ∈ S, ‖z - chartPt (RS := CRS.toRiemannSurface) p‖ < rp) ∧
          (∀ z, ‖z - chartPt (RS := CRS.toRiemannSurface) p‖ < rp →
            meromorphicOrderAt (fun w => chartRep (RS := CRS.toRiemannSurface) f p w - c) z ≠ 0 →
            meromorphicOrderAt (fun w => chartRep (RS := CRS.toRiemannSurface) f p w - c) z ≠ ⊤ →
            z ∈ S) ∧
          S.sum (fun z => (meromorphicOrderAt
            (fun w => chartRep (RS := CRS.toRiemannSurface) f p w - c) z).getD 0) = 0) := by
      intro p
      by_cases hp : p ∈ PF
      · have h_symm : (extChartAt 𝓘(ℂ, ℂ) p).symm
            (chartPt (RS := CRS.toRiemannSurface) p) = p :=
          (extChartAt 𝓘(ℂ, ℂ) p).left_inv (mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) p)
        have h_nhds : (extChartAt 𝓘(ℂ, ℂ) p).target ∩
            (extChartAt 𝓘(ℂ, ℂ) p).symm ⁻¹' (W p) ∈
            nhds (chartPt (RS := CRS.toRiemannSurface) p) :=
          Filter.inter_mem
            ((isOpen_extChartAt_target (I := 𝓘(ℂ, ℂ)) p).mem_nhds
              (mem_extChartAt_target (I := 𝓘(ℂ, ℂ)) p))
            ((continuousAt_extChartAt_symm''
              (mem_extChartAt_target (I := 𝓘(ℂ, ℂ)) p)).preimage_mem_nhds
              ((hW_prop p).2.mem_nhds (by
                rw [(extChartAt 𝓘(ℂ, ℂ) p).left_inv
                  (mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) p)]
                exact (hW_prop p).1)))
        obtain ⟨ρ, hρ, hρ_sub⟩ := Metric.eventually_nhds_iff.mp h_nhds
        obtain ⟨r, hr_pos, hr_le, Cp, hCp, hS⟩ :=
          meromorphic_pole_local_sum_zero (hf p) (hPF_pole p hp) hρ
        exact ⟨r, Cp, fun _ => ⟨hr_pos, hCp,
          fun z hz => hρ_sub (show dist z (chartPt (RS := CRS.toRiemannSurface) p) < ρ by
            rw [dist_eq_norm]; linarith [hr_le]), hS⟩⟩
      · exact ⟨1, 1, fun h => absurd h hp⟩
    choose rp Cp h_combined using h_pole_data
    -- Convenience accessors
    have hrp : ∀ p ∈ PF, 0 < rp p := fun p hp => (h_combined p hp).1
    have hCp : ∀ p ∈ PF, 0 < Cp p := fun p hp => (h_combined p hp).2.1
    have h_ball : ∀ p ∈ PF, ∀ z, ‖z - chartPt (RS := CRS.toRiemannSurface) p‖ < rp p →
        z ∈ (extChartAt 𝓘(ℂ, ℂ) p).target ∧
        (extChartAt 𝓘(ℂ, ℂ) p).symm z ∈ W p :=
      fun p hp => (h_combined p hp).2.2.1
    have h_local : ∀ p ∈ PF, ∀ c : ℂ, Cp p < ‖c‖ → ∃ S : Finset ℂ,
        (∀ z ∈ S, ‖z - chartPt (RS := CRS.toRiemannSurface) p‖ < rp p) ∧
        (∀ z, ‖z - chartPt (RS := CRS.toRiemannSurface) p‖ < rp p →
          meromorphicOrderAt (fun w => chartRep (RS := CRS.toRiemannSurface) f p w - c) z ≠ 0 →
          meromorphicOrderAt (fun w => chartRep (RS := CRS.toRiemannSurface) f p w - c) z ≠ ⊤ →
          z ∈ S) ∧
        S.sum (fun z => (meromorphicOrderAt
          (fun w => chartRep (RS := CRS.toRiemannSurface) f p w - c) z).getD 0) = 0 :=
      fun p hp => (h_combined p hp).2.2.2
    -- === Step 4: Open chart balls in the manifold ===
    set Vp : CRS.toRiemannSurface.carrier → Set CRS.toRiemannSurface.carrier :=
      fun p => (extChartAt 𝓘(ℂ, ℂ) p).source ∩
        (extChartAt 𝓘(ℂ, ℂ) p) ⁻¹' Metric.ball
          (chartPt (RS := CRS.toRiemannSurface) p) (rp p)
    have hVp_open : ∀ p, @IsOpen _ CRS.toRiemannSurface.topology (Vp p) := by
      intro p
      rw [isOpen_iff_mem_nhds]
      intro q ⟨hq_src, hq_ball⟩
      exact Filter.inter_mem
        ((isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) p).mem_nhds hq_src)
        (((chartAt ℂ p).continuousAt
          (by rw [← extChartAt_source (I := 𝓘(ℂ, ℂ))]; exact hq_src)).preimage_mem_nhds
          (Metric.isOpen_ball.mem_nhds hq_ball))
    have hp_Vp : ∀ p ∈ PF, p ∈ Vp p := by
      intro p hp
      exact ⟨mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) p,
        Metric.mem_ball_self (hrp p hp)⟩
    -- === Step 5: Compact complement with no poles ===
    set K := (⋃ p ∈ PF, Vp p)ᶜ
    have hK_compact : @IsCompact _ CRS.toRiemannSurface.topology K :=
      (isOpen_biUnion fun p _ => hVp_open p).isClosed_compl.isCompact
    have hK_no_pole : ∀ q ∈ K, (0 : WithTop ℤ) ≤
        chartOrderAt (RS := CRS.toRiemannSurface) f q := by
      intro q hq
      by_contra h_neg; push_neg at h_neg
      have hq_PF : q ∈ PF := hpoles_fin.mem_toFinset.mpr h_neg
      exact hq (Set.mem_iUnion₂.mpr ⟨q, hq_PF, hp_Vp q hq_PF⟩)
    obtain ⟨CK, hCK_pos, hCK_bound⟩ :=
      no_support_on_compact_away_from_poles CRS f hf hne_top K hK_compact hK_no_pole
    -- === Step 6: Choose c₀ ===
    set C_all := max CK (PF.sup' hPF_ne Cp) + 1
    have hC_all_pos : 0 < C_all := by linarith [le_max_left CK (PF.sup' hPF_ne Cp)]
    use ↑C_all  -- embed ℝ → ℂ
    have hc₀_norm : ‖(↑C_all : ℂ)‖ = C_all := by
      simp [abs_of_pos hC_all_pos]
    have hc₀_CK : CK < ‖(↑C_all : ℂ)‖ := by
      rw [hc₀_norm]; linarith [le_max_left CK (PF.sup' hPF_ne Cp)]
    have hc₀_Cp : ∀ p ∈ PF, Cp p < ‖(↑C_all : ℂ)‖ := by
      intro p hp; rw [hc₀_norm]
      linarith [Finset.le_sup' Cp hp, le_max_right CK (PF.sup' hPF_ne Cp)]
    -- === Step 7: Get S_p for this c₀, define T_p ===
    set c₀ : ℂ := ↑C_all
    -- Use ∀ p (not ∀ p ∈ PF) for non-dependent choose
    have h_Sp : ∀ p : CRS.toRiemannSurface.carrier, ∃ S : Finset ℂ,
        p ∈ PF →
        (∀ z ∈ S, ‖z - chartPt (RS := CRS.toRiemannSurface) p‖ < rp p) ∧
        (∀ z, ‖z - chartPt (RS := CRS.toRiemannSurface) p‖ < rp p →
          meromorphicOrderAt (fun w =>
            chartRep (RS := CRS.toRiemannSurface) f p w - c₀) z ≠ 0 →
          meromorphicOrderAt (fun w =>
            chartRep (RS := CRS.toRiemannSurface) f p w - c₀) z ≠ ⊤ →
          z ∈ S) ∧
        S.sum (fun z => (meromorphicOrderAt (fun w =>
          chartRep (RS := CRS.toRiemannSurface) f p w - c₀) z).getD 0) = 0 := by
      intro p
      by_cases hp : p ∈ PF
      · obtain ⟨S, hS⟩ := h_local p hp c₀ (hc₀_Cp p hp)
        exact ⟨S, fun _ => hS⟩
      · exact ⟨∅, fun h => absurd h hp⟩
    choose Sp h_Sp_data using h_Sp
    -- Manifold-level finsets: Tp = Sp.image (eChart p).symm
    set Tp : CRS.toRiemannSurface.carrier →
        Finset CRS.toRiemannSurface.carrier :=
      fun p => (Sp p).image (extChartAt 𝓘(ℂ, ℂ) p).symm
    -- === Step 8: Each Tp.sum = 0 ===
    have hTp_sum : ∀ p ∈ PF, (Tp p).sum (fun q =>
        (chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c₀) q).getD 0) = 0 := by
      intro p hp
      -- Injectivity of symm on Sp ⊆ target
      have h_inj : Set.InjOn (extChartAt 𝓘(ℂ, ℂ) p).symm ↑(Sp p) := by
        apply (extChartAt 𝓘(ℂ, ℂ) p).symm.injOn.mono
        intro z hz
        rw [PartialEquiv.symm_source]
        exact (h_ball p hp z ((h_Sp_data p hp).1 z (Finset.mem_coe.mp hz))).1
      rw [show Tp p = (Sp p).image _ from rfl, Finset.sum_image h_inj]
      -- Translate chartOrderAt to meromorphicOrderAt
      have h_translate : ∀ z ∈ Sp p,
          (chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c₀)
            ((extChartAt 𝓘(ℂ, ℂ) p).symm z)).getD 0 =
          (meromorphicOrderAt (fun w =>
            chartRep (RS := CRS.toRiemannSurface) f p w - c₀) z).getD 0 := by
        intro z hz
        have hz_tgt : z ∈ (extChartAt 𝓘(ℂ, ℂ) p).target :=
          (h_ball p hp z ((h_Sp_data p hp).1 z hz)).1
        have hz_src : (extChartAt 𝓘(ℂ, ℂ) p).symm z ∈
            (extChartAt 𝓘(ℂ, ℂ) p).source :=
          (extChartAt 𝓘(ℂ, ℂ) p).map_target hz_tgt
        congr 1
        rw [chartOrderAt_eq_in_chart _ p _
            (chartMeromorphic_sub_const c₀ hf) hz_src,
          chartRep_sub_const]
        congr 1
        exact (extChartAt 𝓘(ℂ, ℂ) p).right_inv hz_tgt
      rw [Finset.sum_congr rfl h_translate]
      exact (h_Sp_data p hp).2.2
    -- === Step 9: Support ⊆ PF.biUnion Tp ===
    have h_support_sub :
        (chartOrderSupport_sub_const_finite CRS f c₀ hf).toFinset ⊆
        PF.biUnion Tp := by
      intro q hq
      rw [Set.Finite.mem_toFinset] at hq
      obtain ⟨hq_ne_zero, hq_ne_top⟩ := hq
      -- q ∉ K (since in K, order = 0 for large c₀)
      have hq_not_K : q ∉ K := by
        intro hq_K
        exact hq_ne_zero (hCK_bound c₀ hc₀_CK q hq_K)
      -- q ∈ ⋃ Vp → q ∈ Vp p for some p ∈ PF
      rw [Set.mem_compl_iff, not_not] at hq_not_K
      obtain ⟨p, hp_PF, hq_Vp⟩ := Set.mem_iUnion₂.mp hq_not_K
      obtain ⟨hq_src, hq_ball⟩ := hq_Vp
      -- chartOrderAt = meromorphicOrderAt in chart of p
      have hq_in_ball : ‖(extChartAt 𝓘(ℂ, ℂ) p) q -
          chartPt (RS := CRS.toRiemannSurface) p‖ < rp p := by
        rwa [← dist_eq_norm, ← Metric.mem_ball]
      have hq_order_chart :
          chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c₀) q =
          meromorphicOrderAt (fun w =>
            chartRep (RS := CRS.toRiemannSurface) f p w - c₀)
            ((extChartAt 𝓘(ℂ, ℂ) p) q) := by
        rw [chartOrderAt_eq_in_chart _ p q
            (chartMeromorphic_sub_const c₀ hf) hq_src,
          chartRep_sub_const]
      -- (eChart p) q ∈ Sp p
      have hq_in_Sp : (extChartAt 𝓘(ℂ, ℂ) p) q ∈ Sp p :=
        (h_Sp_data p hp_PF).2.1 _ hq_in_ball
          (by rwa [← hq_order_chart]) (by rwa [← hq_order_chart])
      -- q = symm ((eChart p) q) ∈ Tp p
      rw [Finset.mem_biUnion]
      exact ⟨p, hp_PF, Finset.mem_image.mpr
        ⟨(extChartAt 𝓘(ℂ, ℂ) p) q, hq_in_Sp,
          (extChartAt 𝓘(ℂ, ℂ) p).left_inv hq_src⟩⟩
    -- === Step 10: Tp pairwise disjoint ===
    have hTp_disj : Set.PairwiseDisjoint (↑PF) Tp := by
      intro p₁ hp₁ p₂ hp₂ hne
      show Disjoint (Tp p₁) (Tp p₂)
      rw [Finset.disjoint_left]
      intro q hq₁ hq₂
      -- q ∈ Tp p₁ → q ∈ W p₁
      have hq_W₁ : q ∈ W p₁ := by
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq₁
        exact (h_ball p₁ hp₁ z ((h_Sp_data p₁ hp₁).1 z hz)).2
      -- q ∈ Tp p₂ → q ∈ W p₂
      have hq_W₂ : q ∈ W p₂ := by
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq₂
        exact (h_ball p₂ hp₂ z ((h_Sp_data p₂ hp₂).1 z hz)).2
      -- W pairwise disjoint on pole set
      exact Set.disjoint_left.mp
        (hW_disj (hpoles_fin.mem_toFinset.mp hp₁)
          (hpoles_fin.mem_toFinset.mp hp₂) hne) hq_W₁ hq_W₂
    -- === Step 11: Final sum computation ===
    simp only [chartOrderSum]
    -- chartOrderSum = support.sum = (biUnion Tp).sum = ∑_p Tp.sum = ∑_p 0 = 0
    have h_extra_zero : ∀ q ∈ PF.biUnion Tp,
        q ∉ (chartOrderSupport_sub_const_finite CRS f c₀ hf).toFinset →
        (chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c₀) q).getD 0 = 0 := by
      intro q _ hq_notin
      simp only [Set.Finite.mem_toFinset, chartOrderSupport, Set.mem_setOf_eq,
        not_and_or, not_not] at hq_notin
      rcases hq_notin with h | h <;> rw [h] <;> rfl
    rw [Finset.sum_subset h_support_sub h_extra_zero,
      Finset.sum_biUnion hTp_disj]
    exact Finset.sum_eq_zero fun p hp => hTp_sum p hp
  · -- Case 2: f has no poles — all orders ≥ 0
    push_neg at h_has_pole
    -- By maximum principle: all orders = 0 (holomorphic on compact RS → constant)
    have h_all_zero := chartOrderAt_eq_zero_of_all_nonneg CRS f hf hne_top h_has_pole
    -- Take c₀ = 0: chartOrderSum(f - 0) = chartOrderSum(f) = 0 (empty support)
    use 0
    simp only [chartOrderSum]
    -- The support of (f - 0) is empty since all orders of f are 0
    -- and f - 0 has the same orders as f (by extensionality)
    have hsupp_empty : (chartOrderSupport_sub_const_finite CRS f 0 hf).toFinset = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr (fun p hp => by
        rw [Set.Finite.mem_toFinset] at hp
        have := hp.1
        rw [chartOrderAt_congr' (fun x => by ring :
          ∀ x, (fun x => f x - (0 : ℂ)) x = f x)] at this
        exact this (h_all_zero p))
    rw [hsupp_empty, Finset.sum_empty]

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
