import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.Infrastructure.MaximumPrinciple

/-!
# Poisson Integral on Discs

This file develops the Poisson integral for discs in ℂ, which is used to prove
that continuous functions satisfying the mean value property are harmonic.

## Main Results

* `mvp_maximum_principle` - Maximum principle for functions satisfying MVP
* `schwarzIntegral` - The Schwarz integral (holomorphic, Re = Poisson integral)
* `mvp_eq_poissonIntegral` - MVP function equals its Poisson integral
* `mvp_implies_harmonicOnNhd` - MVP implies harmonicity

## Strategy

Given f continuous on closedBall c R satisfying MVP on ball c R:
1. Define the Schwarz integral H(z) = Poisson-type integral of f
2. H is holomorphic on ball c R (parametric integral with holomorphic integrand)
3. P[f] = Re(H) is harmonic, hence satisfies MVP
4. f - P[f] satisfies MVP and vanishes on the boundary
5. By maximum principle for MVP functions: f = P[f]
6. Therefore f = Re(holomorphic), hence f is harmonic

## References

* Axler, Bourdon, Ramey "Harmonic Function Theory" Ch 1
* Ahlfors "Complex Analysis" Ch 6
-/

namespace RiemannSurfaces.Analytic.Infrastructure

open Complex Metric Set Filter MeasureTheory InnerProductSpace Real Topology

/-!
## Maximum Principle for MVP Functions

The maximum principle holds for continuous functions satisfying the mean value property,
without assuming they are harmonic. The proof is identical to the harmonic case:
if f attains its maximum at an interior point, then MVP forces f to be constant
on any circle around that point where the maximum is attained, and by iteration
f is constant on the entire connected component.
-/

/-- If f is continuous on a closed ball, satisfies MVP, and its maximum is attained
    at a point on the sphere (boundary circle), then the maximum on the ball
    equals the maximum on the sphere.

    This is a helper for the MVP maximum principle. -/
theorem mvp_max_le_sphere_max (f : ℂ → ℝ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hcont : ContinuousOn f (closedBall c R))
    (hmvp : ∀ z ∈ ball c R, ∀ r > 0, closedBall z r ⊆ closedBall c R →
      f z = circleAverage f z r)
    (z₀ : ℂ) (hz₀ : z₀ ∈ ball c R)
    (hmax : ∀ z ∈ closedBall c R, f z ≤ f z₀) :
    ∀ z ∈ closedBall c R, f z = f z₀ := by
  -- First, show f = f(z₀) on ball c R using the clopen argument
  have hball : ∀ z ∈ ball c R, f z = f z₀ := by
    -- Define S = {z ∈ ball c R | f z = f z₀}
    let S := {z ∈ ball c R | f z = f z₀}
    -- Use connectedness: S is open, ball \ S is open, S nonempty → S = ball
    have hball_conn := (convex_ball c R).isConnected (nonempty_ball.mpr hR)
    -- S is open: if f(w) = f(z₀) and w ∈ ball, then f = f(z₀) on a neighborhood
    have hS_open : IsOpen S := by
      rw [isOpen_iff_forall_mem_open]
      intro w ⟨hw_ball, hfw⟩
      -- Take ε so that closedBall w ε ⊆ closedBall c R
      set ε := (R - dist w c) / 2 with hε_def
      have hw_dist : dist w c < R := mem_ball.mp hw_ball
      have hε_pos : 0 < ε := by linarith
      have h_sub : closedBall w ε ⊆ closedBall c R := by
        intro x hx; rw [mem_closedBall] at hx ⊢
        linarith [dist_triangle x w c]
      -- For each x ∈ ball w ε with x ≠ w, x ∈ sphere w (dist x w)
      -- By MVP at w: f(w) = circleAvg(f, w, dist x w)
      -- By eq_of_circleAverage_eq_of_le: f = f(z₀) on sphere w (dist x w)
      refine ⟨ball w ε, ?_, isOpen_ball, mem_ball_self hε_pos⟩
      intro x hx
      have hx_ball : x ∈ ball c R := by
        rw [mem_ball] at hx ⊢; linarith [dist_triangle x w c]
      constructor
      · exact hx_ball
      · by_cases hxw : x = w
        · rw [hxw, hfw]
        · -- x ≠ w, so dist x w > 0
          set s := dist x w with hs_def
          have hs_pos : 0 < s := dist_pos.mpr hxw
          have hs_lt : s < ε := mem_ball.mp hx
          -- closedBall w s ⊆ closedBall c R
          have hs_sub : closedBall w s ⊆ closedBall c R :=
            (closedBall_subset_closedBall hs_lt.le).trans h_sub
          -- MVP at w gives f(w) = circleAvg(f, w, s)
          have hmvp_s := hmvp w hw_ball s hs_pos hs_sub
          -- f ≤ f(z₀) = f(w) on sphere w |s|
          have abs_s : |s| = s := abs_of_pos hs_pos
          have sph_sub : sphere w |s| ⊆ closedBall w s := by
            rw [abs_s]; exact sphere_subset_closedBall
          have hle_sph : ∀ y ∈ sphere w |s|, f y ≤ f z₀ :=
            fun y hy => hmax y (hs_sub (sph_sub hy))
          -- Continuity on sphere
          have hcont_sph : ContinuousOn f (sphere w |s|) :=
            hcont.mono (sph_sub.trans hs_sub)
          -- circleAverage f w s = f(z₀)
          have havg : circleAverage f w s = f z₀ := by rw [← hmvp_s, hfw]
          -- Apply eq_of_circleAverage_eq_of_le from MaximumPrinciple.lean
          have h_eq := eq_of_circleAverage_eq_of_le hs_pos.ne' hcont_sph hle_sph havg
          -- x ∈ sphere w |s| since dist x w = s > 0
          have hx_sph : x ∈ sphere w |s| := by
            rw [mem_sphere, abs_of_pos hs_pos]
          exact h_eq x hx_sph
    -- ball \ S is open (by continuity of f)
    have hT_open : IsOpen (ball c R \ S) := by
      have : ball c R \ S = ball c R ∩ f ⁻¹' {f z₀}ᶜ := by
        ext z; simp only [mem_diff, mem_sep_iff, mem_inter_iff, mem_preimage,
          mem_compl_iff, mem_singleton_iff, not_and, S]
        constructor
        · intro ⟨hz, hne⟩; exact ⟨hz, hne hz⟩
        · intro ⟨hz, hne⟩; exact ⟨hz, fun _ => hne⟩
      rw [this]
      exact (hcont.mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball
        isOpen_compl_singleton
    -- S nonempty
    have hS_ne : (ball c R ∩ S).Nonempty := ⟨z₀, hz₀, hz₀, rfl⟩
    -- By preconnectedness, ball ⊆ S
    have h_subset := hball_conn.isPreconnected.subset_left_of_subset_union
      hS_open hT_open disjoint_sdiff_self_right
      (fun z hz => by
        by_cases hzS : z ∈ S
        · exact Or.inl hzS
        · exact Or.inr ⟨hz, hzS⟩)
      hS_ne
    intro z hz
    exact (h_subset hz).2
  -- Extend from ball to closedBall by continuity
  intro z hz
  rcases (mem_closedBall.mp hz).eq_or_lt with h | h
  · -- z on the boundary: use density of ball in closedBall
    -- z ∈ closure(ball c R), f = f(z₀) on ball, f continuous → f(z) = f(z₀)
    have h_closure : z ∈ closure (ball c R) := by
      rw [closure_ball c hR.ne']; exact hz
    haveI h_nebot : (𝓝[ball c R] z).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp h_closure
    -- f converges to f(z) along 𝓝[ball c R] z (by continuity on closedBall)
    have h_tendsto : Tendsto f (𝓝[ball c R] z) (𝓝 (f z)) :=
      (hcont.continuousWithinAt hz).mono ball_subset_closedBall
    -- f equals the constant f(z₀) on ball c R
    have h_ev_eq : f =ᶠ[𝓝[ball c R] z] fun _ => f z₀ :=
      eventuallyEq_iff_exists_mem.mpr ⟨ball c R, self_mem_nhdsWithin,
        fun w hw => hball w hw⟩
    -- So f converges to f(z₀) along the same filter
    have h_tendsto' : Tendsto (fun _ => f z₀) (𝓝[ball c R] z) (𝓝 (f z)) :=
      h_tendsto.congr' h_ev_eq
    -- By uniqueness of limits, f(z) = f(z₀)
    exact tendsto_nhds_unique h_tendsto' tendsto_const_nhds
  · exact hball z (mem_ball.mpr h)

/-- Maximum principle for MVP functions on closed balls:
    if f satisfies MVP and attains its maximum at an interior point,
    then f is constant. -/
theorem mvp_maximum_principle (f : ℂ → ℝ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hcont : ContinuousOn f (closedBall c R))
    (hmvp : ∀ z ∈ ball c R, ∀ r > 0, closedBall z r ⊆ closedBall c R →
      f z = circleAverage f z r)
    (z₀ : ℂ) (hz₀ : z₀ ∈ ball c R)
    (hmax : ∀ z ∈ closedBall c R, f z ≤ f z₀) :
    ∀ z ∈ closedBall c R, f z = f z₀ :=
  mvp_max_le_sphere_max f c R hR hcont hmvp z₀ hz₀ hmax

/-- If f satisfies MVP, is continuous on closedBall, and vanishes on the sphere,
    then f = 0 on the ball. -/
theorem mvp_zero_boundary_implies_zero (f : ℂ → ℝ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hcont : ContinuousOn f (closedBall c R))
    (hmvp : ∀ z ∈ ball c R, ∀ r > 0, closedBall z r ⊆ closedBall c R →
      f z = circleAverage f z r)
    (hbdry : ∀ z, ‖z - c‖ = R → f z = 0) :
    ∀ z ∈ ball c R, f z = 0 := by
  -- Convert boundary to sphere
  have hbdry_sph : ∀ z ∈ sphere c R, f z = 0 := by
    intro z hz; exact hbdry z (by rwa [← dist_eq_norm, ← mem_sphere])
  -- Sphere is nonempty
  obtain ⟨w₀, hw₀⟩ := (NormedSpace.sphere_nonempty (x := c)).mpr hR.le
  -- Compact and nonempty
  have hK := isCompact_closedBall (x := c) (r := R)
  have hne : (closedBall c R).Nonempty := ⟨c, mem_closedBall_self hR.le⟩
  -- f ≤ 0 on ball: f achieves max on closedBall
  have hle : ∀ z ∈ ball c R, f z ≤ 0 := by
    obtain ⟨z_max, hz_max, hmax⟩ := hK.exists_isMaxOn hne hcont
    intro z hz
    have hfz_le : f z ≤ f z_max := hmax (ball_subset_closedBall hz)
    suffices f z_max ≤ 0 by linarith
    rcases (mem_closedBall.mp hz_max).eq_or_lt with h | h
    · linarith [hbdry_sph z_max (mem_sphere.mpr h)]
    · -- z_max in ball: f is constant on closedBall by max principle
      linarith [mvp_max_le_sphere_max f c R hR hcont hmvp z_max (mem_ball.mpr h) hmax w₀
        (sphere_subset_closedBall hw₀), hbdry_sph w₀ hw₀]
  -- f ≥ 0 on ball: -f achieves max on closedBall
  have hge : ∀ z ∈ ball c R, 0 ≤ f z := by
    -- -f satisfies MVP: need circleAverage(-f) = -circleAverage(f)
    have hmvp_neg : ∀ z ∈ ball c R, ∀ r > 0, closedBall z r ⊆ closedBall c R →
        (-f) z = circleAverage (-f) z r := by
      intro z hz r hr hsub
      show -f z = circleAverage (-f) z r
      have neg_eq : (-f) = ((-1 : ℝ) • f) := by ext x; simp
      rw [neg_eq, circleAverage_smul]
      simp [hmvp z hz r hr hsub]
    obtain ⟨z_min, hz_min, hmin⟩ := hK.exists_isMaxOn hne hcont.neg
    intro z hz
    have hfz_ge : (-f) z ≤ (-f) z_min := hmin (ball_subset_closedBall hz)
    simp only [Pi.neg_apply, neg_le_neg_iff] at hfz_ge
    suffices 0 ≤ f z_min by linarith
    rcases (mem_closedBall.mp hz_min).eq_or_lt with h | h
    · linarith [hbdry_sph z_min (mem_sphere.mpr h)]
    · -- z_min in ball: -f is constant, hence f is constant = 0
      have hconst := mvp_max_le_sphere_max (-f) c R hR hcont.neg hmvp_neg
        z_min (mem_ball.mpr h) hmin
      have := hconst w₀ (sphere_subset_closedBall hw₀)
      simp only [Pi.neg_apply, neg_inj] at this
      linarith [hbdry_sph w₀ hw₀]
  -- Combine
  intro z hz
  linarith [hle z hz, hge z hz]

/-!
## The Schwarz Integral

The Schwarz integral is a holomorphic function on a disc whose real part
gives the Poisson integral (harmonic extension of boundary data).

For a disc B(c, R) and continuous boundary data g on sphere(c, R):
  S(z) = (1/2π) ∫₀²π g(c + Re^{iθ}) · (Re^{iθ} + (z-c)) / (Re^{iθ} - (z-c)) dθ

S is holomorphic in z for |z-c| < R, and Re(S(z)) = P[g](z) is the Poisson integral.
-/

/-- The Schwarz integral for boundary data on a circle.
    This is holomorphic in z inside the disc, and its real part is the Poisson integral. -/
noncomputable def schwarzIntegral (g : ℂ → ℝ) (c : ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
    ((g (circleMap c R θ) : ℝ) : ℂ) *
      ((circleMap c R θ - c + (z - c)) / (circleMap c R θ - z))

/-- The Poisson integral: Re of the Schwarz integral. -/
noncomputable def poissonIntegralDisc (g : ℂ → ℝ) (c : ℂ) (R : ℝ) (z : ℂ) : ℝ :=
  (schwarzIntegral g c R z).re

/-!
## Properties of the Schwarz/Poisson Integral

Key properties needed for the MVP → Harmonic proof:
1. The Schwarz integral is holomorphic inside the disc
2. The Poisson integral (= Re(Schwarz)) is therefore harmonic
3. The Poisson integral has the correct boundary values
-/

/-- Helper: the Schwarz integrand is differentiable in z for each θ. -/
private lemma schwarz_integrand_hasDerivAt {c z ζ : ℂ} (hζz : ζ - z ≠ 0) (a : ℂ) :
    HasDerivAt (fun w => a * ((ζ - c + (w - c)) / (ζ - w)))
      (a * (2 * (ζ - c) / (ζ - z) ^ 2)) z := by
  have h_num : HasDerivAt (fun w => ζ - c + (w - c)) 1 z := by
    have h1 : HasDerivAt (fun w => w - c) 1 z := (hasDerivAt_id z).sub_const c
    convert (hasDerivAt_const z (ζ - c)).add h1 using 1; ring
  have h_den : HasDerivAt (fun w => ζ - w) (-1) z := by
    have h := (hasDerivAt_const z ζ).sub (hasDerivAt_id z)
    simp only [zero_sub] at h; exact h
  have h_div := h_num.div h_den hζz
  have h_eq : (1 * (ζ - z) - (ζ - c + (z - c)) * -1) / (ζ - z) ^ 2 =
      2 * (ζ - c) / (ζ - z) ^ 2 := by ring
  rw [h_eq] at h_div
  have h_mul := (hasDerivAt_const z a).mul h_div
  simp only [zero_mul, zero_add] at h_mul; exact h_mul

/-- Helper: norm bound on the Schwarz integrand derivative. -/
private lemma schwarz_deriv_norm_bound {c z ζ : ℂ} {M R δ : ℝ}
    (hζc : ‖ζ - c‖ = R) (hδ : δ ≤ ‖ζ - z‖) (hδ_pos : 0 < δ)
    {a : ℂ} (ha : ‖a‖ ≤ M) :
    ‖a * (2 * (ζ - c) / (ζ - z) ^ 2)‖ ≤ M * (2 * R) / δ ^ 2 := by
  have hM_nn : 0 ≤ M := le_trans (norm_nonneg a) ha
  have hR_nn : 0 ≤ R := hζc ▸ norm_nonneg (ζ - c)
  rw [norm_mul, norm_div, norm_mul, norm_pow, Complex.norm_ofNat, hζc]
  -- Goal: ‖a‖ * (2 * R / ‖ζ - z‖ ^ 2) ≤ M * (2 * R) / δ ^ 2
  calc ‖a‖ * (2 * R / ‖ζ - z‖ ^ 2)
      ≤ ‖a‖ * (2 * R / δ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg a)
        exact div_le_div_of_nonneg_left (by linarith) (pow_pos hδ_pos 2)
          (sq_le_sq' (by linarith [norm_nonneg (ζ - z)]) hδ)
    _ ≤ M * (2 * R / δ ^ 2) := by
        exact mul_le_mul_of_nonneg_right ha (div_nonneg (by linarith) (sq_nonneg _))
    _ = M * (2 * R) / δ ^ 2 := by ring

/-- The Schwarz integral is differentiable (holomorphic) at points inside the disc.
    This follows from differentiation under the integral sign:
    the integrand is holomorphic in z (for fixed θ), and the z-derivative
    is bounded by an integrable function. -/
theorem schwarzIntegral_differentiableAt (g : ℂ → ℝ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hg : ContinuousOn g (sphere c R))
    (z : ℂ) (hz : z ∈ ball c R) :
    DifferentiableAt ℂ (schwarzIntegral g c R) z := by
  set ζ : ℝ → ℂ := circleMap c R with hζ_def
  -- Parameters
  have hz_dist : dist z c < R := mem_ball.mp hz
  set δ := (R - dist z c) / 2 with hδ_def
  have hδ_pos : 0 < δ := by linarith
  -- g ∘ ζ is continuous
  have hgζ : Continuous (fun θ => g (ζ θ)) :=
    hg.comp_continuous (continuous_circleMap c R) (circleMap_mem_sphere c hR.le)
  -- ζ(θ) - w ≠ 0 for w ∈ closedBall z δ
  have hζ_ne : ∀ θ, ∀ w ∈ closedBall z δ, ζ θ - w ≠ 0 := by
    intro θ w hw habs
    have hζw : ζ θ = w := sub_eq_zero.mp habs
    have h_sph : w ∈ sphere c R := hζw ▸ circleMap_mem_sphere c hR.le θ
    have h_ball : w ∈ ball c R := by
      rw [mem_ball]; linarith [mem_closedBall.mp hw, dist_triangle w z c]
    exact absurd (mem_sphere.mp h_sph) (ne_of_lt (mem_ball.mp h_ball))
  -- dist (ζ θ) w ≥ δ for w ∈ closedBall z δ
  have hζw_ge : ∀ θ, ∀ w ∈ closedBall z δ, δ ≤ dist (ζ θ) w := by
    intro θ w hw
    have h1 : dist (ζ θ) c = R := mem_sphere.mp (circleMap_mem_sphere c hR.le θ)
    linarith [dist_triangle (ζ θ) z c, dist_triangle (ζ θ) w z, mem_closedBall.mp hw]
  -- ‖ζ θ - w‖ ≥ δ
  have hζw_norm : ∀ θ, ∀ w ∈ closedBall z δ, δ ≤ ‖ζ θ - w‖ := by
    intro θ w hw; rw [← dist_eq_norm]; exact hζw_ge θ w hw
  -- ‖ζ θ - c‖ = R
  have hζc_norm : ∀ θ, ‖ζ θ - c‖ = R := by
    intro θ; rw [← dist_eq_norm]; exact mem_sphere.mp (circleMap_mem_sphere c hR.le θ)
  -- Sup bound on ‖g‖: use IsCompact.exists_isMaxOn on the sphere
  have hg_bdd : ∃ M : ℝ, 0 ≤ M ∧ ∀ θ, ‖(↑(g (ζ θ)) : ℂ)‖ ≤ M := by
    have hgn : ContinuousOn (fun x => ‖g x‖) (sphere c R) :=
      continuous_norm.comp_continuousOn hg
    obtain ⟨w₀, hw₀⟩ := (NormedSpace.sphere_nonempty (x := c)).mpr hR.le
    obtain ⟨w_max, hw_mem, hw_max⟩ := (isCompact_sphere c R).exists_isMaxOn ⟨w₀, hw₀⟩ hgn
    refine ⟨‖g w_max‖, norm_nonneg _, fun θ => ?_⟩
    simp only [Complex.norm_real]
    exact hw_max (circleMap_mem_sphere c hR.le θ)
  obtain ⟨M, hM_nn, hM_bound⟩ := hg_bdd
  set L := M * (2 * R) / δ ^ 2 with hL_def
  -- Continuity of integrand in θ (for fixed w with ζ θ - w ≠ 0)
  have hF_cont : ∀ w, (∀ θ, ζ θ - w ≠ 0) →
      Continuous (fun θ => (↑(g (ζ θ)) : ℂ) * ((ζ θ - c + (w - c)) / (ζ θ - w))) := by
    intro w hne
    refine Continuous.mul (continuous_ofReal.comp hgζ) ?_
    refine continuous_iff_continuousAt.mpr (fun θ => ContinuousAt.div ?_ ?_ (hne θ))
    · exact (((continuous_circleMap c R).sub continuous_const).add
        continuous_const).continuousAt
    · exact ((continuous_circleMap c R).sub continuous_const).continuousAt
  -- Continuity of derivative in θ (at z)
  have hF'_cont :
      Continuous (fun θ => (↑(g (ζ θ)) : ℂ) * (2 * (ζ θ - c) / (ζ θ - z) ^ 2)) := by
    refine Continuous.mul (continuous_ofReal.comp hgζ) ?_
    refine continuous_iff_continuousAt.mpr (fun θ => ContinuousAt.div ?_ ?_
      (pow_ne_zero 2 (hζ_ne θ z (mem_closedBall_self hδ_pos.le))))
    · exact (continuous_const.mul ((continuous_circleMap c R).sub
        continuous_const)).continuousAt
    · exact (((continuous_circleMap c R).sub continuous_const).pow 2).continuousAt
  -- Apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
  have key := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℂ) (μ := MeasureTheory.MeasureSpace.volume)
    -- hs : s ∈ 𝓝 z
    (closedBall_mem_nhds z hδ_pos)
    -- hF_meas
    (by filter_upwards [closedBall_mem_nhds z hδ_pos] with w hw
        exact (hF_cont w (fun θ => hζ_ne θ w hw)).aestronglyMeasurable.restrict)
    -- hF_int
    ((hF_cont z (fun θ => hζ_ne θ z (mem_closedBall_self hδ_pos.le))).intervalIntegrable
      0 (2 * π))
    -- hF'_meas (at x₀ = z)
    (hF'_cont.aestronglyMeasurable.restrict)
    -- h_bound: ‖F' x t‖ ≤ bound t for x ∈ s
    (by filter_upwards with θ _hθ
        intro w hw
        exact schwarz_deriv_norm_bound (hζc_norm θ) (hζw_norm θ w hw) hδ_pos (hM_bound θ))
    -- bound_integrable
    intervalIntegrable_const
    -- h_diff: HasDerivAt for each θ and each x ∈ s
    (by filter_upwards with θ _hθ
        intro w hw
        exact schwarz_integrand_hasDerivAt (hζ_ne θ w hw) _)).2
  -- schwarzIntegral = (2π)⁻¹ • ∫ ..., so DifferentiableAt follows
  show DifferentiableAt ℂ (fun z => ((2 * π)⁻¹ : ℝ) • ∫ θ in (0 : ℝ)..2 * π,
    ((g (ζ θ) : ℝ) : ℂ) * ((ζ θ - c + (z - c)) / (ζ θ - z))) z
  -- Convert ℝ-smul to ℂ-multiplication to avoid SMulCommClass ℂ ℝ ℂ
  have h_smul_eq : (fun z => ((2 * π)⁻¹ : ℝ) • ∫ θ in (0 : ℝ)..2 * π,
      ((g (ζ θ) : ℝ) : ℂ) * ((ζ θ - c + (z - c)) / (ζ θ - z))) =
    (fun z => (((2 * π)⁻¹ : ℝ) : ℂ) * ∫ θ in (0 : ℝ)..2 * π,
      ((g (ζ θ) : ℝ) : ℂ) * ((ζ θ - c + (z - c)) / (ζ θ - z))) := by
    ext w; rw [Complex.real_smul]
  rw [h_smul_eq]
  exact key.differentiableAt.const_mul _

/-- The Poisson integral is harmonic on the ball.
    This follows from the Schwarz integral being holomorphic:
    Re(holomorphic) is harmonic. -/
theorem poissonIntegral_harmonicOnNhd (g : ℂ → ℝ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hg : ContinuousOn g (sphere c R)) :
    HarmonicOnNhd (poissonIntegralDisc g c R) (ball c R) := by
  intro z hz
  -- Schwarz integral is holomorphic at z
  have hSdiff := schwarzIntegral_differentiableAt g c R hR hg z hz
  -- Re(holomorphic) is harmonic
  -- Need: DifferentiableAt ℂ → AnalyticAt ℂ → harmonicAt_re
  have hSdiffOn : DifferentiableOn ℂ (schwarzIntegral g c R) (ball c R) := by
    intro w hw
    exact (schwarzIntegral_differentiableAt g c R hR hg w hw).differentiableWithinAt
  have hSana : AnalyticOnNhd ℂ (schwarzIntegral g c R) (ball c R) :=
    hSdiffOn.analyticOnNhd isOpen_ball
  exact (hSana z hz).harmonicAt_re

/-!
## Kernel Integral Identities

The Schwarz kernel integrates to 2π over the full circle, which is fundamental
for the boundary value and approximate identity arguments.
-/

/-- ζ(θ) - z ≠ 0 for z strictly inside the disc. -/
private lemma circleMap_sub_ne_zero {c : ℂ} {R : ℝ} (hR : 0 < R)
    {z : ℂ} (hz : z ∈ ball c R) (θ : ℝ) : circleMap c R θ - z ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have hsph := circleMap_mem_sphere c hR.le θ
  rw [h, mem_sphere] at hsph
  exact absurd hsph (ne_of_lt (mem_ball.mp hz))

/-- The integral of (ζ(θ)-c)/(ζ(θ)-z) over the circle equals 2π.
    This follows from the Cauchy integral formula ∮ (ζ-z)⁻¹ dζ = 2πI. -/
private lemma circle_ratio_integral {c : ℂ} {R : ℝ} (hR : 0 < R)
    {z : ℂ} (hz : z ∈ ball c R) :
    ∫ θ in (0 : ℝ)..2 * π,
      ((circleMap c R θ - c) / (circleMap c R θ - z) : ℂ) = 2 * ↑Real.pi := by
  -- From Cauchy: ∮ (ζ-z)⁻¹ = 2πI
  have hCauchy := circleIntegral.integral_sub_inv_of_mem_ball hz
  -- Rewrite ∮ integrand: deriv(ζ)(θ) • (ζ(θ)-z)⁻¹ = ((ζ(θ)-c)/(ζ(θ)-z)) * I
  have h_eq : ∀ θ : ℝ,
      deriv (circleMap c R) θ • (circleMap c R θ - z)⁻¹ =
      ((circleMap c R θ - c) / (circleMap c R θ - z)) * I := by
    intro θ
    simp only [deriv_circleMap, circleMap_sub_center, smul_eq_mul]
    ring
  simp only [circleIntegral, h_eq] at hCauchy
  -- Pull I to the right: ∫ f(θ)*I = (∫ f(θ)) * I
  -- Cancel I from both sides: (∫ f) * I = 2π * I → ∫ f = 2π
  have h_pull : ∫ θ in (0:ℝ)..2 * π,
      (circleMap c R θ - c) / (circleMap c R θ - z) * I =
    (∫ θ in (0:ℝ)..2 * π, (circleMap c R θ - c) / (circleMap c R θ - z)) * I :=
    intervalIntegral.integral_mul_const _ _
  have hCauchy' : (∫ θ in (0:ℝ)..2 * π,
      (circleMap c R θ - c) / (circleMap c R θ - z)) * I = 2 * ↑Real.pi * I := by
    rwa [← h_pull]
  exact mul_right_cancel₀ Complex.I_ne_zero hCauchy'

/-- Continuity of (ζ(θ)-c)/(ζ(θ)-z) as a function of θ. -/
private lemma circle_ratio_continuous {c : ℂ} {R : ℝ} (hR : 0 < R)
    {z : ℂ} (hz : z ∈ ball c R) :
    Continuous (fun θ => (circleMap c R θ - c) / (circleMap c R θ - z) : ℝ → ℂ) :=
  ((continuous_circleMap c R).sub continuous_const).div
    ((continuous_circleMap c R).sub continuous_const)
    (fun θ => circleMap_sub_ne_zero hR hz θ)

/-- The Schwarz kernel integrates to 2π over the full circle.
    K(z,θ) = (ζ(θ)-c+(z-c))/(ζ(θ)-z) and ∫₀²π K dθ = 2π. -/
private lemma schwarz_kernel_integral {c : ℂ} {R : ℝ} (hR : 0 < R)
    {z : ℂ} (hz : z ∈ ball c R) :
    ∫ θ in (0 : ℝ)..2 * π,
      ((circleMap c R θ - c + (z - c)) / (circleMap c R θ - z) : ℂ) = 2 * ↑Real.pi := by
  -- K = 2*(ζ-c)/(ζ-z) - 1
  have h_split : ∀ θ : ℝ,
      (circleMap c R θ - c + (z - c)) / (circleMap c R θ - z) =
      2 * ((circleMap c R θ - c) / (circleMap c R θ - z)) - 1 := by
    intro θ
    have h := circleMap_sub_ne_zero hR hz θ
    field_simp
    ring
  simp_rw [h_split]
  have hf_int : IntervalIntegrable
      (fun θ => (circleMap c R θ - c) / (circleMap c R θ - z) : ℝ → ℂ) volume 0 (2 * π) :=
    (circle_ratio_continuous hR hz).intervalIntegrable 0 (2 * π)
  rw [intervalIntegral.integral_sub (hf_int.const_mul 2)
    (intervalIntegrable_const (μ := volume))]
  have h_const_mul : ∫ x in (0:ℝ)..2 * π,
      2 * ((circleMap c R x - c) / (circleMap c R x - z)) =
    2 * ∫ x in (0:ℝ)..2 * π, (circleMap c R x - c) / (circleMap c R x - z) :=
    intervalIntegral.integral_const_mul _ _
  rw [h_const_mul, circle_ratio_integral hR hz,
    intervalIntegral.integral_const, sub_zero]
  change 2 * (2 * ↑Real.pi) - (↑(2 * π) : ℂ) * 1 = 2 * ↑Real.pi
  push_cast; ring

/-- Re((u+v)/(u-v)) = (‖u‖²-‖v‖²)/‖u-v‖² for u ≠ v. -/
private lemma re_sum_div_diff {u v : ℂ} (h : u - v ≠ 0) :
    ((u + v) / (u - v)).re = (‖u‖ ^ 2 - ‖v‖ ^ 2) / ‖u - v‖ ^ 2 := by
  have hns := (Complex.normSq_pos.mpr h).ne'
  simp only [← Complex.normSq_eq_norm_sq]
  rw [Complex.div_re, ← add_div]
  congr 1
  simp only [Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im,
    Complex.normSq_apply]
  ring

/-- The Poisson kernel Re(K(z,θ)) = (R²-|z-c|²)/|ζ(θ)-z|². -/
private lemma schwarz_kernel_re {c : ℂ} {R : ℝ} (hR : 0 < R)
    {z : ℂ} (hz : z ∈ ball c R) (θ : ℝ) :
    ((circleMap c R θ - c + (z - c)) / (circleMap c R θ - z)).re =
    (R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2 := by
  have hne := circleMap_sub_ne_zero hR hz θ
  have h_eq2 : circleMap c R θ - z = (circleMap c R θ - c) - (z - c) := by ring
  rw [show circleMap c R θ - c + (z - c) = (circleMap c R θ - c) + (z - c) from rfl, h_eq2,
    re_sum_div_diff (by rwa [h_eq2] at hne)]
  congr 1
  · -- ‖ζ-c‖² = R²
    have h_norm : ‖circleMap c R θ - c‖ = R := by
      rw [← dist_eq_norm]
      exact mem_sphere.mp (circleMap_mem_sphere c hR.le θ)
    rw [h_norm]

/-- The Poisson kernel is nonneg for z inside the disc. -/
private lemma poisson_kernel_nonneg {c : ℂ} {R : ℝ} (hR : 0 < R)
    {z : ℂ} (hz : z ∈ ball c R) (θ : ℝ) :
    0 ≤ (R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2 := by
  apply div_nonneg
  · have hzR : ‖z - c‖ < R := by rwa [← dist_eq_norm, ← mem_ball]
    have : 0 ≤ (R - ‖z - c‖) * (R + ‖z - c‖) :=
      mul_nonneg (by linarith) (by linarith [norm_nonneg (z - c)])
    linarith [sq_abs R, sq_abs ‖z - c‖]
  · positivity

/-- Continuity of the Poisson kernel as a function of θ. -/
private lemma poisson_kernel_continuous {c : ℂ} {R : ℝ} (hR : 0 < R)
    {z : ℂ} (hz : z ∈ ball c R) :
    Continuous (fun θ => (R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2) :=
  continuous_const.div (((continuous_circleMap c R).sub continuous_const).norm.pow 2)
    (fun θ => pow_ne_zero 2 (norm_ne_zero_iff.mpr (circleMap_sub_ne_zero hR hz θ)))

/-- The Poisson kernel integrates to 2π. -/
private lemma poisson_kernel_integral {c : ℂ} {R : ℝ} (hR : 0 < R)
    {z : ℂ} (hz : z ∈ ball c R) :
    ∫ θ in (0:ℝ)..(2*π),
      (R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2 = 2 * π := by
  have hK_int : IntervalIntegrable (fun θ =>
      (circleMap c R θ - c + (z - c)) / (circleMap c R θ - z) : ℝ → ℂ)
      MeasureTheory.MeasureSpace.volume 0 (2 * π) := by
    exact (((continuous_circleMap c R).sub continuous_const |>.add continuous_const).div
      ((continuous_circleMap c R).sub continuous_const)
      (fun θ => circleMap_sub_ne_zero hR hz θ)).intervalIntegrable 0 (2 * π)
  have h_re_comm := Complex.reCLM.intervalIntegral_comp_comm hK_int (a := 0) (b := 2 * π)
  have h_rw : (fun θ => ((circleMap c R θ - c + (z - c)) / (circleMap c R θ - z)).re) =
      (fun θ => (R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2) :=
    funext (schwarz_kernel_re hR hz)
  rw [← h_rw]
  -- h_re_comm : ∫ reCLM (f x) = reCLM (∫ f x); need to convert reCLM to .re
  have h_eq : ∫ θ in (0:ℝ)..2 * π,
      ((circleMap c R θ - c + (z - c)) / (circleMap c R θ - z)).re =
    (∫ θ in (0:ℝ)..2 * π,
      (circleMap c R θ - c + (z - c)) / (circleMap c R θ - z)).re := by
    exact_mod_cast h_re_comm
  rw [h_eq, schwarz_kernel_integral hR hz]
  simp

/-- Continuity of g ∘ circleMap. -/
private lemma g_circleMap_continuous {c : ℂ} {R : ℝ} (hR : 0 < R) {g : ℂ → ℝ}
    (hg : ContinuousOn g (sphere c R)) :
    Continuous (fun θ => g (circleMap c R θ)) :=
  hg.comp_continuous (continuous_circleMap c R) (circleMap_mem_sphere c hR.le)

/-- The Poisson integral equals a real integral with the Poisson kernel. -/
private lemma poissonIntegralDisc_eq_real {c : ℂ} {R : ℝ} (hR : 0 < R)
    {z : ℂ} (hz : z ∈ ball c R) {g : ℂ → ℝ} (hg : ContinuousOn g (sphere c R)) :
    poissonIntegralDisc g c R z = (2 * π)⁻¹ *
      ∫ θ in (0:ℝ)..(2*π),
        g (circleMap c R θ) * ((R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2) := by
  unfold poissonIntegralDisc schwarzIntegral
  -- (r • z).re = r * z.re for real r
  show ((2 * π)⁻¹ • ∫ θ in (0:ℝ)..(2*π),
    ((g (circleMap c R θ) : ℝ) : ℂ) *
      ((circleMap c R θ - c + (z - c)) / (circleMap c R θ - z))).re = _
  rw [Complex.real_smul, Complex.re_ofReal_mul]
  congr 1
  -- Re commutes with integral
  have hK_cont : Continuous (fun θ =>
      ((g (circleMap c R θ) : ℝ) : ℂ) *
        ((circleMap c R θ - c + (z - c)) / (circleMap c R θ - z))) :=
    (continuous_ofReal.comp (g_circleMap_continuous hR hg)).mul
      (((continuous_circleMap c R).sub continuous_const |>.add continuous_const).div
        ((continuous_circleMap c R).sub continuous_const) (fun θ => circleMap_sub_ne_zero hR hz θ))
  have h_int : IntervalIntegrable (fun θ =>
      ((g (circleMap c R θ) : ℝ) : ℂ) *
        ((circleMap c R θ - c + (z - c)) / (circleMap c R θ - z))) volume 0 (2 * π) :=
    hK_cont.intervalIntegrable 0 (2 * π)
  -- Re commutes with integral (reCLM and .re are definitionally equal)
  have h_re_comm : (∫ θ in (0:ℝ)..2 * π,
      (↑(g (circleMap c R θ)) : ℂ) * ((circleMap c R θ - c + (z - c)) / (circleMap c R θ - z))).re =
    ∫ θ in (0:ℝ)..2 * π,
      ((↑(g (circleMap c R θ)) : ℂ) * ((circleMap c R θ - c + (z - c)) / (circleMap c R θ - z))).re :=
    (Complex.reCLM.intervalIntegral_comp_comm h_int).symm
  rw [h_re_comm]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [Complex.re_ofReal_mul, schwarz_kernel_re hR hz]

/-- The Poisson integral has the correct boundary values:
    as z → ζ on the sphere, poissonIntegralDisc g c R z → g(ζ). -/
theorem poissonIntegral_boundary_values (g : ℂ → ℝ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hg : ContinuousOn g (sphere c R)) :
    ∀ ζ, ζ ∈ sphere c R →
      Filter.Tendsto (poissonIntegralDisc g c R) (𝓝[ball c R] ζ) (𝓝 (g ζ)) := by
  intro ζ₀ hζ₀
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- g uniformly continuous on sphere (compact)
  have hg_unif := (isCompact_sphere c R).uniformContinuousOn_of_continuous hg
  rw [Metric.uniformContinuousOn_iff] at hg_unif
  obtain ⟨δ₁, hδ₁_pos, hg_δ₁⟩ := hg_unif (ε / 2) (half_pos hε)
  -- Bound on |g|
  have hg_cont := g_circleMap_continuous hR hg
  obtain ⟨M, hM_pos, hM_bound⟩ : ∃ M > 0, ∀ ζ' ∈ sphere c R, |g ζ'| ≤ M := by
    obtain ⟨w, hw_mem, hw_max⟩ := (isCompact_sphere c R).exists_isMaxOn
      (NormedSpace.sphere_nonempty.mpr hR.le) (continuous_abs.comp_continuousOn hg)
    exact ⟨|g w| + 1, by positivity, fun ζ' hζ' => by
      linarith [show |g ζ'| ≤ |g w| by simpa using hw_max hζ']⟩
  -- Choose δ: near boundary separation δ₁/2, far decay via R²-|z-c|²
  set δ := min (δ₁ / 2) (ε * δ₁ ^ 2 / (32 * M * R + 1)) with hδ_def
  have hδ_pos : 0 < δ := by positivity
  refine ⟨δ, hδ_pos, fun z hz_ball hz_dist => ?_⟩
  rw [Real.dist_eq, poissonIntegralDisc_eq_real hR hz_ball hg]
  -- Normalization: g(ζ₀) = (2π)⁻¹ * ∫ g(ζ₀) * Pr
  have hPr_nn := fun θ => poisson_kernel_nonneg hR hz_ball θ
  have hPr_int := poisson_kernel_integral hR hz_ball
  have hPr_cont := poisson_kernel_continuous hR hz_ball
  -- Write difference as integral
  have hg₀_eq : g ζ₀ = (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2*π),
      g ζ₀ * ((R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2) := by
    erw [intervalIntegral.integral_const_mul, hPr_int]
    field_simp
  rw [hg₀_eq, ← mul_sub]
  rw [show (∫ θ in (0:ℝ)..(2*π),
        g (circleMap c R θ) * ((R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2)) -
      (∫ θ in (0:ℝ)..(2*π),
        g ζ₀ * ((R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2)) =
    ∫ θ in (0:ℝ)..(2*π),
      (g (circleMap c R θ) * ((R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2) -
       g ζ₀ * ((R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2)) from
    (intervalIntegral.integral_sub
      ((hg_cont.mul hPr_cont).intervalIntegrable 0 (2*π))
      ((continuous_const.mul hPr_cont).intervalIntegrable 0 (2*π))).symm]
  -- Simplify integrand: g(ζ(θ))*Pr - g(ζ₀)*Pr = (g(ζ(θ))-g(ζ₀))*Pr
  simp_rw [show ∀ θ, g (circleMap c R θ) * ((R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2) -
    g ζ₀ * ((R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2) =
    (g (circleMap c R θ) - g ζ₀) * ((R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2)
    from fun θ => by ring]
  -- Key auxiliary estimates
  have hζ₀c : ‖ζ₀ - c‖ = R := by
    rw [← dist_eq_norm]; exact mem_sphere.mp hζ₀
  have hzR : ‖z - c‖ < R := by rwa [← dist_eq_norm, ← mem_ball]
  -- Set up the constant C = 16MRδ/δ₁² and show C < ε/2
  set C := 16 * M * R * δ / δ₁ ^ 2 with hC_def
  have hC_nn : 0 ≤ C := by positivity
  have hC_lt : C < ε / 2 := by
    have hδ_le : δ ≤ ε * δ₁ ^ 2 / (32 * M * R + 1) := min_le_right _ _
    calc C ≤ 16 * M * R * (ε * δ₁ ^ 2 / (32 * M * R + 1)) / δ₁ ^ 2 := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hδ_le (by positivity)) (by positivity)
      _ = 16 * M * R * ε / (32 * M * R + 1) := by field_simp
      _ < ε / 2 := by
          rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < 32 * M * R + 1) two_pos]
          nlinarith
  -- R² - ‖z-c‖² < 2Rδ (using triangle inequality: R - ‖z-c‖ ≤ dist z ζ₀ < δ)
  have h_numer_bound : R ^ 2 - ‖z - c‖ ^ 2 < 2 * R * δ := by
    have h_tri : R - ‖z - c‖ ≤ dist z ζ₀ := by
      have : ‖ζ₀ - c‖ ≤ ‖ζ₀ - z‖ + ‖z - c‖ := by
        calc ‖ζ₀ - c‖ = ‖(ζ₀ - z) + (z - c)‖ := by ring_nf
          _ ≤ ‖ζ₀ - z‖ + ‖z - c‖ := norm_add_le _ _
      rw [dist_comm, dist_eq_norm]; linarith [hζ₀c]
    calc R ^ 2 - ‖z - c‖ ^ 2 = (R - ‖z - c‖) * (R + ‖z - c‖) := by ring
      _ ≤ dist z ζ₀ * (R + ‖z - c‖) :=
          mul_le_mul_of_nonneg_right h_tri (by linarith [norm_nonneg (z - c)])
      _ < δ * (R + ‖z - c‖) := by nlinarith [norm_nonneg (z - c)]
      _ ≤ δ * (2 * R) := mul_le_mul_of_nonneg_left (by linarith) hδ_pos.le
      _ = 2 * R * δ := by ring
  -- Pointwise bound: |g(ζ(θ))-g(ζ₀)| · Pr ≤ (ε/2) · Pr + C
  have h_ptwise : ∀ θ : ℝ,
      |g (circleMap c R θ) - g ζ₀| *
        ((R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2) ≤
      (ε / 2) * ((R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2) + C := by
    intro θ
    by_cases h_near : dist (circleMap c R θ) ζ₀ < δ₁
    · -- Near case: |g-g₀| < ε/2 by uniform continuity
      have hg_near : |g (circleMap c R θ) - g ζ₀| < ε / 2 := by
        have := hg_δ₁ (circleMap c R θ) (circleMap_mem_sphere c hR.le θ) ζ₀ hζ₀ h_near
        rwa [Real.dist_eq] at this
      linarith [mul_le_mul_of_nonneg_right hg_near.le (hPr_nn θ)]
    · -- Far case: Pr ≤ 8Rδ/δ₁², |g-g₀| ≤ 2M, product ≤ C
      push_neg at h_near
      -- dist(ζ(θ), z) ≥ δ₁/2
      have h_dist_lower : δ₁ / 2 ≤ dist (circleMap c R θ) z := by
        have h1 := dist_triangle (circleMap c R θ) z ζ₀
        have h2 : δ ≤ δ₁ / 2 := min_le_left _ _
        linarith
      -- ‖ζ(θ)-z‖² ≥ (δ₁/2)²
      have h_norm_sq_lower : (δ₁ / 2) ^ 2 ≤ ‖circleMap c R θ - z‖ ^ 2 := by
        have : δ₁ / 2 ≤ ‖circleMap c R θ - z‖ := by rwa [← dist_eq_norm]
        nlinarith [norm_nonneg (circleMap c R θ - z)]
      -- Pr ≤ 8Rδ/δ₁²
      have h_Pr_bound : (R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2 ≤
          8 * R * δ / δ₁ ^ 2 := by
        calc (R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2
            ≤ (2 * R * δ) / ‖circleMap c R θ - z‖ ^ 2 :=
              div_le_div_of_nonneg_right h_numer_bound.le (by positivity)
          _ ≤ (2 * R * δ) / (δ₁ / 2) ^ 2 :=
              div_le_div_of_nonneg_left (by positivity) (by positivity) h_norm_sq_lower
          _ = 8 * R * δ / δ₁ ^ 2 := by field_simp; ring
      -- |g-g₀| ≤ 2M
      have h_g_bound : |g (circleMap c R θ) - g ζ₀| ≤ 2 * M := by
        have h1 := hM_bound _ (circleMap_mem_sphere c hR.le θ)
        have h2 := hM_bound _ hζ₀
        rw [abs_le] at h1 h2 ⊢; constructor <;> linarith
      -- Product: |g-g₀|·Pr ≤ 2M · (8Rδ/δ₁²) = C ≤ (ε/2)·Pr + C
      calc |g (circleMap c R θ) - g ζ₀| *
            ((R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2)
          ≤ (2 * M) * (8 * R * δ / δ₁ ^ 2) :=
            mul_le_mul h_g_bound h_Pr_bound (hPr_nn θ) (by positivity)
        _ = C := by simp only [hC_def]; ring
        _ ≤ (ε / 2) * ((R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2) + C :=
            le_add_of_nonneg_left (mul_nonneg (by positivity) (hPr_nn θ))
  -- Use norm_integral_le_of_norm_le to bound ‖∫ f‖ ≤ ∫ bound
  have h_bound_cont : Continuous (fun θ =>
      (ε / 2) * ((R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2) + C) :=
    (continuous_const.mul hPr_cont).add continuous_const
  have h_int_norm := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := fun θ => (g (circleMap c R θ) - g ζ₀) *
      ((R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2))
    (show (0:ℝ) ≤ 2 * π from by linarith [Real.pi_pos])
    (by filter_upwards with θ; intro _
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hPr_nn θ)]
        exact h_ptwise θ)
    (h_bound_cont.intervalIntegrable 0 (2 * π))
  -- Compute ∫ bound = (ε/2)·2π + C·2π
  have h_int_val : ∫ θ in (0:ℝ)..(2*π),
      ((ε / 2) * ((R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2) + C) =
      (ε / 2) * (2 * π) + C * (2 * π) := by
    have h_add := (intervalIntegral.integral_add
      ((continuous_const.mul hPr_cont).intervalIntegrable 0 (2*π))
      (intervalIntegrable_const (μ := volume)) :
      ∫ θ in (0:ℝ)..(2*π),
        (ε / 2 * ((R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2) + C) =
      (∫ θ in (0:ℝ)..(2*π), ε / 2 * ((R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2)) +
      ∫ θ in (0:ℝ)..(2*π), C)
    rw [h_add]
    erw [intervalIntegral.integral_const_mul, hPr_int,
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]; ring
  rw [h_int_val] at h_int_norm
  -- Final calculation: |(2π)⁻¹ * ∫ f| < ε
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (2 * π)⁻¹), ← Real.norm_eq_abs]
  calc (2 * π)⁻¹ * ‖∫ θ in (0:ℝ)..(2*π), (g (circleMap c R θ) - g ζ₀) *
          ((R ^ 2 - ‖z - c‖ ^ 2) / ‖circleMap c R θ - z‖ ^ 2)‖
      ≤ (2 * π)⁻¹ * ((ε / 2) * (2 * π) + C * (2 * π)) :=
        mul_le_mul_of_nonneg_left h_int_norm (by positivity)
    _ = ε / 2 + C := by field_simp
    _ < ε := by linarith

/-!
## MVP Implies Harmonic

The main theorem: continuous functions satisfying MVP are harmonic.
-/

/-- In a normed space, closedBall z r ⊆ closedBall c R implies r + dist z c ≤ R.
    Proof: construct a point at distance r from z in the direction away from c. -/
private theorem dist_add_le_of_closedBall_subset {z c : ℂ} {r R : ℝ} (hr : 0 < r)
    (hsub : closedBall z r ⊆ closedBall c R) : r + dist z c ≤ R := by
  by_cases hzc : z = c
  · -- z = c case: take any point at distance r from z
    subst hzc
    have hw_mem : z + (↑r : ℂ) ∈ closedBall z r := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      simp [Complex.norm_real, abs_of_pos hr]
    have := mem_closedBall.mp (hsub hw_mem)
    simp only [dist_self, add_zero]
    -- After subst, this : dist (z + ↑r) z ≤ R, and dist (z + ↑r) z = r
    have : dist (z + (↑r : ℂ)) z = r := by
      rw [dist_eq_norm, add_sub_cancel_left]
      simp [Complex.norm_real, abs_of_pos hr]
    linarith
  · -- z ≠ c case: go in direction away from c
    have hzc_ne : z - c ≠ 0 := sub_ne_zero.mpr hzc
    set u := (‖z - c‖⁻¹ : ℝ) • (z - c)
    have hu_norm : ‖u‖ = 1 := by
      simp only [u]
      rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hzc_ne)
    set w := z + r • u
    have hw_dist_z : dist w z = r := by
      simp only [w, dist_eq_norm, add_sub_cancel_left]
      rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hr, hu_norm, mul_one]
    have hw_mem : w ∈ closedBall z r := by rw [mem_closedBall]; linarith
    have hw_cb := mem_closedBall.mp (hsub hw_mem)
    -- Show dist w c = r + dist z c
    have hw_dist_c : dist w c = r + dist z c := by
      simp only [w, u, dist_eq_norm]
      -- w - c = (z - c) + r • (‖z-c‖⁻¹ • (z - c)) = (1 + r * ‖z-c‖⁻¹) • (z - c)
      have h_eq : z + r • (‖z - c‖⁻¹ • (z - c)) - c = (1 + r * ‖z - c‖⁻¹) • (z - c) := by
        simp only [Complex.real_smul]; push_cast; ring
      rw [h_eq, Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hfactor_pos : 0 < 1 + r * ‖z - c‖⁻¹ := by positivity
      rw [abs_of_pos hfactor_pos]
      have hne : ‖z - c‖ ≠ 0 := norm_ne_zero_iff.mpr hzc_ne
      field_simp; ring
    linarith

/-- Distance between circleMap points at different radii. -/
private theorem dist_circleMap_radii (z : ℂ) (r r' : ℝ) (θ : ℝ) :
    dist (circleMap z r θ) (circleMap z r' θ) = |r - r'| := by
  simp only [circleMap, dist_eq_norm]
  rw [show z + ↑r * exp (↑θ * Complex.I) - (z + ↑r' * exp (↑θ * Complex.I))
      = ↑(r - r') * exp (↑θ * Complex.I) from by push_cast; ring]
  rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs]

private theorem harmonicOnNhd_mvp_closedball (f : ℂ → ℝ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hf_cont : ContinuousOn f (closedBall c R))
    (hf_harm : HarmonicOnNhd f (ball c R)) :
    ∀ z ∈ ball c R, ∀ r > 0, closedBall z r ⊆ closedBall c R →
      f z = circleAverage f z r := by
  intro z hz r hr hsub
  have hdist : dist z c < R := mem_ball.mp hz
  have hrd : r + dist z c ≤ R := dist_add_le_of_closedBall_subset hr hsub
  -- For any 0 < r' < r with closedBall z r' ⊂ ball c R, the MVP holds
  have hmvp_small : ∀ r' : ℝ, 0 < r' → r' < r → f z = circleAverage f z r' := by
    intro r' hr' hr'_lt
    have habs : |r'| = r' := abs_of_pos hr'
    have hcb_sub : closedBall z |r'| ⊆ ball c R := by
      rw [habs]; intro w hw
      rw [mem_closedBall] at hw; rw [mem_ball]
      calc dist w c ≤ dist w z + dist z c := dist_triangle w z c
        _ ≤ r' + dist z c := by linarith
        _ < r + dist z c := by linarith
        _ ≤ R := hrd
    have hharm_cb : HarmonicOnNhd f (closedBall z |r'|) := by
      intro w hw; exact hf_harm w (hcb_sub hw)
    exact (HarmonicOnNhd.circleAverage_eq hharm_cb).symm
  -- f z = circleAverage f z r by a limiting argument via uniform continuity
  -- Strategy: show dist (f z) (circleAverage f z r) ≤ ε for all ε > 0
  apply eq_of_forall_dist_le
  intro ε hε
  -- f is uniformly continuous on the compact set closedBall c R
  have huc := (isCompact_closedBall (x := c) (r := R)).uniformContinuousOn_of_continuous hf_cont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ_pos, huc_δ⟩ := huc ε hε
  -- Choose r' with 0 < r' < r and |r - r'| < δ
  set r' := r - min (δ / 2) (r / 2) with hr'_def
  have hmin_pos : 0 < min (δ / 2) (r / 2) := lt_min (by linarith) (by linarith)
  have hr'_pos : 0 < r' := by linarith [min_le_right (δ / 2) (r / 2)]
  have hr'_lt : r' < r := by linarith
  have hr_r'_lt : r - r' < δ := by
    have : r - r' = min (δ / 2) (r / 2) := by simp [hr'_def]
    linarith [min_le_left (δ / 2) (r / 2)]
  have hr_r'_abs : |r - r'| < δ := by rwa [abs_of_pos (by linarith)]
  -- f z = circleAverage f z r'
  have hfz_eq := hmvp_small r' hr'_pos hr'_lt
  -- Bound: dist (f z) (circleAverage f z r) = dist (circleAverage f z r') (circleAverage f z r)
  rw [Real.dist_eq, hfz_eq]
  -- Bound |circleAverage f z r' - circleAverage f z r| ≤ ε
  rw [circleAverage_def, circleAverage_def]
  -- f ∘ circleMap z r is integrable (continuous on compact interval)
  have hr_nn : (0 : ℝ) ≤ r := hr.le
  have hr'_nn : (0 : ℝ) ≤ r' := hr'_pos.le
  have hf_r_int : IntervalIntegrable (fun θ => f (circleMap z r θ)) MeasureTheory.volume 0 (2 * π) :=
    ((hf_cont.mono (sphere_subset_closedBall.trans hsub)).comp_continuous
      (continuous_circleMap z r) (fun θ => circleMap_mem_sphere z hr_nn θ)).intervalIntegrable 0 (2 * π)
  have hf_r'_int : IntervalIntegrable (fun θ => f (circleMap z r' θ)) MeasureTheory.volume 0 (2 * π) :=
    ((hf_cont.mono (sphere_subset_closedBall.trans
      ((closedBall_subset_closedBall hr'_lt.le).trans hsub))).comp_continuous
      (continuous_circleMap z r') (fun θ => circleMap_mem_sphere z hr'_nn θ)).intervalIntegrable 0 (2 * π)
  -- Rewrite: |(2π)⁻¹ • A - (2π)⁻¹ • B| = (2π)⁻¹ * |A - B| (for ℝ, smul = mul)
  rw [← smul_sub, smul_eq_mul, abs_mul,
      abs_of_pos (by positivity : (0:ℝ) < (2 * π)⁻¹)]
  -- Rewrite integral difference as integral of difference
  rw [(intervalIntegral.integral_sub hf_r'_int hf_r_int).symm]
  -- Pointwise bound: for each θ, ‖f(circleMap z r' θ) - f(circleMap z r θ)‖ ≤ ε
  have h_ptwise : ∀ θ ∈ Set.uIoc (0:ℝ) (2 * π),
      ‖f (circleMap z r' θ) - f (circleMap z r θ)‖ ≤ ε := by
    intro θ _
    rw [Real.norm_eq_abs, abs_sub_comm]
    have h_close : dist (circleMap z r θ) (circleMap z r' θ) < δ := by
      rw [dist_circleMap_radii]; exact hr_r'_abs
    have h1 : circleMap z r θ ∈ closedBall c R :=
      hsub (circleMap_mem_closedBall z hr_nn θ)
    have h2 : circleMap z r' θ ∈ closedBall c R :=
      (closedBall_subset_closedBall hr'_lt.le).trans hsub (circleMap_mem_closedBall z hr'_nn θ)
    exact (huc_δ _ h1 _ h2 h_close).le
  -- Apply interval integral bound: |∫ f| ≤ C * |b - a|, then (2π)⁻¹ * (ε * 2π) = ε
  rw [← Real.norm_eq_abs]
  calc (2 * π)⁻¹ * ‖∫ θ in (0:ℝ)..(2 * π), (f (circleMap z r' θ) - f (circleMap z r θ))‖
      ≤ (2 * π)⁻¹ * (ε * |2 * π - 0|) := by
        gcongr
        exact intervalIntegral.norm_integral_le_of_norm_le_const h_ptwise
    _ = ε := by
        rw [sub_zero, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
        field_simp

open Classical in
/-- A continuous function satisfying MVP on a closed ball equals
    its Poisson integral on the ball. -/
theorem mvp_eq_poissonIntegral (f : ℂ → ℝ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hcont : ContinuousOn f (closedBall c R))
    (hmvp : ∀ z ∈ ball c R, ∀ r > 0, closedBall z r ⊆ closedBall c R →
      f z = circleAverage f z r) :
    ∀ z ∈ ball c R, f z = poissonIntegralDisc f c R z := by
  -- Strategy: Define Pt = P[f] on ball, f on complement.
  -- h = f - Pt is continuous on closedBall, satisfies MVP, vanishes on sphere.
  -- By maximum principle: h = 0 on ball.
  set Pt : ℂ → ℝ := fun w => if w ∈ ball c R then poissonIntegralDisc f c R w else f w with hPt_def
  -- Pt is HarmonicOnNhd on ball c R
  have hP_harm : HarmonicOnNhd Pt (ball c R) := by
    intro w hw
    have : Pt =ᶠ[nhds w] poissonIntegralDisc f c R := by
      apply eventuallyEq_iff_exists_mem.mpr
      exact ⟨ball c R, isOpen_ball.mem_nhds hw,
        fun v hv => by simp only [hPt_def, if_pos hv]⟩
    exact (harmonicAt_congr_nhds this.symm).mp
      (poissonIntegral_harmonicOnNhd f c R hR (hcont.mono sphere_subset_closedBall) w hw)
  -- Pt is ContinuousOn on closedBall c R
  have hP_cont : ContinuousOn Pt (closedBall c R) := by
    intro w hw
    rcases (mem_closedBall.mp hw).eq_or_lt with h | h
    · -- w on sphere: Pt(w) = f(w), show continuity
      have hw_not_ball : ¬(w ∈ ball c R) := by rw [mem_ball]; linarith
      have hP_eq : Pt w = f w := by simp only [hPt_def, if_neg hw_not_ball]
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      rw [hP_eq]
      -- f is continuous at w within closedBall
      obtain ⟨δ₁, hδ₁_pos, hf_close⟩ :=
        Metric.continuousWithinAt_iff.mp (hcont.continuousWithinAt hw) (ε / 2) (half_pos hε)
      -- Poisson integral has boundary values
      have hP_bv := poissonIntegral_boundary_values f c R hR (hcont.mono sphere_subset_closedBall)
        w (mem_sphere.mpr h)
      rw [Metric.tendsto_nhdsWithin_nhds] at hP_bv
      obtain ⟨δ₂, hδ₂_pos, hP_close⟩ := hP_bv (ε / 2) (half_pos hε)
      refine ⟨min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, fun v hv_cb hv_dist => ?_⟩
      by_cases hv_ball : v ∈ ball c R
      · simp only [hPt_def, if_pos hv_ball]
        exact lt_trans (hP_close hv_ball (lt_of_lt_of_le hv_dist (min_le_right _ _))) (by linarith)
      · simp only [hPt_def, if_neg hv_ball]
        exact lt_trans (hf_close hv_cb (lt_of_lt_of_le hv_dist (min_le_left _ _))) (by linarith)
    · -- w in ball: Pt = P[f] locally, which is harmonic hence continuous
      exact (hP_harm w (mem_ball.mpr h)).1.continuousAt.continuousWithinAt
  -- Pt satisfies MVP on ball c R
  have hP_mvp : ∀ w ∈ ball c R, ∀ r > 0, closedBall w r ⊆ closedBall c R →
      Pt w = circleAverage Pt w r :=
    harmonicOnNhd_mvp_closedball Pt c R hR hP_cont hP_harm
  -- h = f - Pt is continuous on closedBall, satisfies MVP, vanishes on sphere
  set h : ℂ → ℝ := fun w => f w - Pt w with hh_def
  have hh_cont : ContinuousOn h (closedBall c R) := hcont.sub hP_cont
  have hh_mvp : ∀ w ∈ ball c R, ∀ r > 0, closedBall w r ⊆ closedBall c R →
      h w = circleAverage h w r := by
    intro w hw r' hr' hsub'
    have hf_eq := hmvp w hw r' hr' hsub'
    have hP_eq := hP_mvp w hw r' hr' hsub'
    simp only [hh_def]
    rw [hf_eq, hP_eq]
    -- circleAverage f - circleAverage Pt = circleAverage (f - Pt)
    have hr'_nn : (0 : ℝ) ≤ r' := hr'.le
    have hsphere_sub : sphere w r' ⊆ closedBall c R :=
      sphere_subset_closedBall.trans hsub'
    have hf_on_sphere : ContinuousOn f (sphere w r') := hcont.mono hsphere_sub
    have hf_circ : Continuous (fun θ => f (circleMap w r' θ)) :=
      hf_on_sphere.comp_continuous (continuous_circleMap w r')
        (fun θ => circleMap_mem_sphere w hr'_nn θ)
    have hf_int : IntervalIntegrable (fun θ => f (circleMap w r' θ))
        MeasureTheory.volume 0 (2 * π) := hf_circ.intervalIntegrable 0 (2 * π)
    have hP_on_sphere : ContinuousOn Pt (sphere w r') := hP_cont.mono hsphere_sub
    have hP_circ : Continuous (fun θ => Pt (circleMap w r' θ)) :=
      hP_on_sphere.comp_continuous (continuous_circleMap w r')
        (fun θ => circleMap_mem_sphere w hr'_nn θ)
    have hP_int : IntervalIntegrable (fun θ => Pt (circleMap w r' θ))
        MeasureTheory.volume 0 (2 * π) := hP_circ.intervalIntegrable 0 (2 * π)
    simp only [circleAverage_def, ← smul_sub,
      ← intervalIntegral.integral_sub hf_int hP_int]
  have hh_bdry : ∀ w, ‖w - c‖ = R → h w = 0 := by
    intro w hw_norm
    simp only [hh_def]
    have : ¬(w ∈ ball c R) := by
      rw [mem_ball, not_lt, dist_eq_norm]
      linarith
    simp only [hPt_def, if_neg this, sub_self]
  -- Apply maximum principle
  have hh_zero := mvp_zero_boundary_implies_zero h c R hR hh_cont hh_mvp hh_bdry
  -- Extract: f = P[f] on ball
  intro w hw
  have := hh_zero w hw
  simp only [hh_def, hPt_def, if_pos hw, sub_eq_zero] at this
  exact this

/-- **Main theorem**: Continuous functions satisfying MVP on a ball are harmonic.

    This is the key result connecting the mean value property to harmonicity.
    The proof goes through the Poisson integral representation:
    f = Re(Schwarz integral) → f is the real part of a holomorphic function → f is harmonic.

    This directly proves `harmonicOnNhd_of_mvp` without needing separate
    `smooth_of_mvp_ball` and `laplacian_zero_of_mvp` results. -/
theorem mvp_implies_harmonicOnNhd (f : ℂ → ℝ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hcont : ContinuousOn f (closedBall c R))
    (hmvp : ∀ z ∈ ball c R, ∀ r > 0, closedBall z r ⊆ closedBall c R →
      f z = circleAverage f z r) :
    HarmonicOnNhd f (ball c R) := by
  intro z hz
  -- f = P[f] on ball
  have hfP := mvp_eq_poissonIntegral f c R hR hcont hmvp
  -- P[f] is harmonic on ball
  have hP_harm := poissonIntegral_harmonicOnNhd f c R hR
    (hcont.mono (sphere_subset_closedBall))
  -- f = P[f] at z, so f is harmonic at z
  have hfz := hfP z hz
  -- HarmonicAt for P[f] at z
  have hPz := hP_harm z hz
  -- f =ᶠ[𝓝 z] P[f] on a neighborhood
  have hfeq : f =ᶠ[nhds z] poissonIntegralDisc f c R := by
    apply eventuallyEq_iff_exists_mem.mpr
    use ball c R, isOpen_ball.mem_nhds hz
    intro w hw
    exact hfP w hw
  -- Transfer harmonicity via local equality
  exact (harmonicAt_congr_nhds hfeq.symm).mp hPz

/-- Corollary: MVP implies smoothness (C^∞). -/
theorem mvp_implies_contDiffOn (f : ℂ → ℝ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hcont : ContinuousOn f (closedBall c R))
    (hmvp : ∀ z ∈ ball c R, ∀ r > 0, closedBall z r ⊆ closedBall c R →
      f z = circleAverage f z r) :
    ContDiffOn ℝ ⊤ f (ball c R) := by
  -- f is harmonic on ball → analytic → C^∞
  have hharm := mvp_implies_harmonicOnNhd f c R hR hcont hmvp
  -- HarmonicAt → AnalyticAt ℝ → ContDiffAt ℝ ⊤
  intro z hz
  exact (HarmonicAt.analyticAt (hharm z hz)).contDiffAt.contDiffWithinAt

end RiemannSurfaces.Analytic.Infrastructure
