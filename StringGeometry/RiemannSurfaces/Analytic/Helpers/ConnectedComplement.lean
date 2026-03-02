import StringGeometry.RiemannSurfaces.Analytic.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

/-!
# Connected Complement: Removing Finite Sets from Riemann Surfaces

Removing finitely many points from a connected Riemann surface preserves connectedness.

## Proof outline

By induction on |S|. The key step is: removing a single point from a connected
open set in a Riemann surface preserves preconnectedness, using:
1. Punctured balls in ℂ are preconnected (polar coordinates)
2. Chart neighborhoods transfer this to the manifold
3. The "clopen extension" argument: if X \ {p} = A ⊔ B with A, B open disjoint,
   extend one side through p using W to get a partition of X, contradicting X connected.
-/

namespace RiemannSurfaces.Analytic

open Complex Topology
open scoped Manifold Topology

/-- The rank of ℂ as an ℝ-module is > 1. -/
theorem complex_rank_gt_one : 1 < Module.rank ℝ ℂ :=
  by
    simpa using (Complex.rank_real_complex ▸ Nat.one_lt_ofNat)

/-- In ℂ, the complement of a finite set is path-connected. -/
theorem complex_compl_finite_pathConnected (S : Set ℂ) (hS : S.Finite) :
    IsPathConnected Sᶜ :=
  hS.countable.isPathConnected_compl_of_one_lt_rank complex_rank_gt_one

/-- In ℂ, the complement of a singleton is path-connected. -/
theorem complex_compl_singleton_pathConnected (z : ℂ) :
    IsPathConnected {z}ᶜ :=
  complex_compl_finite_pathConnected {z} (Set.finite_singleton z)

/-! ## Punctured ball -/

/-- A punctured ball in ℂ is preconnected. Proved via polar coordinates:
    ball(z₀, ε) \ {z₀} is the continuous image of the connected set (0,ε) × ℝ
    under the map (r,θ) ↦ z₀ + r·exp(iθ). -/
theorem puncturedBall_isPreconnected (z₀ : ℂ) {ε : ℝ} (hε : 0 < ε) :
    IsPreconnected (Metric.ball z₀ ε \ {z₀}) := by
  -- The set (0,ε) × ℝ is connected (product of connected sets)
  -- and maps continuously and surjectively onto the punctured ball via polar coordinates.
  set f : ℝ × ℝ → ℂ := fun p => z₀ + ↑p.1 * exp (Complex.I * ↑p.2)
  set D : Set (ℝ × ℝ) := Set.Ioo 0 ε ×ˢ Set.univ
  have hD_conn : IsPreconnected D :=
    (convex_Ioo 0 ε).isPreconnected.prod isPreconnected_univ
  have hf_cont : Continuous f := by
    apply Continuous.add continuous_const
    exact (Complex.continuous_ofReal.comp continuous_fst).mul
      (Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp continuous_snd)))
  -- Show f '' D = ball \ {z₀}, then transfer preconnectedness
  suffices himg : f '' D = Metric.ball z₀ ε \ {z₀} by
    rw [← himg]; exact hD_conn.image f hf_cont.continuousOn
  apply Set.eq_of_subset_of_subset
  · -- f '' D ⊆ ball \ {z₀}
    rintro _ ⟨⟨r, θ⟩, ⟨hr_mem, _⟩, rfl⟩
    simp only [Set.mem_Ioo] at hr_mem
    refine Set.mem_diff_singleton.mpr ⟨?_, ?_⟩
    · -- dist < ε
      rw [Metric.mem_ball, dist_eq,
        show f (r, θ) - z₀ = ↑r * exp (Complex.I * ↑θ) by simp [f],
        norm_mul, Complex.norm_real, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I,
        mul_one, Real.norm_of_nonneg (le_of_lt hr_mem.1)]
      exact hr_mem.2
    · -- ≠ z₀
      intro h
      have : f (r, θ) - z₀ = 0 := sub_eq_zero.mpr h
      simp only [f] at this
      rw [show z₀ + ↑r * exp (Complex.I * ↑θ) - z₀ = ↑r * exp (Complex.I * ↑θ) by ring] at this
      rcases mul_eq_zero.mp this with hr0 | hexp0
      · exact absurd (Complex.ofReal_eq_zero.mp hr0) (ne_of_gt hr_mem.1)
      · exact absurd hexp0 (Complex.exp_ne_zero _)
  · -- ball \ {z₀} ⊆ f '' D (polar decomposition)
    intro w hw
    obtain ⟨hw_ball, hw_ne⟩ := Set.mem_diff_singleton.mp hw
    set δ := w - z₀ with hδ_def
    have hδ_ne : δ ≠ 0 := sub_ne_zero.mpr hw_ne
    have hr_pos : 0 < ‖δ‖ := norm_pos_iff.mpr hδ_ne
    have hr_lt : ‖δ‖ < ε := by
      rwa [Metric.mem_ball, dist_eq, ← hδ_def] at hw_ball
    refine ⟨(‖δ‖, Complex.arg δ), ⟨⟨hr_pos, hr_lt⟩, Set.mem_univ _⟩, ?_⟩
    -- z₀ + ‖δ‖ * exp(I * arg(δ)) = w
    show z₀ + ↑‖δ‖ * exp (Complex.I * ↑(Complex.arg δ)) = w
    rw [mul_comm Complex.I ↑(Complex.arg δ), Complex.norm_mul_exp_arg_mul_I]
    simp [hδ_def]

/-- A punctured ball in ℂ is nonempty (for ε > 0). -/
private theorem puncturedBall_nonempty (z₀ : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (Metric.ball z₀ ε \ {z₀}).Nonempty :=
  ⟨z₀ + ε / 2, by
    simp only [Set.mem_diff, Metric.mem_ball, Set.mem_singleton_iff]
    constructor
    · rw [dist_eq, add_sub_cancel_left,
        show (↑ε / 2 : ℂ) = ↑(ε / 2) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ ε / 2)]
      linarith
    · intro h; have := congr_arg (· - z₀) h; simp at this; linarith⟩

/-! ## Removing a point from a connected open set -/

variable {RS : RiemannSurface}

/-- In a Riemann surface, every point has a chart neighborhood W inside any given
    open set G, such that W \ {p} is preconnected and nonempty. -/
private theorem exists_preconnected_punctured_nhd
    (p : RS.carrier) (G : Set RS.carrier)
    (hG : @IsOpen RS.carrier RS.topology G) (hpG : p ∈ G) :
    ∃ W : Set RS.carrier, @IsOpen RS.carrier RS.topology W ∧ p ∈ W ∧ W ⊆ G ∧
      @IsPreconnected RS.carrier RS.topology (W \ {p}) ∧ (W \ {p}).Nonempty := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  haveI := RS.t2
  -- Use the extended chart at p
  set e := extChartAt 𝓘(ℂ, ℂ) p with he_def
  have he_src : p ∈ e.source := mem_extChartAt_source p
  -- Find ε: ball(e p, ε) ⊆ e.target ∩ e.symm ⁻¹' G
  have he_tgt_nhds : e.target ∈ nhds (e p) := extChartAt_target_mem_nhds p
  have he_symm_cont' : ContinuousAt e.symm (e p) := continuousAt_extChartAt_symm p
  have he_preimage : e.symm ⁻¹' G ∈ nhds (e p) := by
    apply he_symm_cont'.preimage_mem_nhds
    have : e.symm (e p) = p := e.left_inv he_src
    rw [this]; exact hG.mem_nhds hpG
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_ball.mem_iff.mp
    (Filter.inter_mem he_tgt_nhds he_preimage)
  -- hball : ball(e p, ε) ⊆ e.target ∩ e.symm ⁻¹' G
  have hball_tgt : Metric.ball (e p) ε ⊆ e.target := fun z hz => (hball hz).1
  have hball_G : ∀ z ∈ Metric.ball (e p) ε, e.symm z ∈ G := fun z hz => (hball hz).2
  -- W = e.source ∩ e ⁻¹'(ball(e p, ε))
  set W := e.source ∩ e ⁻¹' Metric.ball (e p) ε with hW_def
  refine ⟨W, ?_, ?_, ?_, ?_, ?_⟩
  · -- W is open
    exact (continuousOn_extChartAt p).isOpen_inter_preimage
      (isOpen_extChartAt_source p) Metric.isOpen_ball
  · -- p ∈ W
    exact ⟨he_src, Metric.mem_ball_self hε⟩
  · -- W ⊆ G
    intro x ⟨hx_src, hx_ball⟩
    have h1 : e.symm (e x) ∈ G := hball_G (e x) hx_ball
    rwa [e.left_inv hx_src] at h1
  · -- W \ {p} is preconnected
    -- Strategy: show W \ {p} = e.symm '' (ball \ {e p}), transfer preconnectedness
    have himg_sub : e.symm '' (Metric.ball (e p) ε \ {e p}) ⊆ W \ {p} := by
      rintro _ ⟨z, ⟨hz_ball, hz_ne⟩, rfl⟩
      constructor
      · constructor
        · exact e.map_target (hball_tgt hz_ball)
        · show e (e.symm z) ∈ Metric.ball (e p) ε
          rw [e.right_inv (hball_tgt hz_ball)]; exact hz_ball
      · intro h
        apply hz_ne; rw [Set.mem_singleton_iff] at h ⊢
        rw [← e.right_inv (hball_tgt hz_ball), h]
    have hW_sub_img : W \ {p} ⊆ e.symm '' (Metric.ball (e p) ε \ {e p}) := by
      intro x ⟨⟨hx_src, hx_ball⟩, hx_ne⟩
      refine ⟨e x, ⟨hx_ball, ?_⟩, e.left_inv hx_src⟩
      intro h; apply hx_ne; rw [Set.mem_singleton_iff] at h ⊢
      rw [← e.left_inv hx_src, h]; exact e.left_inv he_src
    have himg_eq : e.symm '' (Metric.ball (e p) ε \ {e p}) = W \ {p} :=
      Set.eq_of_subset_of_subset himg_sub hW_sub_img
    rw [← himg_eq]
    exact (puncturedBall_isPreconnected (e p) hε).image e.symm
      ((continuousOn_extChartAt_symm p).mono (Set.diff_subset.trans hball_tgt))
  · -- W \ {p} nonempty
    have : (Metric.ball (e p) ε \ {e p}).Nonempty := puncturedBall_nonempty (e p) hε
    obtain ⟨z, hz_ball, hz_ne⟩ := this
    exact ⟨e.symm z, by
      constructor
      · exact ⟨e.map_target (hball_tgt hz_ball), by
          show e (e.symm z) ∈ Metric.ball (e p) ε
          rw [e.right_inv (hball_tgt hz_ball)]; exact hz_ball⟩
      · intro h
        apply hz_ne; rw [Set.mem_singleton_iff] at h ⊢
        rw [← e.right_inv (hball_tgt hz_ball), h]⟩

/-- Removing a point from a preconnected open subset of a Riemann surface preserves
    preconnectedness. Uses the "clopen extension" argument. -/
private theorem preconnected_remove_point
    (X : Set RS.carrier) (hX_open : @IsOpen RS.carrier RS.topology X)
    (hX_conn : @IsPreconnected RS.carrier RS.topology X)
    (p : RS.carrier) (hp : p ∈ X)
    (W : Set RS.carrier) (hW_open : @IsOpen RS.carrier RS.topology W)
    (hW_sub : W ⊆ X) (hp_W : p ∈ W)
    (hW_punct : @IsPreconnected RS.carrier RS.topology (W \ {p}))
    (_hW_ne : (W \ {p}).Nonempty) :
    @IsPreconnected RS.carrier RS.topology (X \ {p}) := by
  letI := RS.topology
  haveI := RS.t2
  intro U V hU hV hcover hUne hVne
  -- Need: (X \ {p}) ∩ (U ∩ V) nonempty
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  -- W \ {p} ⊆ X \ {p} ⊆ U ∪ V
  have hWp_sub : W \ {p} ⊆ X \ {p} := Set.diff_subset_diff_left hW_sub
  -- W \ {p} ⊆ U or W \ {p} ⊆ V (by preconnectedness of W \ {p})
  have hWUV : W \ {p} ⊆ U ∨ W \ {p} ⊆ V := by
    by_contra h
    push_neg at h
    obtain ⟨hnotU, hnotV⟩ := h
    rw [Set.not_subset] at hnotU hnotV
    obtain ⟨a, haW, haU⟩ := hnotU
    obtain ⟨b, hbW, hbV⟩ := hnotV
    obtain ⟨x, hxW, hxUV⟩ := hW_punct U V hU hV (hWp_sub.trans hcover)
      ⟨b, hbW, (hcover (hWp_sub hbW)).resolve_right hbV⟩
      ⟨a, haW, (hcover (hWp_sub haW)).resolve_left haU⟩
    have : x ∈ X \ {p} ∩ (U ∩ V) := ⟨hWp_sub hxW, hxUV⟩
    simp [hempty] at this
  rcases hWUV with hWU | hWV
  · -- Case W \ {p} ⊆ U. Define A' = ((X \ {p}) ∩ U) ∪ {p}, B = (X \ {p}) ∩ V
    set A' := (X \ {p}) ∩ U ∪ {p}
    set B := (X \ {p}) ∩ V
    -- A' is open: each x ∈ A' has an open neighborhood in A'
    have hA'_open : IsOpen A' := by
      rw [isOpen_iff_forall_mem_open]
      intro x hx
      rcases hx with ⟨⟨hxX, hxp⟩, hxU⟩ | hxp
      · -- x ∈ (X \ {p}) ∩ U: use X ∩ U ∩ {p}ᶜ as neighborhood
        refine ⟨X ∩ U ∩ {p}ᶜ,
          fun y ⟨⟨hyX, hyU⟩, hyp⟩ => Or.inl ⟨⟨hyX, hyp⟩, hyU⟩,
          hX_open.inter hU |>.inter isClosed_singleton.isOpen_compl,
          ⟨⟨hxX, hxU⟩, hxp⟩⟩
      · -- x = p: use W as neighborhood (W ⊆ A' since W \ {p} ⊆ U ∩ (X \ {p}) and p ∈ A')
        rw [Set.mem_singleton_iff.mp hxp]
        refine ⟨W, fun y hyW => ?_, hW_open, hp_W⟩
        by_cases hyp : y = p
        · exact Or.inr (Set.mem_singleton_iff.mpr hyp)
        · exact Or.inl ⟨⟨hW_sub hyW, hyp⟩, hWU ⟨hyW, hyp⟩⟩
    -- B is open
    have hB_open : IsOpen B :=
      (hX_open.inter isClosed_singleton.isOpen_compl).inter hV
    -- X ⊆ A' ∪ B
    have hX_cover : X ⊆ A' ∪ B := by
      intro x hx
      by_cases hxp : x = p
      · left; right; exact Set.mem_singleton_iff.mpr hxp
      · have hxXp : x ∈ X \ {p} := ⟨hx, hxp⟩
        rcases hcover hxXp with hxU | hxV
        · left; left; exact ⟨hxXp, hxU⟩
        · right; exact ⟨hxXp, hxV⟩
    -- X ∩ A' nonempty
    have hA'ne : (X ∩ A').Nonempty := by
      obtain ⟨x, hxXp, hxU⟩ := hUne
      exact ⟨x, hxXp.1, Or.inl ⟨hxXp, hxU⟩⟩
    -- X ∩ B nonempty
    have hBne : (X ∩ B).Nonempty := by
      obtain ⟨x, hxXp, hxV⟩ := hVne
      exact ⟨x, hxXp.1, hxXp, hxV⟩
    -- A' ∩ B = ∅
    have hA'B_disj : A' ∩ B = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      intro ⟨hxA', hxB⟩
      have ⟨⟨_, hxp⟩, hxV⟩ := hxB
      rcases hxA' with ⟨_, hxU⟩ | hxeq
      · exact hempty.subset ⟨⟨hxB.1.1, hxp⟩, hxU, hxV⟩
      · exact hxp (Set.mem_singleton_iff.mp hxeq)
    -- By X preconnected: X ∩ A' ∩ B nonempty. But A' ∩ B = ∅. Contradiction.
    have := hX_conn A' B hA'_open hB_open hX_cover hA'ne hBne
    rw [hA'B_disj, Set.inter_empty] at this
    exact this.ne_empty rfl
  · -- Symmetric case: W \ {p} ⊆ V
    set A := (X \ {p}) ∩ U
    set B' := (X \ {p}) ∩ V ∪ {p}
    have hA_open : IsOpen A :=
      (hX_open.inter isClosed_singleton.isOpen_compl).inter hU
    have hB'_open : IsOpen B' := by
      rw [isOpen_iff_forall_mem_open]
      intro x hx
      rcases hx with ⟨⟨hxX, hxp⟩, hxV⟩ | hxp
      · refine ⟨X ∩ V ∩ {p}ᶜ,
          fun y ⟨⟨hyX, hyV⟩, hyp⟩ => Or.inl ⟨⟨hyX, hyp⟩, hyV⟩,
          hX_open.inter hV |>.inter isClosed_singleton.isOpen_compl,
          ⟨⟨hxX, hxV⟩, hxp⟩⟩
      · rw [Set.mem_singleton_iff.mp hxp]
        refine ⟨W, fun y hyW => ?_, hW_open, hp_W⟩
        by_cases hyp : y = p
        · exact Or.inr (Set.mem_singleton_iff.mpr hyp)
        · exact Or.inl ⟨⟨hW_sub hyW, hyp⟩, hWV ⟨hyW, hyp⟩⟩
    have hX_cover : X ⊆ A ∪ B' := by
      intro x hx
      by_cases hxp : x = p
      · right; right; exact Set.mem_singleton_iff.mpr hxp
      · have hxXp : x ∈ X \ {p} := ⟨hx, hxp⟩
        rcases hcover hxXp with hxU | hxV
        · left; exact ⟨hxXp, hxU⟩
        · right; left; exact ⟨hxXp, hxV⟩
    have hAne : (X ∩ A).Nonempty := by
      obtain ⟨x, hxXp, hxU⟩ := hUne
      exact ⟨x, hxXp.1, hxXp, hxU⟩
    have hB'ne : (X ∩ B').Nonempty := by
      obtain ⟨x, hxXp, hxV⟩ := hVne
      exact ⟨x, hxXp.1, Or.inl ⟨hxXp, hxV⟩⟩
    have hAB'_disj : A ∩ B' = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      intro ⟨hxA, hxB'⟩
      have ⟨⟨_, hxp⟩, hxU⟩ := hxA
      rcases hxB' with ⟨_, hxV⟩ | hxeq
      · exact hempty.subset ⟨⟨hxA.1.1, hxp⟩, hxU, hxV⟩
      · exact hxp (Set.mem_singleton_iff.mp hxeq)
    have := hX_conn A B' hA_open hB'_open hX_cover hAne hB'ne
    rw [hAB'_disj, Set.inter_empty] at this
    exact this.ne_empty rfl

/-! ## Main theorems -/

/-- The complement of a finite subset of a Riemann surface is nonempty. -/
theorem rs_compl_finite_nonempty (S : Set RS.carrier) (hS : S.Finite) :
    @Set.Nonempty RS.carrier Sᶜ := by
  letI := RS.topology
  obtain ⟨a, ha⟩ := hS.exists_notMem
  exact ⟨a, ha⟩

/-- The complement of a finite subset of a Riemann surface is connected. -/
theorem rs_compl_finite_isConnected (S : Set RS.carrier) (hS : S.Finite) :
    @IsConnected RS.carrier RS.topology Sᶜ := by
  -- Induction on the finite set S
  induction S, hS using Set.Finite.induction_on with
  | empty => -- Base case: S = ∅, Sᶜ = univ
    letI := RS.topology
    haveI := RS.connected
    simp only [Set.compl_empty]
    exact isConnected_univ
  | @insert p S' hp hS' ih => -- Inductive step: S = insert p S', with p ∉ S'
    letI := RS.topology
    letI := RS.chartedSpace
    haveI := RS.isManifold
    haveI := RS.t2
    haveI := RS.secondCountable
    haveI := RS.connected
    -- (insert p S')ᶜ = S'ᶜ \ {p}
    have hcompl : (insert p S')ᶜ = S'ᶜ \ {p} := by
      ext x; simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_diff,
        Set.mem_singleton_iff, not_or]; tauto
    rw [hcompl]
    -- S'ᶜ is open (S' finite → S' closed → S'ᶜ open)
    have hS'_closed : IsClosed S' := hS'.isClosed
    have hS'c_open : IsOpen S'ᶜ := hS'_closed.isOpen_compl
    -- S'ᶜ is connected by IH
    -- p ∈ S'ᶜ (since p ∉ S')
    have hp_mem : p ∈ S'ᶜ := Set.mem_compl hp
    -- Get a chart neighborhood W of p inside S'ᶜ
    obtain ⟨W, hW_open, hpW, hW_sub, hW_punct, hW_ne⟩ :=
      exists_preconnected_punctured_nhd p S'ᶜ hS'c_open hp_mem
    constructor
    · -- Nonemptiness
      exact hW_ne.mono (Set.diff_subset_diff_left hW_sub)
    · -- Preconnectedness via the clopen extension argument
      exact preconnected_remove_point S'ᶜ hS'c_open ih.isPreconnected p hp_mem
        W hW_open hW_sub hpW hW_punct hW_ne

/-- The complement of a singleton in a Riemann surface is connected. -/
theorem rs_compl_singleton_isConnected (p : RS.carrier) :
    @IsConnected RS.carrier RS.topology ({p}ᶜ) :=
  rs_compl_finite_isConnected {p} (Set.finite_singleton p)

/-- The complement of a finite set in a Riemann surface is preconnected. -/
theorem rs_compl_finite_isPreconnected (S : Set RS.carrier) (hS : S.Finite) :
    @IsPreconnected RS.carrier RS.topology Sᶜ := by
  letI := RS.topology
  exact (rs_compl_finite_isConnected S hS).isPreconnected

end RiemannSurfaces.Analytic
