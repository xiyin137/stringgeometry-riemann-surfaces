import StringGeometry.RiemannSurfaces.Analytic.Helpers.ArgumentPrinciple.Foundation

namespace RiemannSurfaces.Analytic

open Complex Topology Classical Filter
open scoped Manifold Topology
open scoped BigOperators

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
  letI := CRS.toRiemannSurface.topology
  letI := CRS.toRiemannSurface.chartedSpace
  haveI := CRS.toRiemannSurface.isManifold
  haveI := CRS.toRiemannSurface.t2
  haveI : CompactSpace CRS.toRiemannSurface.carrier := CRS.compact
  rw [IsLocallyConstant.iff_eventually_eq]
  intro c₀
  set f₀ : CRS.toRiemannSurface.carrier → ℂ := fun x => f x - c₀
  have hf₀ : IsChartMeromorphic (RS := CRS.toRiemannSurface) f₀ := by
    simpa [f₀] using chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c₀ hf
  have hsupp₀ : (chartOrderSupport (RS := CRS.toRiemannSurface) f₀).Finite := by
    simpa [f₀] using chartOrderSupport_sub_const_finite CRS f c₀ hf
  obtain ⟨U, hU_mem_open, hU_disj⟩ := hsupp₀.t2_separation
  have hlocal :
      ∀ q ∈ chartOrderSupport (RS := CRS.toRiemannSurface) f₀,
        ∃ r > 0, r ≤ 1 ∧
          (∀ z, ‖z - chartPt (RS := CRS.toRiemannSurface) q‖ < r →
            z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target ∧
            (extChartAt 𝓘(ℂ, ℂ) q).symm z ∈ U q) ∧
          ∃ ε > 0, ∀ c : ℂ, ‖c - c₀‖ < ε →
          ∃ S : Finset ℂ,
            (∀ z ∈ S, ‖z - chartPt (RS := CRS.toRiemannSurface) q‖ < r) ∧
            (∀ z, ‖z - chartPt (RS := CRS.toRiemannSurface) q‖ < r →
              meromorphicOrderAt
                (fun w => chartRep (RS := CRS.toRiemannSurface) f q w - c) z ≠ 0 →
              meromorphicOrderAt
                (fun w => chartRep (RS := CRS.toRiemannSurface) f q w - c) z ≠ ⊤ →
              z ∈ S) ∧
            S.sum (fun z => (meromorphicOrderAt
              (fun w => chartRep (RS := CRS.toRiemannSurface) f q w - c) z).getD 0) =
              (chartOrderAt (RS := CRS.toRiemannSurface) f₀ q).getD 0 := by
    intro q hq
    set e_q := extChartAt 𝓘(ℂ, ℂ) q
    have hU_nhds : U q ∈ @nhds _ CRS.toRiemannSurface.topology q :=
      (hU_mem_open q).2.mem_nhds (hU_mem_open q).1
    have hpreU : e_q.symm ⁻¹' U q ∈ nhds (chartPt (RS := CRS.toRiemannSurface) q) := by
      have hU_nhds' : U q ∈ nhds (e_q.symm (chartPt (RS := CRS.toRiemannSurface) q)) := by
        simpa [e_q, chartPt] using hU_nhds
      exact (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) q).preimage_mem_nhds hU_nhds'
    have htgt_nhds : e_q.target ∈ nhds (chartPt (RS := CRS.toRiemannSurface) q) := by
      simpa [e_q, chartPt] using extChartAt_target_mem_nhds (I := 𝓘(ℂ, ℂ)) q
    obtain ⟨ρq, hρq_pos, hρq_sub⟩ := Metric.nhds_basis_ball.mem_iff.mp
      (Filter.inter_mem htgt_nhds hpreU)
    set ρ : ℝ := min 1 ρq with hρ_def
    have hρ_pos : 0 < ρ := by
      exact lt_min zero_lt_one hρq_pos
    obtain ⟨r, hr_pos, hr_le_ρ, ε, hε_pos, hloc⟩ :=
      support_local_chart_sum_constant (RS := CRS.toRiemannSurface) c₀
        (hf := hf) (q := q) (hne_top q) hq.1 hq.2 hρ_pos
    refine ⟨r, hr_pos, le_trans hr_le_ρ (min_le_left _ _), ?_, ε, hε_pos, hloc⟩
    intro z hz
    have hzρq : ‖z - chartPt (RS := CRS.toRiemannSurface) q‖ < ρq := by
      exact lt_of_lt_of_le hz (le_trans hr_le_ρ (min_le_right _ _))
    have hz_ball : z ∈ Metric.ball (chartPt (RS := CRS.toRiemannSurface) q) ρq := by
      simpa [Metric.mem_ball, dist_eq_norm] using hzρq
    exact hρq_sub hz_ball
  by_cases htop₀ : ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) f₀ q = ⊤
  · -- Degenerate branch: `f - c₀` is locally zero everywhere.
    -- Then `chartOrderSum(f-c)` vanishes for every `c`.
    have hsum_zero :
        ∀ c : ℂ,
          chartOrderSum CRS (fun x => f x - c)
            (chartMeromorphic_sub_const c hf)
            (chartOrderSupport_sub_const_finite CRS f c hf) = 0 := by
      intro c
      by_cases hc : c = c₀
      · subst c
        have hsupp_empty : chartOrderSupport (RS := CRS.toRiemannSurface) f₀ = ∅ := by
          ext q
          simp [chartOrderSupport, htop₀ q]
        have hsupp_empty' :
            chartOrderSupport (RS := CRS.toRiemannSurface) (fun x => f x - c₀) = ∅ := by
          simpa [f₀] using hsupp_empty
        simp only [chartOrderSum]
        rw [show (chartOrderSupport_sub_const_finite CRS f c₀ hf).toFinset = ∅ from by
              rw [← Finset.val_eq_zero]
              ext q
              simp [hsupp_empty']]
        simp
      · set d : ℂ := c - c₀ with hd_def
        have hd_ne : d ≠ 0 := by simpa [d, hd_def, sub_eq_zero] using hc
        have hfun : ∀ x, f x - c = f₀ x - d := by
          intro x
          simp [f₀, d]
        have hord_zero_aux :
            ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f₀ x - d) q = 0 := by
          intro q
          simp only [chartOrderAt, chartRep_sub_const]
          have hrep : (fun z => chartRep (RS := CRS.toRiemannSurface) f₀ q z - d) =
              (fun _ => -d) + chartRep (RS := CRS.toRiemannSurface) f₀ q := by
            ext z
            simp [Pi.add_apply, sub_eq_add_neg, add_comm]
          rw [hrep]
          have htop_chart :
              meromorphicOrderAt (chartRep (RS := CRS.toRiemannSurface) f₀ q)
                (chartPt (RS := CRS.toRiemannSurface) q) = ⊤ := by
            simpa [chartOrderAt] using htop₀ q
          have hlt :
              meromorphicOrderAt (fun _ : ℂ => -d) (chartPt (RS := CRS.toRiemannSurface) q) <
                meromorphicOrderAt (chartRep (RS := CRS.toRiemannSurface) f₀ q)
                  (chartPt (RS := CRS.toRiemannSurface) q) := by
            have hconst0 :
                meromorphicOrderAt (fun _ : ℂ => -d) (chartPt (RS := CRS.toRiemannSurface) q) = 0 := by
              rw [meromorphicOrderAt_const]
              simp [hd_ne]
            rw [hconst0, htop_chart]
            have h0top : ((0 : WithTop ℤ) < (⊤ : WithTop ℤ)) := by
              exact lt_top_iff_ne_top.mpr (by simp)
            exact h0top
          rw [meromorphicOrderAt_add_eq_left_of_lt (hf₀ q) hlt, meromorphicOrderAt_const]
          simp [hd_ne]
        have hord_zero :
            ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) q = 0 := by
          intro q
          rw [chartOrderAt_congr' (RS := CRS.toRiemannSurface) (f := fun x => f x - c)
            (g := fun x => f₀ x - d) hfun q]
          exact hord_zero_aux q
        have hsupp_empty_c :
            chartOrderSupport (RS := CRS.toRiemannSurface) (fun x => f x - c) = ∅ := by
          ext q
          simp [chartOrderSupport, hord_zero q]
        simp only [chartOrderSum]
        rw [show (chartOrderSupport_sub_const_finite CRS f c hf).toFinset = ∅ from by
              rw [← Finset.val_eq_zero]
              ext q
              simp [hsupp_empty_c]]
        simp
    exact Filter.Eventually.of_forall (fun c => by
      rw [hsum_zero c, hsum_zero c₀])
  · push_neg at htop₀
    obtain ⟨q₁, hq₁_ne_top⟩ := htop₀
    have hne_top₀ : ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) f₀ q ≠ ⊤ := by
      intro q
      exact chartOrderAt_ne_top_of_ne_top_somewhere (RS := CRS.toRiemannSurface)
        f₀ hf₀ q₁ hq₁_ne_top q
    set K : Set CRS.toRiemannSurface.carrier :=
      (⋃ q ∈ chartOrderSupport (RS := CRS.toRiemannSurface) f₀, U q)ᶜ with hK_def
    have hK_compact : @IsCompact _ CRS.toRiemannSurface.topology K := by
      have h_union_open :
          IsOpen (⋃ q ∈ chartOrderSupport (RS := CRS.toRiemannSurface) f₀, U q) := by
        refine isOpen_iUnion ?_
        intro q
        refine isOpen_iUnion ?_
        intro _hq
        exact (hU_mem_open q).2
      have hK_closed : IsClosed K := by
        simpa [K, hK_def] using h_union_open.isClosed_compl
      exact hK_closed.isCompact
    have hK_no_support :
        ∀ q ∈ K, chartOrderAt (RS := CRS.toRiemannSurface) f₀ q = 0 := by
      intro q hqK
      have hq_not_union : q ∉ ⋃ q' ∈ chartOrderSupport (RS := CRS.toRiemannSurface) f₀, U q' := by
        simpa [K, hK_def] using hqK
      have hq_not_supp : q ∉ chartOrderSupport (RS := CRS.toRiemannSurface) f₀ := by
        intro hq_supp
        exact hq_not_union (Set.mem_iUnion₂.mpr ⟨q, hq_supp, (hU_mem_open q).1⟩)
      have hnot :
          ¬ (chartOrderAt (RS := CRS.toRiemannSurface) f₀ q ≠ 0 ∧
            chartOrderAt (RS := CRS.toRiemannSurface) f₀ q ≠ ⊤) := by
        simpa [chartOrderSupport] using hq_not_supp
      by_cases hq0 : chartOrderAt (RS := CRS.toRiemannSurface) f₀ q = 0
      · exact hq0
      · have hq_top : chartOrderAt (RS := CRS.toRiemannSurface) f₀ q = ⊤ := by
          by_contra hq_ne_top
          exact hnot ⟨hq0, hq_ne_top⟩
        exact (hne_top₀ q hq_top).elim
    have hK_no_pole :
        ∀ q ∈ K, (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f q := by
      intro q hqK
      have hnonneg_sub : (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f₀ q := by
        simpa [hK_no_support q hqK]
      exact (chartOrderAt_sub_const_nonneg_iff (RS := CRS.toRiemannSurface)
        (f := f) (p := q) c₀).1 hnonneg_sub
    obtain ⟨εK, hεK_pos, hεK⟩ :=
      no_support_on_compact_near_c₀ CRS f hf hne_top c₀ K hK_compact hK_no_pole hK_no_support
    have hsupport_subset :
        ∀ c : ℂ, ‖c - c₀‖ < εK →
          chartOrderSupport (RS := CRS.toRiemannSurface) (fun x => f x - c) ⊆
            ⋃ q ∈ chartOrderSupport (RS := CRS.toRiemannSurface) f₀, U q := by
      intro c hc p hp
      by_contra hp_not_union
      have hpK : p ∈ K := by
        simpa [K, hK_def] using hp_not_union
      have hord0 : chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p = 0 :=
        hεK c hc p hpK
      exact hp.1 hord0
    by_cases hsupp₀_empty : chartOrderSupport (RS := CRS.toRiemannSurface) f₀ = ∅
    · have hsum_c₀ :
          chartOrderSum CRS (fun x => f x - c₀)
            (chartMeromorphic_sub_const c₀ hf)
            (chartOrderSupport_sub_const_finite CRS f c₀ hf) = 0 := by
        simp only [chartOrderSum]
        rw [show (chartOrderSupport_sub_const_finite CRS f c₀ hf).toFinset = ∅ from by
              rw [← Finset.val_eq_zero]
              ext q
              simp [f₀, hsupp₀_empty]]
        simp
      refine Filter.mem_of_superset (Metric.ball_mem_nhds c₀ hεK_pos) ?_
      intro c hcball
      have hc : ‖c - c₀‖ < εK := by simpa [dist_eq_norm] using hcball
      have hsupp_empty_c :
          chartOrderSupport (RS := CRS.toRiemannSurface) (fun x => f x - c) = ∅ := by
        ext p
        constructor
        · intro hp
          have hp_union : p ∈ ⋃ q ∈ chartOrderSupport (RS := CRS.toRiemannSurface) f₀, U q :=
            hsupport_subset c hc hp
          simpa [hsupp₀_empty] using hp_union
        · intro hp
          simpa using hp
      have hsum_c :
          chartOrderSum CRS (fun x => f x - c)
            (chartMeromorphic_sub_const c hf)
            (chartOrderSupport_sub_const_finite CRS f c hf) = 0 := by
        simp only [chartOrderSum]
        rw [show (chartOrderSupport_sub_const_finite CRS f c hf).toFinset = ∅ from by
              rw [← Finset.val_eq_zero]
              ext q
              simp [hsupp_empty_c]]
        simp
      simpa [hsum_c, hsum_c₀]
    have hsupp₀_nonempty : (chartOrderSupport (RS := CRS.toRiemannSurface) f₀).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hsupp₀_empty
    set s₀ : Finset CRS.toRiemannSurface.carrier := hsupp₀.toFinset with hs₀_def
    have hs₀_nonempty : s₀.Nonempty := by
      obtain ⟨q, hq⟩ := hsupp₀_nonempty
      exact ⟨q, by simpa [s₀, hs₀_def] using hsupp₀.mem_toFinset.mpr hq⟩
    have hlocal_fin :
        ∀ q ∈ s₀,
          ∃ r > 0, r ≤ 1 ∧
            (∀ z, ‖z - chartPt (RS := CRS.toRiemannSurface) q‖ < r →
              z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target ∧
              (extChartAt 𝓘(ℂ, ℂ) q).symm z ∈ U q) ∧
            ∃ ε > 0, ∀ c : ℂ, ‖c - c₀‖ < ε →
            ∃ S : Finset ℂ,
              (∀ z ∈ S, ‖z - chartPt (RS := CRS.toRiemannSurface) q‖ < r) ∧
              (∀ z, ‖z - chartPt (RS := CRS.toRiemannSurface) q‖ < r →
                meromorphicOrderAt
                  (fun w => chartRep (RS := CRS.toRiemannSurface) f q w - c) z ≠ 0 →
                meromorphicOrderAt
                  (fun w => chartRep (RS := CRS.toRiemannSurface) f q w - c) z ≠ ⊤ →
                z ∈ S) ∧
              S.sum (fun z => (meromorphicOrderAt
                (fun w => chartRep (RS := CRS.toRiemannSurface) f q w - c) z).getD 0) =
                (chartOrderAt (RS := CRS.toRiemannSurface) f₀ q).getD 0 := by
      intro q hq
      exact hlocal q (by simpa [s₀, hs₀_def] using hsupp₀.mem_toFinset.mp hq)
    choose r hr_pos hr_le_one hr_chart ε hε_pos hloc using hlocal_fin
    set t₀ : Finset {q // q ∈ s₀} := s₀.attach with ht₀_def
    have ht₀_nonempty : t₀.Nonempty := by
      simpa [t₀, ht₀_def] using hs₀_nonempty.attach
    set eFun : {q // q ∈ s₀} → ℝ := fun q => ε q.1 q.2 with heFun_def
    set ε₀ : ℝ := min εK (t₀.inf' ht₀_nonempty eFun) with hε₀_def
    have hε_inf_pos : 0 < t₀.inf' ht₀_nonempty eFun :=
      Finset.inf'_induction ht₀_nonempty eFun
        (fun _ h₁ _ h₂ => lt_min h₁ h₂) (fun q hq => by
          exact hε_pos q.1 q.2)
    have hε₀_pos : 0 < ε₀ := by
      exact lt_min hεK_pos hε_inf_pos
    have hlocal_at :
        ∀ c : ℂ, ‖c - c₀‖ < ε₀ →
          ∀ q, ∀ hq : q ∈ s₀,
            ∃ S : Finset ℂ,
              (∀ z ∈ S, ‖z - chartPt (RS := CRS.toRiemannSurface) q‖ < r q hq) ∧
              (∀ z, ‖z - chartPt (RS := CRS.toRiemannSurface) q‖ < r q hq →
                meromorphicOrderAt
                  (fun w => chartRep (RS := CRS.toRiemannSurface) f q w - c) z ≠ 0 →
                meromorphicOrderAt
                  (fun w => chartRep (RS := CRS.toRiemannSurface) f q w - c) z ≠ ⊤ →
                z ∈ S) ∧
              S.sum (fun z => (meromorphicOrderAt
                (fun w => chartRep (RS := CRS.toRiemannSurface) f q w - c) z).getD 0) =
                (chartOrderAt (RS := CRS.toRiemannSurface) f₀ q).getD 0 := by
      intro c hc q hq
      have hcεq : ‖c - c₀‖ < ε q hq := by
        have hq_attach : (⟨q, hq⟩ : {q // q ∈ s₀}) ∈ t₀ := by
          simpa [t₀, ht₀_def]
        have hc_inf : ‖c - c₀‖ < t₀.inf' ht₀_nonempty eFun :=
          lt_of_lt_of_le hc (min_le_right _ _)
        have hle : t₀.inf' ht₀_nonempty eFun ≤ eFun ⟨q, hq⟩ := Finset.inf'_le eFun hq_attach
        exact lt_of_lt_of_le hc_inf (by simpa [eFun, heFun_def] using hle)
      exact hloc q hq c hcεq
    set W : Set CRS.toRiemannSurface.carrier :=
      ⋃ q : CRS.toRiemannSurface.carrier, ⋃ hq : q ∈ s₀,
        U q ∩ ((extChartAt 𝓘(ℂ, ℂ) q).source ∩
          (extChartAt 𝓘(ℂ, ℂ) q) ⁻¹'
            Metric.ball (chartPt (RS := CRS.toRiemannSurface) q) (r q hq))
      with hW_def
    set KW : Set CRS.toRiemannSurface.carrier := Wᶜ with hKW_def
    have hW_open : IsOpen W := by
      refine isOpen_iUnion ?_
      intro q
      refine isOpen_iUnion ?_
      intro hq
      have hchart_open :
          IsOpen
            ((extChartAt 𝓘(ℂ, ℂ) q).source ∩
              (extChartAt 𝓘(ℂ, ℂ) q) ⁻¹'
                Metric.ball (chartPt (RS := CRS.toRiemannSurface) q) (r q hq)) :=
        (continuousOn_extChartAt q).isOpen_inter_preimage
          (isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) q) Metric.isOpen_ball
      exact (hU_mem_open q).2.inter hchart_open
    have hKW_compact : @IsCompact _ CRS.toRiemannSurface.topology KW := by
      have hKW_closed : IsClosed KW := by
        simpa [KW, hKW_def] using hW_open.isClosed_compl
      exact hKW_closed.isCompact
    have hKW_no_support :
        ∀ p ∈ KW, chartOrderAt (RS := CRS.toRiemannSurface) f₀ p = 0 := by
      intro p hpKW
      have hp_not_W : p ∉ W := by simpa [KW, hKW_def] using hpKW
      have hp_not_supp :
          p ∉ chartOrderSupport (RS := CRS.toRiemannSurface) f₀ := by
        intro hp_supp
        have hp_s₀ : p ∈ s₀ := by
          simpa [s₀, hs₀_def] using hsupp₀.mem_toFinset.mpr hp_supp
        have hpW : p ∈ W := by
          refine Set.mem_iUnion₂.mpr ⟨p, hp_s₀, ?_⟩
          refine ⟨(hU_mem_open p).1, ?_⟩
          refine ⟨mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) p, ?_⟩
          have hpball :
              extChartAt 𝓘(ℂ, ℂ) p p ∈
                Metric.ball (chartPt (RS := CRS.toRiemannSurface) p) (r p hp_s₀) := by
            change dist (extChartAt 𝓘(ℂ, ℂ) p p)
                (chartPt (RS := CRS.toRiemannSurface) p) < r p hp_s₀
            simpa [chartPt] using hr_pos p hp_s₀
          exact hpball
        exact hp_not_W hpW
      have hnot :
          ¬ (chartOrderAt (RS := CRS.toRiemannSurface) f₀ p ≠ 0 ∧
            chartOrderAt (RS := CRS.toRiemannSurface) f₀ p ≠ ⊤) := by
        simpa [chartOrderSupport] using hp_not_supp
      by_cases hp0 : chartOrderAt (RS := CRS.toRiemannSurface) f₀ p = 0
      · exact hp0
      · have hp_top : chartOrderAt (RS := CRS.toRiemannSurface) f₀ p = ⊤ := by
          by_contra hp_ne_top
          exact hnot ⟨hp0, hp_ne_top⟩
        exact (hne_top₀ p hp_top).elim
    have hKW_no_pole :
        ∀ p ∈ KW, (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p := by
      intro p hpKW
      have hnonneg_sub : (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f₀ p := by
        simpa [hKW_no_support p hpKW]
      exact (chartOrderAt_sub_const_nonneg_iff (RS := CRS.toRiemannSurface)
        (f := f) (p := p) c₀).1 hnonneg_sub
    obtain ⟨εW, hεW_pos, hεW⟩ :=
      no_support_on_compact_near_c₀ CRS f hf hne_top c₀ KW hKW_compact hKW_no_pole hKW_no_support
    set ε₁ : ℝ := min ε₀ εW with hε₁_def
    have hε₁_pos : 0 < ε₁ := lt_min hε₀_pos hεW_pos
    refine Filter.mem_of_superset (Metric.ball_mem_nhds c₀ hε₁_pos) ?_
    intro c hcball
    have hc : ‖c - c₀‖ < ε₁ := by simpa [dist_eq_norm] using hcball
    have hc₀ : ‖c - c₀‖ < ε₀ := lt_of_lt_of_le hc (min_le_left _ _)
    have hcW : ‖c - c₀‖ < εW := lt_of_lt_of_le hc (min_le_right _ _)
    have hsupp_subset_W :
        chartOrderSupport (RS := CRS.toRiemannSurface) (fun x => f x - c) ⊆ W := by
      intro p hp
      by_contra hp_not_W
      have hpKW : p ∈ KW := by simpa [KW, hKW_def] using hp_not_W
      have hord0 : chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p = 0 :=
        hεW c hcW p hpKW
      exact hp.1 hord0
    have hlocal_c :
        ∀ q, ∀ hq : q ∈ s₀,
          ∃ S : Finset ℂ,
            (∀ z ∈ S, ‖z - chartPt (RS := CRS.toRiemannSurface) q‖ < r q hq) ∧
            (∀ z, ‖z - chartPt (RS := CRS.toRiemannSurface) q‖ < r q hq →
              meromorphicOrderAt
                (fun w => chartRep (RS := CRS.toRiemannSurface) f q w - c) z ≠ 0 →
              meromorphicOrderAt
                (fun w => chartRep (RS := CRS.toRiemannSurface) f q w - c) z ≠ ⊤ →
              z ∈ S) ∧
            S.sum (fun z => (meromorphicOrderAt
              (fun w => chartRep (RS := CRS.toRiemannSurface) f q w - c) z).getD 0) =
              (chartOrderAt (RS := CRS.toRiemannSurface) f₀ q).getD 0 :=
      hlocal_at c hc₀
    choose Sc hSc_ball hSc_cap hSc_sum using hlocal_c
    have hsupp_owner :
        ∀ p ∈ chartOrderSupport (RS := CRS.toRiemannSurface) (fun x => f x - c),
          ∃ q, ∃ hq : q ∈ s₀,
            p ∈ U q ∧
            p ∈ (extChartAt 𝓘(ℂ, ℂ) q).source ∧
            extChartAt 𝓘(ℂ, ℂ) q p ∈
              Metric.ball (chartPt (RS := CRS.toRiemannSurface) q) (r q hq) := by
      intro p hp
      have hpW : p ∈ W := hsupp_subset_W hp
      rcases Set.mem_iUnion₂.mp hpW with ⟨q, hq, hpq⟩
      rcases hpq with ⟨hpU, hpRest⟩
      rcases hpRest with ⟨hpSrc, hpBall⟩
      exact ⟨q, hq, hpU, hpSrc, hpBall⟩
    have hsupp_owner_unique :
        ∀ p q₁ q₂, q₁ ∈ s₀ → q₂ ∈ s₀ → p ∈ U q₁ → p ∈ U q₂ → q₁ = q₂ := by
      intro p q₁ q₂ hq₁ hq₂ hpU₁ hpU₂
      have hq₁_supp : q₁ ∈ chartOrderSupport (RS := CRS.toRiemannSurface) f₀ := by
        simpa [s₀, hs₀_def] using hsupp₀.mem_toFinset.mp hq₁
      have hq₂_supp : q₂ ∈ chartOrderSupport (RS := CRS.toRiemannSurface) f₀ := by
        simpa [s₀, hs₀_def] using hsupp₀.mem_toFinset.mp hq₂
      have hnot_disj : ¬ Disjoint (U q₁) (U q₂) := by
        exact Set.not_disjoint_iff.mpr ⟨p, hpU₁, hpU₂⟩
      exact Set.PairwiseDisjoint.elim hU_disj hq₁_supp hq₂_supp hnot_disj
    have hsupp_point_mem_Sc :
        ∀ p ∈ chartOrderSupport (RS := CRS.toRiemannSurface) (fun x => f x - c),
          ∃ q, ∃ hq : q ∈ s₀,
            p ∈ U q ∧
            p ∈ (extChartAt 𝓘(ℂ, ℂ) q).source ∧
            extChartAt 𝓘(ℂ, ℂ) q p ∈ Sc q hq := by
      intro p hp
      rcases hsupp_owner p hp with ⟨q, hq, hpU, hpSrc, hpBall⟩
      have hpEChart : p ∈ (eChart q).source := by
        change p ∈ (extChartAt 𝓘(ℂ, ℂ) q).source
        simpa using hpSrc
      have horder_eq :
          chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p =
            meromorphicOrderAt
              (fun w => chartRep (RS := CRS.toRiemannSurface) f q w - c)
              (extChartAt 𝓘(ℂ, ℂ) q p) := by
        rw [chartOrderAt_eq_in_chart (RS := CRS.toRiemannSurface) (fun x => f x - c) q p
          (chartMeromorphic_sub_const c hf) hpEChart, chartRep_sub_const]
      have hchart_ne0 :
          meromorphicOrderAt
            (fun w => chartRep (RS := CRS.toRiemannSurface) f q w - c)
            (extChartAt 𝓘(ℂ, ℂ) q p) ≠ 0 := by
        intro h0
        exact hp.1 (horder_eq.trans h0)
      have hchart_ne_top :
          meromorphicOrderAt
            (fun w => chartRep (RS := CRS.toRiemannSurface) f q w - c)
            (extChartAt 𝓘(ℂ, ℂ) q p) ≠ ⊤ := by
        intro htop
        exact hp.2 (horder_eq.trans htop)
      have hpNorm :
          ‖extChartAt 𝓘(ℂ, ℂ) q p - chartPt (RS := CRS.toRiemannSurface) q‖ < r q hq := by
        simpa [dist_eq_norm] using Metric.mem_ball.mp hpBall
      refine ⟨q, hq, hpU, hpSrc, ?_⟩
      exact hSc_cap q hq (extChartAt 𝓘(ℂ, ℂ) q p) hpNorm hchart_ne0 hchart_ne_top
    have hsupp0_finset_eq_s₀ :
        (chartOrderSupport_sub_const_finite CRS f c₀ hf).toFinset = s₀ := by
      ext p
      simp [s₀, hs₀_def, f₀]
    have hsum_c₀_as_s₀ :
        chartOrderSum CRS (fun x => f x - c₀)
          (chartMeromorphic_sub_const c₀ hf)
          (chartOrderSupport_sub_const_finite CRS f c₀ hf) =
          s₀.sum (fun q =>
            (chartOrderAt (RS := CRS.toRiemannSurface) f₀ q).getD 0) := by
      simp [chartOrderSum, hsupp0_finset_eq_s₀, f₀]
    have hsum_locals :
        s₀.sum (fun q =>
          (chartOrderAt (RS := CRS.toRiemannSurface) f₀ q).getD 0) =
          (s₀.attach).sum (fun q =>
            (Sc q.1 q.2).sum (fun z =>
              (meromorphicOrderAt
                (fun w => chartRep (RS := CRS.toRiemannSurface) f q.1 w - c) z).getD 0)) := by
      calc
        s₀.sum (fun q => (chartOrderAt (RS := CRS.toRiemannSurface) f₀ q).getD 0)
            = (s₀.attach).sum (fun q =>
                (chartOrderAt (RS := CRS.toRiemannSurface) f₀ q.1).getD 0) := by
                  symm
                  exact Finset.sum_attach s₀
                    (fun q => (chartOrderAt (RS := CRS.toRiemannSurface) f₀ q).getD 0)
        _ = (s₀.attach).sum (fun q =>
              (Sc q.1 q.2).sum (fun z =>
                (meromorphicOrderAt
                  (fun w => chartRep (RS := CRS.toRiemannSurface) f q.1 w - c) z).getD 0)) := by
              refine Finset.sum_congr rfl ?_
              intro q hq
              simpa using (hSc_sum q.1 q.2).symm
    have hsum_c_as_locals :
        chartOrderSum CRS (fun x => f x - c)
          (chartMeromorphic_sub_const c hf)
          (chartOrderSupport_sub_const_finite CRS f c hf) =
          (s₀.attach).sum (fun q =>
            (Sc q.1 q.2).sum (fun z =>
              (meromorphicOrderAt
                (fun w => chartRep (RS := CRS.toRiemannSurface) f q.1 w - c) z).getD 0)) := by
      set suppc : Finset CRS.toRiemannSurface.carrier :=
        (chartOrderSupport_sub_const_finite CRS f c hf).toFinset with hsuppc_def
      set F : CRS.toRiemannSurface.carrier → ℤ := fun p =>
        (chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p).getD 0 with hF_def
      have hsum_def :
          chartOrderSum CRS (fun x => f x - c)
            (chartMeromorphic_sub_const c hf)
            (chartOrderSupport_sub_const_finite CRS f c hf) = suppc.sum F := by
        simp [chartOrderSum, suppc, F]
      set Tsub : {q // q ∈ s₀} → Finset CRS.toRiemannSurface.carrier :=
        fun q => suppc.filter (fun p => p ∈ U q.1) with hTsub_def
      have hTsub_disj : (↑t₀ : Set {q // q ∈ s₀}).PairwiseDisjoint Tsub := by
        intro q₁ hq₁ q₂ hq₂ hne
        refine Finset.disjoint_left.2 ?_
        intro p hp₁ hp₂
        have hpU₁ : p ∈ U q₁.1 := (Finset.mem_filter.mp hp₁).2
        have hpU₂ : p ∈ U q₂.1 := (Finset.mem_filter.mp hp₂).2
        have hqeq : q₁.1 = q₂.1 := hsupp_owner_unique p q₁.1 q₂.1 q₁.2 q₂.2 hpU₁ hpU₂
        exact hne (Subtype.ext hqeq)
      have hsuppc_eq_biUnion : suppc = t₀.biUnion Tsub := by
        ext p
        constructor
        · intro hp
          have hp_supp :
              p ∈ chartOrderSupport (RS := CRS.toRiemannSurface) (fun x => f x - c) := by
            simpa [suppc, hsuppc_def] using
              (chartOrderSupport_sub_const_finite CRS f c hf).mem_toFinset.mp hp
          rcases hsupp_owner p hp_supp with ⟨q, hq, hpU, _hpSrc, _hpBall⟩
          have hq_t₀ : (⟨q, hq⟩ : {q // q ∈ s₀}) ∈ t₀ := by
            simpa [t₀, ht₀_def]
          refine Finset.mem_biUnion.mpr ⟨⟨q, hq⟩, hq_t₀, ?_⟩
          exact Finset.mem_filter.mpr ⟨hp, hpU⟩
        · intro hp
          rcases Finset.mem_biUnion.mp hp with ⟨q, _hq_t₀, hpT⟩
          exact (Finset.mem_filter.mp hpT).1
      have hsum_partition :
          suppc.sum F = t₀.sum (fun q => (Tsub q).sum F) := by
        rw [hsuppc_eq_biUnion]
        simpa using (Finset.sum_biUnion hTsub_disj)
      have hTsub_mem_source :
          ∀ q : {q // q ∈ s₀}, ∀ p ∈ Tsub q,
            p ∈ (extChartAt 𝓘(ℂ, ℂ) q.1).source := by
        intro q p hpT
        have hp_in_suppc : p ∈ suppc := (Finset.mem_filter.mp hpT).1
        have hpUq : p ∈ U q.1 := (Finset.mem_filter.mp hpT).2
        have hp_supp :
            p ∈ chartOrderSupport (RS := CRS.toRiemannSurface) (fun x => f x - c) := by
          simpa [suppc, hsuppc_def] using
            (chartOrderSupport_sub_const_finite CRS f c hf).mem_toFinset.mp hp_in_suppc
        rcases hsupp_owner p hp_supp with ⟨q₀, hq₀, hpU₀, hpSrc₀, _hpBall₀⟩
        have hqeq : q.1 = q₀ := hsupp_owner_unique p q.1 q₀ q.2 hq₀ hpUq hpU₀
        subst hqeq
        simpa using hpSrc₀
      set Gsub : {q // q ∈ s₀} → ℂ → ℤ := fun q z =>
        (meromorphicOrderAt
          (fun w => chartRep (RS := CRS.toRiemannSurface) f q.1 w - c) z).getD 0 with hGsub_def
      have hF_eq_Gsub :
          ∀ q : {q // q ∈ s₀}, ∀ p ∈ Tsub q,
            F p = Gsub q (extChartAt 𝓘(ℂ, ℂ) q.1 p) := by
        intro q p hpT
        unfold F Gsub
        have hpSrc : p ∈ (extChartAt 𝓘(ℂ, ℂ) q.1).source := hTsub_mem_source q p hpT
        have hpEChart : p ∈ (eChart q.1).source := by
          change p ∈ (extChartAt 𝓘(ℂ, ℂ) q.1).source
          simpa using hpSrc
        rw [chartOrderAt_eq_in_chart (RS := CRS.toRiemannSurface) (fun x => f x - c) q.1 p
          (chartMeromorphic_sub_const c hf) hpEChart, chartRep_sub_const]
      have hTsub_sum_image :
          ∀ q : {q // q ∈ s₀},
            (Tsub q).sum F =
              ((Tsub q).image (fun p => extChartAt 𝓘(ℂ, ℂ) q.1 p)).sum (Gsub q) := by
        intro q
        have hsum_rewrite :
            (Tsub q).sum F = (Tsub q).sum (fun p => Gsub q (extChartAt 𝓘(ℂ, ℂ) q.1 p)) := by
          refine Finset.sum_congr rfl ?_
          intro p hpT
          exact hF_eq_Gsub q p hpT
        rw [hsum_rewrite]
        symm
        refine Finset.sum_image ?_
        intro p₁ hp₁ p₂ hp₂ heq
        exact (extChartAt 𝓘(ℂ, ℂ) q.1).injOn
          (hTsub_mem_source q p₁ hp₁) (hTsub_mem_source q p₂ hp₂) heq
      set Iq : {q // q ∈ s₀} → Finset ℂ := fun q =>
        (Tsub q).image (fun p => extChartAt 𝓘(ℂ, ℂ) q.1 p) with hIq_def
      have hIq_subset_Sc :
          ∀ q : {q // q ∈ s₀}, ∀ z ∈ Iq q, z ∈ Sc q.1 q.2 := by
        intro q z hzIq
        rcases Finset.mem_image.mp (by simpa [Iq, hIq_def] using hzIq) with ⟨p, hpT, rfl⟩
        have hp_in_suppc : p ∈ suppc := (Finset.mem_filter.mp hpT).1
        have hpUq : p ∈ U q.1 := (Finset.mem_filter.mp hpT).2
        have hp_supp :
            p ∈ chartOrderSupport (RS := CRS.toRiemannSurface) (fun x => f x - c) := by
          simpa [suppc, hsuppc_def] using
            (chartOrderSupport_sub_const_finite CRS f c hf).mem_toFinset.mp hp_in_suppc
        rcases hsupp_point_mem_Sc p hp_supp with ⟨q₀, hq₀, hpU₀, _hpSrc₀, hzSc₀⟩
        have hqeq : q.1 = q₀ := hsupp_owner_unique p q.1 q₀ q.2 hq₀ hpUq hpU₀
        subst hqeq
        have hproof : hq₀ = q.2 := Subsingleton.elim _ _
        simpa [hproof] using hzSc₀
      have hsum_as_images :
          chartOrderSum CRS (fun x => f x - c)
            (chartMeromorphic_sub_const c hf)
            (chartOrderSupport_sub_const_finite CRS f c hf) =
          t₀.sum (fun q => (Iq q).sum (Gsub q)) := by
        rw [hsum_def, hsum_partition]
        refine Finset.sum_congr rfl ?_
        intro q hq
        simpa [Iq, hIq_def] using hTsub_sum_image q
      have himages_eq_locals :
          t₀.sum (fun q => (Iq q).sum (Gsub q)) =
            t₀.sum (fun q =>
              (Sc q.1 q.2).sum (fun z =>
                (meromorphicOrderAt
                  (fun w => chartRep (RS := CRS.toRiemannSurface) f q.1 w - c) z).getD 0)) := by
        refine Finset.sum_congr rfl ?_
        intro q hq
        have hsubset : Iq q ⊆ Sc q.1 q.2 := by
          intro z hz
          exact hIq_subset_Sc q z hz
        have hzero :
            ∀ z ∈ Sc q.1 q.2, z ∉ Iq q → Gsub q z = 0 := by
          intro z hzSc hzNotIq
          by_cases hz0 :
              meromorphicOrderAt
                (fun w => chartRep (RS := CRS.toRiemannSurface) f q.1 w - c) z = 0
          · unfold Gsub
            rw [hz0]
            rfl
          · by_cases hzTop :
                meromorphicOrderAt
                  (fun w => chartRep (RS := CRS.toRiemannSurface) f q.1 w - c) z = ⊤
            · unfold Gsub
              rw [hzTop]
              rfl
            · have hzBall : ‖z - chartPt (RS := CRS.toRiemannSurface) q.1‖ < r q.1 q.2 :=
                hSc_ball q.1 q.2 z hzSc
              have hzTargetU :
                  z ∈ (extChartAt 𝓘(ℂ, ℂ) q.1).target ∧
                  (extChartAt 𝓘(ℂ, ℂ) q.1).symm z ∈ U q.1 :=
                hr_chart q.1 q.2 z hzBall
              let p : CRS.toRiemannSurface.carrier := (extChartAt 𝓘(ℂ, ℂ) q.1).symm z
              have hpU : p ∈ U q.1 := by
                simpa [p] using hzTargetU.2
              have hpSrc : p ∈ (extChartAt 𝓘(ℂ, ℂ) q.1).source := by
                exact (extChartAt 𝓘(ℂ, ℂ) q.1).map_target hzTargetU.1
              have hpEChart : p ∈ (eChart q.1).source := by
                change p ∈ (extChartAt 𝓘(ℂ, ℂ) q.1).source
                exact hpSrc
              have hzEq : extChartAt 𝓘(ℂ, ℂ) q.1 p = z := by
                change (extChartAt 𝓘(ℂ, ℂ) q.1) ((extChartAt 𝓘(ℂ, ℂ) q.1).symm z) = z
                exact (extChartAt 𝓘(ℂ, ℂ) q.1).right_inv hzTargetU.1
              have horder_eq :
                  chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p =
                    meromorphicOrderAt
                      (fun w => chartRep (RS := CRS.toRiemannSurface) f q.1 w - c) z := by
                rw [chartOrderAt_eq_in_chart (RS := CRS.toRiemannSurface) (fun x => f x - c) q.1 p
                  (chartMeromorphic_sub_const c hf) hpEChart, chartRep_sub_const, hzEq]
              have hp_supp :
                  p ∈ chartOrderSupport (RS := CRS.toRiemannSurface) (fun x => f x - c) := by
                refine ⟨?_, ?_⟩
                · intro hp0
                  exact hz0 (horder_eq.symm.trans hp0)
                · intro hpTop
                  exact hzTop (horder_eq.symm.trans hpTop)
              have hp_suppc : p ∈ suppc := by
                simpa [suppc, hsuppc_def] using
                  (chartOrderSupport_sub_const_finite CRS f c hf).mem_toFinset.mpr hp_supp
              have hpTsub : p ∈ Tsub q := Finset.mem_filter.mpr ⟨hp_suppc, hpU⟩
              have hzIq : z ∈ Iq q := by
                refine Finset.mem_image.mpr ⟨p, hpTsub, ?_⟩
                simpa [p] using hzEq
              exact (hzNotIq hzIq).elim
        have hsum_subset :
            (Iq q).sum (Gsub q) = (Sc q.1 q.2).sum (Gsub q) :=
          Finset.sum_subset hsubset hzero
        simpa [Gsub, hGsub_def] using hsum_subset
      calc
        chartOrderSum CRS (fun x => f x - c)
            (chartMeromorphic_sub_const c hf)
            (chartOrderSupport_sub_const_finite CRS f c hf)
            = t₀.sum (fun q => (Iq q).sum (Gsub q)) := hsum_as_images
        _ = t₀.sum (fun q =>
              (Sc q.1 q.2).sum (fun z =>
                (meromorphicOrderAt
                  (fun w => chartRep (RS := CRS.toRiemannSurface) f q.1 w - c) z).getD 0)) :=
              himages_eq_locals
        _ = (s₀.attach).sum (fun q =>
              (Sc q.1 q.2).sum (fun z =>
                (meromorphicOrderAt
                  (fun w => chartRep (RS := CRS.toRiemannSurface) f q.1 w - c) z).getD 0)) := by
              simpa [t₀, ht₀_def]
    have hsum_c_eq_hsum_c₀ :
        chartOrderSum CRS (fun x => f x - c)
          (chartMeromorphic_sub_const c hf)
          (chartOrderSupport_sub_const_finite CRS f c hf) =
        chartOrderSum CRS (fun x => f x - c₀)
          (chartMeromorphic_sub_const c₀ hf)
          (chartOrderSupport_sub_const_finite CRS f c₀ hf) := by
      calc
        chartOrderSum CRS (fun x => f x - c)
            (chartMeromorphic_sub_const c hf)
            (chartOrderSupport_sub_const_finite CRS f c hf)
            =
            (s₀.attach).sum (fun q =>
              (Sc q.1 q.2).sum (fun z =>
                (meromorphicOrderAt
                  (fun w => chartRep (RS := CRS.toRiemannSurface) f q.1 w - c) z).getD 0)) :=
              hsum_c_as_locals
        _ = s₀.sum (fun q =>
              (chartOrderAt (RS := CRS.toRiemannSurface) f₀ q).getD 0) := by
                simpa using hsum_locals.symm
        _ = chartOrderSum CRS (fun x => f x - c₀)
              (chartMeromorphic_sub_const c₀ hf)
              (chartOrderSupport_sub_const_finite CRS f c₀ hf) := by
                simpa using hsum_c₀_as_s₀.symm
    simpa using hsum_c_eq_hsum_c₀
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
  obtain ⟨q₀⟩ := (inferInstance : Nonempty CRS.toRiemannSurface.carrier)
  have hsupp_f : (chartOrderSupport (RS := CRS.toRiemannSurface) f).Finite :=
    chartOrderSupport_finite_general CRS f hf ⟨q₀, hne_top q₀⟩
  have hpole_fin : (poleSet (RS := CRS.toRiemannSurface) f).Finite :=
    poleSet_finite CRS f hf hsupp_f
  obtain ⟨U, hU_mem_open, hU_disj⟩ := hpole_fin.t2_separation
  set K : Set CRS.toRiemannSurface.carrier :=
    (⋃ p ∈ poleSet (RS := CRS.toRiemannSurface) f, U p)ᶜ
  by_cases hpole_empty : poleSet (RS := CRS.toRiemannSurface) f = ∅
  · have hnonneg : ∀ q, (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f q := by
      intro q
      exact le_of_not_gt (by
        intro hlt
        have hmem : q ∈ poleSet (RS := CRS.toRiemannSurface) f := by
          simpa [poleSet, Set.mem_setOf_eq] using hlt
        simpa [hpole_empty] using hmem)
    obtain ⟨C, hC_pos, hC_prop⟩ :=
      no_support_on_compact_away_from_poles CRS f hf hne_top Set.univ isCompact_univ
        (by intro q _; exact hnonneg q)
    let c₀ : ℂ := (C + 1 : ℝ)
    have hc₀_large : C < ‖c₀‖ := by
      have hnorm : ‖c₀‖ = |C + 1| := by
        simpa [c₀] using (Complex.norm_real (C + 1))
      have hle_abs : C + 1 ≤ |C + 1| := le_abs_self (C + 1)
      have hC_lt : C < C + 1 := by linarith
      linarith
    have hzero_all :
        ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c₀) q = 0 := by
      intro q
      exact hC_prop c₀ hc₀_large q (by simp)
    have hsupp_empty :
        chartOrderSupport (RS := CRS.toRiemannSurface) (fun x => f x - c₀) = ∅ := by
      ext q
      simp [chartOrderSupport, hzero_all q]
    have hsuppc_empty :
        (chartOrderSupport_sub_const_finite CRS f c₀ hf).toFinset = ∅ := by
      rw [← Finset.val_eq_zero]
      ext q
      simp [hsupp_empty]
    refine ⟨c₀, ?_⟩
    unfold chartOrderSum
    rw [hsuppc_empty]
    simp
  have hpole_nonempty : (poleSet (RS := CRS.toRiemannSurface) f).Nonempty := by
    exact Set.nonempty_iff_ne_empty.mpr hpole_empty
  have hpole_finset_nonempty : (hpole_fin.toFinset).Nonempty := by
    obtain ⟨p, hp⟩ := hpole_nonempty
    refine ⟨p, ?_⟩
    exact hpole_fin.mem_toFinset.mpr hp
  have hchart_data :
      ∀ pp : {p // p ∈ hpole_fin.toFinset}, ∃ ρ : ℝ, 0 < ρ ∧
        ∀ z, ‖z - chartPt (RS := CRS.toRiemannSurface) pp.1‖ < ρ →
          z ∈ (extChartAt 𝓘(ℂ, ℂ) pp.1).target ∧
          (extChartAt 𝓘(ℂ, ℂ) pp.1).symm z ∈ U pp.1 := by
    intro pp
    let e := extChartAt 𝓘(ℂ, ℂ) pp.1
    have hU_nhds : U pp.1 ∈ nhds pp.1 := (hU_mem_open pp.1).2.mem_nhds (hU_mem_open pp.1).1
    have hpt_tgt : chartPt (RS := CRS.toRiemannSurface) pp.1 ∈ e.target := by
      simpa [e, chartPt] using
        (e.map_source (mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) pp.1))
    have hsymm_pt : e.symm (chartPt (RS := CRS.toRiemannSurface) pp.1) = pp.1 := by
      simpa [e, chartPt] using
        (e.left_inv (mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) pp.1))
    have hU_nhds' : U pp.1 ∈ nhds (e.symm (chartPt (RS := CRS.toRiemannSurface) pp.1)) := by
      simpa [hsymm_pt] using hU_nhds
    have hpre : e.symm ⁻¹' U pp.1 ∈ nhds (chartPt (RS := CRS.toRiemannSurface) pp.1) :=
      (continuousAt_extChartAt_symm'' (I := 𝓘(ℂ, ℂ)) hpt_tgt).preimage_mem_nhds hU_nhds'
    have htgt : e.target ∈ nhds (chartPt (RS := CRS.toRiemannSurface) pp.1) := by
      simpa [e, chartPt] using extChartAt_target_mem_nhds (I := 𝓘(ℂ, ℂ)) pp.1
    obtain ⟨ρ, hρ_pos, hρ_sub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem htgt hpre)
    refine ⟨ρ, hρ_pos, ?_⟩
    intro z hz
    have hz' : z ∈ e.target ∩ e.symm ⁻¹' U pp.1 := hρ_sub (Metric.mem_ball.mp (by
      simpa [dist_eq_norm] using hz))
    exact hz'
  choose ρ hρ_pos hρ_prop using hchart_data
  have hpole_local_data :
      ∀ pp : {p // p ∈ hpole_fin.toFinset},
        ∃ r > 0, r ≤ ρ pp ∧ ∃ C : ℝ, 0 < C ∧
          ∀ c : ℂ, C < ‖c‖ →
            ∃ S : Finset ℂ,
              (∀ z ∈ S, ‖z - chartPt (RS := CRS.toRiemannSurface) pp.1‖ < r) ∧
              (∀ z, ‖z - chartPt (RS := CRS.toRiemannSurface) pp.1‖ < r →
                meromorphicOrderAt
                  (fun w => chartRep (RS := CRS.toRiemannSurface) f pp.1 w - c) z ≠ 0 →
                meromorphicOrderAt
                  (fun w => chartRep (RS := CRS.toRiemannSurface) f pp.1 w - c) z ≠ ⊤ →
                z ∈ S) ∧
              S.sum (fun z =>
                (meromorphicOrderAt
                  (fun w => chartRep (RS := CRS.toRiemannSurface) f pp.1 w - c) z).getD 0) = 0 := by
    intro pp
    have hppole_mem : pp.1 ∈ poleSet (RS := CRS.toRiemannSurface) f :=
      hpole_fin.mem_toFinset.mp pp.2
    have hppole : chartOrderAt (RS := CRS.toRiemannSurface) f pp.1 < 0 := by
      simpa [poleSet, Set.mem_setOf_eq] using hppole_mem
    obtain ⟨r, hr_pos, hr_le, C, hC_pos, hC_data⟩ :=
      meromorphic_pole_local_sum_zero
        (g := chartRep (RS := CRS.toRiemannSurface) f pp.1)
        (z₀ := chartPt (RS := CRS.toRiemannSurface) pp.1)
        (hf pp.1)
        (by simpa [chartOrderAt] using hppole)
        (hρ_pos pp)
    refine ⟨r, hr_pos, hr_le, C, hC_pos, ?_⟩
    intro c hc
    exact hC_data c hc
  choose r hr_pos hr_leρ Cpole hCpole_pos hSpole using hpole_local_data
  set V : {p // p ∈ hpole_fin.toFinset} → Set CRS.toRiemannSurface.carrier := fun pp =>
    (extChartAt 𝓘(ℂ, ℂ) pp.1).source ∩
      (extChartAt 𝓘(ℂ, ℂ) pp.1) ⁻¹'
        Metric.ball (chartPt (RS := CRS.toRiemannSurface) pp.1) (r pp) with hV_def
  set Wpole : Set CRS.toRiemannSurface.carrier := ⋃ pp : {p // p ∈ hpole_fin.toFinset}, V pp
    with hWpole_def
  set Kpole : Set CRS.toRiemannSurface.carrier := Wpoleᶜ with hKpole_def
  have hWpole_open : IsOpen Wpole := by
    refine isOpen_iUnion ?_
    intro pp
    have hV_open :
        IsOpen ((extChartAt 𝓘(ℂ, ℂ) pp.1).source ∩
          (extChartAt 𝓘(ℂ, ℂ) pp.1) ⁻¹'
            Metric.ball (chartPt (RS := CRS.toRiemannSurface) pp.1) (r pp)) :=
      (continuousOn_extChartAt pp.1).isOpen_inter_preimage
        (isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) pp.1) Metric.isOpen_ball
    simpa [V, hV_def] using hV_open
  have hKpole_compact : @IsCompact _ CRS.toRiemannSurface.topology Kpole := by
    have hKpole_closed : IsClosed Kpole := by
      simpa [Kpole, hKpole_def] using hWpole_open.isClosed_compl
    exact hKpole_closed.isCompact
  have hKpole_no_pole :
      ∀ q ∈ Kpole, (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f q := by
    intro q hqK
    exact le_of_not_gt (by
      intro hlt
      have hq_pole : q ∈ poleSet (RS := CRS.toRiemannSurface) f := by
        simpa [poleSet, Set.mem_setOf_eq] using hlt
      let pp : {p // p ∈ hpole_fin.toFinset} := ⟨q, hpole_fin.mem_toFinset.mpr hq_pole⟩
      have hqV : q ∈ V pp := by
        refine ⟨mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) q, ?_⟩
        have hq_ball :
            extChartAt 𝓘(ℂ, ℂ) q q ∈
              Metric.ball (chartPt (RS := CRS.toRiemannSurface) q) (r pp) := by
          change dist (extChartAt 𝓘(ℂ, ℂ) q q)
              (chartPt (RS := CRS.toRiemannSurface) q) < r pp
          simpa [chartPt] using hr_pos pp
        exact hq_ball
      have hqW : q ∈ Wpole := by
        exact Set.mem_iUnion.mpr ⟨pp, by simpa [V, hV_def] using hqV⟩
      have hqK' : q ∈ Kpole := hqK
      exact (show q ∉ Wpole from by simpa [Kpole, hKpole_def] using hqK') hqW)
  obtain ⟨CK, hCK_pos, hKpole_prop⟩ :=
    no_support_on_compact_away_from_poles CRS f hf hne_top Kpole hKpole_compact hKpole_no_pole
  set tP : Finset {p // p ∈ hpole_fin.toFinset} := (hpole_fin.toFinset).attach with htP_def
  have htP_nonempty : tP.Nonempty := by
    obtain ⟨p, hp⟩ := hpole_finset_nonempty
    refine ⟨⟨p, hp⟩, ?_⟩
    simpa [tP, htP_def]
  set CmaxPole : ℝ := tP.sup' htP_nonempty Cpole
    with hCmaxPole_def
  have hCpole_le_max : ∀ pp : {p // p ∈ hpole_fin.toFinset}, Cpole pp ≤ CmaxPole := by
    intro pp
    have hpp_mem : pp ∈ tP := by
      simpa [tP, htP_def] using (Finset.mem_attach (hpole_fin.toFinset) pp)
    have hle : Cpole pp ≤ tP.sup' htP_nonempty Cpole := tP.le_sup' Cpole hpp_mem
    simpa [CmaxPole, hCmaxPole_def] using hle
  set Cglobal : ℝ := max CK CmaxPole + 1 with hCglobal_def
  have hCglobal_gt_CK : CK < Cglobal := by
    have hle : CK ≤ max CK CmaxPole := le_max_left CK CmaxPole
    linarith [hCglobal_def, hle]
  have hCglobal_gt_pole : ∀ pp : {p // p ∈ hpole_fin.toFinset}, Cpole pp < Cglobal := by
    intro pp
    have hle₁ : Cpole pp ≤ CmaxPole := hCpole_le_max pp
    have hle₂ : CmaxPole ≤ max CK CmaxPole := le_max_right CK CmaxPole
    linarith [hCglobal_def, hle₁, hle₂]
  let c₀ : ℂ := (Cglobal : ℝ)
  have hc₀_gt_CK : CK < ‖c₀‖ := by
    have hnorm : ‖c₀‖ = |Cglobal| := by simpa [c₀] using (Complex.norm_real Cglobal)
    have hle_abs : Cglobal ≤ |Cglobal| := le_abs_self Cglobal
    linarith [hCglobal_gt_CK]
  have hKpole_zero :
      ∀ q ∈ Kpole, chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c₀) q = 0 := by
    intro q hqK
    exact hKpole_prop c₀ hc₀_gt_CK q hqK
  have hsupp_subset_Wpole :
      ∀ q, q ∈ chartOrderSupport (RS := CRS.toRiemannSurface) (fun x => f x - c₀) →
        q ∈ Wpole := by
    intro q hqSupp
    by_contra hq_not_W
    have hqK : q ∈ Kpole := by simpa [Kpole, hKpole_def] using hq_not_W
    exact hqSupp.1 (hKpole_zero q hqK)
  have hc₀_gt_pole : ∀ pp : {p // p ∈ hpole_fin.toFinset}, Cpole pp < ‖c₀‖ := by
    intro pp
    have hnorm : ‖c₀‖ = |Cglobal| := by simpa [c₀] using (Complex.norm_real Cglobal)
    have hle_abs : Cglobal ≤ |Cglobal| := le_abs_self Cglobal
    linarith [hCglobal_gt_pole pp, hle_abs, hnorm]
  have hpole_sets_data :
      ∀ pp : {p // p ∈ hpole_fin.toFinset},
        ∃ S : Finset ℂ,
          (∀ z ∈ S, ‖z - chartPt (RS := CRS.toRiemannSurface) pp.1‖ < r pp) ∧
          (∀ z, ‖z - chartPt (RS := CRS.toRiemannSurface) pp.1‖ < r pp →
            meromorphicOrderAt
              (fun w => chartRep (RS := CRS.toRiemannSurface) f pp.1 w - c₀) z ≠ 0 →
            meromorphicOrderAt
              (fun w => chartRep (RS := CRS.toRiemannSurface) f pp.1 w - c₀) z ≠ ⊤ →
            z ∈ S) ∧
          S.sum (fun z =>
            (meromorphicOrderAt
              (fun w => chartRep (RS := CRS.toRiemannSurface) f pp.1 w - c₀) z).getD 0) = 0 := by
    intro pp
    exact hSpole pp c₀ (hc₀_gt_pole pp)
  choose Spp hS_ball hS_cap hS_sum using hpole_sets_data
  have hV_subset_U :
      ∀ pp : {p // p ∈ hpole_fin.toFinset}, ∀ q ∈ V pp, q ∈ U pp.1 := by
    intro pp q hqV
    rcases hqV with ⟨hqSrc, hqBall⟩
    have hq_norm :
        ‖extChartAt 𝓘(ℂ, ℂ) pp.1 q - chartPt (RS := CRS.toRiemannSurface) pp.1‖ < ρ pp := by
      exact lt_of_lt_of_le (by simpa [dist_eq_norm] using Metric.mem_ball.mp hqBall) (hr_leρ pp)
    have hz := hρ_prop pp (extChartAt 𝓘(ℂ, ℂ) pp.1 q) hq_norm
    have hqU_raw :
        (chartAt ℂ pp.1).symm ((chartAt ℂ pp.1) q) ∈ U pp.1 := by
      simpa using hz.2
    have hqSrc' : q ∈ (chartAt ℂ pp.1).source := by
      simpa using hqSrc
    have hq_eq_raw :
        (chartAt ℂ pp.1).symm ((chartAt ℂ pp.1) q) = q :=
      (chartAt ℂ pp.1).left_inv hqSrc'
    simpa [hq_eq_raw] using hqU_raw
  have hV_owner_unique :
      ∀ q (pp₁ pp₂ : {p // p ∈ hpole_fin.toFinset}),
        q ∈ V pp₁ → q ∈ V pp₂ → pp₁ = pp₂ := by
    intro q pp₁ pp₂ hqV₁ hqV₂
    have hqU₁ : q ∈ U pp₁.1 := hV_subset_U pp₁ q hqV₁
    have hqU₂ : q ∈ U pp₂.1 := hV_subset_U pp₂ q hqV₂
    have hpp₁_pole : pp₁.1 ∈ poleSet (RS := CRS.toRiemannSurface) f :=
      hpole_fin.mem_toFinset.mp pp₁.2
    have hpp₂_pole : pp₂.1 ∈ poleSet (RS := CRS.toRiemannSurface) f :=
      hpole_fin.mem_toFinset.mp pp₂.2
    have hbase_eq : pp₁.1 = pp₂.1 := by
      exact Set.PairwiseDisjoint.elim hU_disj hpp₁_pole hpp₂_pole
        (Set.not_disjoint_iff.mpr ⟨q, hqU₁, hqU₂⟩)
    exact Subtype.ext hbase_eq
  set suppc : Finset CRS.toRiemannSurface.carrier :=
    (chartOrderSupport_sub_const_finite CRS f c₀ hf).toFinset with hsuppc_def
  set F : CRS.toRiemannSurface.carrier → ℤ := fun q =>
    (chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c₀) q).getD 0 with hF_def
  have hsum_def :
      chartOrderSum CRS (fun x => f x - c₀)
        (chartMeromorphic_sub_const c₀ hf)
        (chartOrderSupport_sub_const_finite CRS f c₀ hf) = suppc.sum F := by
    simp [chartOrderSum, suppc, F]
  have hsupp_owner :
      ∀ q ∈ suppc, ∃ pp : {p // p ∈ hpole_fin.toFinset}, q ∈ V pp := by
    intro q hq
    have hq_supp :
        q ∈ chartOrderSupport (RS := CRS.toRiemannSurface) (fun x => f x - c₀) := by
      simpa [suppc, hsuppc_def] using
        (chartOrderSupport_sub_const_finite CRS f c₀ hf).mem_toFinset.mp hq
    have hqW : q ∈ Wpole := hsupp_subset_Wpole q hq_supp
    rcases Set.mem_iUnion.mp hqW with ⟨pp, hqV⟩
    exact ⟨pp, by simpa [V, hV_def] using hqV⟩
  set Tsub : {p // p ∈ hpole_fin.toFinset} → Finset CRS.toRiemannSurface.carrier :=
    fun pp => suppc.filter (fun q => q ∈ V pp) with hTsub_def
  have hTsub_disj : (↑tP : Set {p // p ∈ hpole_fin.toFinset}).PairwiseDisjoint Tsub := by
    intro pp₁ hpp₁ pp₂ hpp₂ hne
    refine Finset.disjoint_left.2 ?_
    intro q hq₁ hq₂
    have hqV₁ : q ∈ V pp₁ := (Finset.mem_filter.mp hq₁).2
    have hqV₂ : q ∈ V pp₂ := (Finset.mem_filter.mp hq₂).2
    have hEq : pp₁ = pp₂ := hV_owner_unique q pp₁ pp₂ hqV₁ hqV₂
    exact hne hEq
  have hsuppc_eq_biUnion : suppc = tP.biUnion Tsub := by
    ext q
    constructor
    · intro hq
      rcases hsupp_owner q hq with ⟨pp, hqV⟩
      have hpp_tP : pp ∈ tP := by
        simpa [tP, htP_def] using (Finset.mem_attach (hpole_fin.toFinset) pp)
      exact Finset.mem_biUnion.mpr ⟨pp, hpp_tP, Finset.mem_filter.mpr ⟨hq, hqV⟩⟩
    · intro hq
      rcases Finset.mem_biUnion.mp hq with ⟨pp, hpp_tP, hqT⟩
      exact (Finset.mem_filter.mp hqT).1
  have hsum_partition :
      suppc.sum F = tP.sum (fun pp => (Tsub pp).sum F) := by
    rw [hsuppc_eq_biUnion]
    simpa using (Finset.sum_biUnion hTsub_disj)
  have hTsub_mem_source :
      ∀ pp : {p // p ∈ hpole_fin.toFinset}, ∀ q ∈ Tsub pp,
        q ∈ (extChartAt 𝓘(ℂ, ℂ) pp.1).source := by
    intro pp q hqT
    exact ((Finset.mem_filter.mp hqT).2).1
  set G : {p // p ∈ hpole_fin.toFinset} → ℂ → ℤ := fun pp z =>
    (meromorphicOrderAt
      (fun w => chartRep (RS := CRS.toRiemannSurface) f pp.1 w - c₀) z).getD 0 with hG_def
  have hF_eq_G :
      ∀ pp : {p // p ∈ hpole_fin.toFinset}, ∀ q ∈ Tsub pp,
        F q = G pp (extChartAt 𝓘(ℂ, ℂ) pp.1 q) := by
    intro pp q hqT
    unfold F G
    have hqSrc : q ∈ (extChartAt 𝓘(ℂ, ℂ) pp.1).source := hTsub_mem_source pp q hqT
    have hqEChart : q ∈ (eChart pp.1).source := by
      change q ∈ (extChartAt 𝓘(ℂ, ℂ) pp.1).source
      simpa using hqSrc
    rw [chartOrderAt_eq_in_chart (RS := CRS.toRiemannSurface) (fun x => f x - c₀) pp.1 q
      (chartMeromorphic_sub_const c₀ hf) hqEChart, chartRep_sub_const]
  have hTsub_sum_image :
      ∀ pp : {p // p ∈ hpole_fin.toFinset},
        (Tsub pp).sum F =
          ((Tsub pp).image (fun q => extChartAt 𝓘(ℂ, ℂ) pp.1 q)).sum (G pp) := by
    intro pp
    have hsum_rewrite :
        (Tsub pp).sum F =
          (Tsub pp).sum (fun q => G pp (extChartAt 𝓘(ℂ, ℂ) pp.1 q)) := by
      refine Finset.sum_congr rfl ?_
      intro q hqT
      exact hF_eq_G pp q hqT
    rw [hsum_rewrite]
    symm
    refine Finset.sum_image ?_
    intro q₁ hq₁ q₂ hq₂ heq
    exact (extChartAt 𝓘(ℂ, ℂ) pp.1).injOn
      (hTsub_mem_source pp q₁ hq₁) (hTsub_mem_source pp q₂ hq₂) heq
  set Ipp : {p // p ∈ hpole_fin.toFinset} → Finset ℂ := fun pp =>
    (Tsub pp).image (fun q => extChartAt 𝓘(ℂ, ℂ) pp.1 q) with hIpp_def
  have hIpp_subset_Spp :
      ∀ pp : {p // p ∈ hpole_fin.toFinset}, ∀ z ∈ Ipp pp, z ∈ Spp pp := by
    intro pp z hzI
    rcases Finset.mem_image.mp (by simpa [Ipp, hIpp_def] using hzI) with ⟨q, hqT, rfl⟩
    have hqSuppc : q ∈ suppc := (Finset.mem_filter.mp hqT).1
    have hqV : q ∈ V pp := (Finset.mem_filter.mp hqT).2
    have hqSrc : q ∈ (extChartAt 𝓘(ℂ, ℂ) pp.1).source := hqV.1
    have hqBall :
        ‖extChartAt 𝓘(ℂ, ℂ) pp.1 q - chartPt (RS := CRS.toRiemannSurface) pp.1‖ < r pp := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hqV.2
    have hqSupp :
        q ∈ chartOrderSupport (RS := CRS.toRiemannSurface) (fun x => f x - c₀) := by
      simpa [suppc, hsuppc_def] using
        (chartOrderSupport_sub_const_finite CRS f c₀ hf).mem_toFinset.mp hqSuppc
    have hqEChart : q ∈ (eChart pp.1).source := by
      change q ∈ (extChartAt 𝓘(ℂ, ℂ) pp.1).source
      simpa using hqSrc
    have horder_eq :
        chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c₀) q =
          meromorphicOrderAt
            (fun w => chartRep (RS := CRS.toRiemannSurface) f pp.1 w - c₀)
            (extChartAt 𝓘(ℂ, ℂ) pp.1 q) := by
      rw [chartOrderAt_eq_in_chart (RS := CRS.toRiemannSurface) (fun x => f x - c₀) pp.1 q
        (chartMeromorphic_sub_const c₀ hf) hqEChart, chartRep_sub_const]
    have horder_ne0 :
        meromorphicOrderAt
          (fun w => chartRep (RS := CRS.toRiemannSurface) f pp.1 w - c₀)
          (extChartAt 𝓘(ℂ, ℂ) pp.1 q) ≠ 0 := by
      intro h0
      exact hqSupp.1 (horder_eq.trans h0)
    have horder_neTop :
        meromorphicOrderAt
          (fun w => chartRep (RS := CRS.toRiemannSurface) f pp.1 w - c₀)
          (extChartAt 𝓘(ℂ, ℂ) pp.1 q) ≠ ⊤ := by
      intro hTop
      exact hqSupp.2 (horder_eq.trans hTop)
    exact hS_cap pp (extChartAt 𝓘(ℂ, ℂ) pp.1 q) hqBall horder_ne0 horder_neTop
  have hsum_as_images :
      chartOrderSum CRS (fun x => f x - c₀)
        (chartMeromorphic_sub_const c₀ hf)
        (chartOrderSupport_sub_const_finite CRS f c₀ hf) =
      tP.sum (fun pp => (Ipp pp).sum (G pp)) := by
    rw [hsum_def, hsum_partition]
    refine Finset.sum_congr rfl ?_
    intro pp hpp
    simpa [Ipp, hIpp_def] using hTsub_sum_image pp
  have hzero_outside :
      ∀ pp : {p // p ∈ hpole_fin.toFinset}, ∀ z ∈ Spp pp, z ∉ Ipp pp → G pp z = 0 := by
    intro pp z hzS hzNotI
    by_cases hz0 :
        meromorphicOrderAt
          (fun w => chartRep (RS := CRS.toRiemannSurface) f pp.1 w - c₀) z = 0
    · unfold G
      rw [hz0]
      rfl
    · by_cases hzTop :
          meromorphicOrderAt
            (fun w => chartRep (RS := CRS.toRiemannSurface) f pp.1 w - c₀) z = ⊤
      · unfold G
        rw [hzTop]
        rfl
      · have hzBall :
          ‖z - chartPt (RS := CRS.toRiemannSurface) pp.1‖ < r pp := hS_ball pp z hzS
        have hzTargetU :
            z ∈ (extChartAt 𝓘(ℂ, ℂ) pp.1).target ∧
            (extChartAt 𝓘(ℂ, ℂ) pp.1).symm z ∈ U pp.1 :=
          hρ_prop pp z (lt_of_lt_of_le hzBall (hr_leρ pp))
        let q : CRS.toRiemannSurface.carrier := (extChartAt 𝓘(ℂ, ℂ) pp.1).symm z
        have hqSrc : q ∈ (extChartAt 𝓘(ℂ, ℂ) pp.1).source := by
          exact (extChartAt 𝓘(ℂ, ℂ) pp.1).map_target hzTargetU.1
        have hzEq : extChartAt 𝓘(ℂ, ℂ) pp.1 q = z := by
          change (extChartAt 𝓘(ℂ, ℂ) pp.1) ((extChartAt 𝓘(ℂ, ℂ) pp.1).symm z) = z
          exact (extChartAt 𝓘(ℂ, ℂ) pp.1).right_inv hzTargetU.1
        have hqBallMem :
            extChartAt 𝓘(ℂ, ℂ) pp.1 q ∈
              Metric.ball (chartPt (RS := CRS.toRiemannSurface) pp.1) (r pp) := by
          have hqBallNorm :
              ‖extChartAt 𝓘(ℂ, ℂ) pp.1 q - chartPt (RS := CRS.toRiemannSurface) pp.1‖ < r pp := by
            rw [hzEq]
            exact hzBall
          change dist (extChartAt 𝓘(ℂ, ℂ) pp.1 q)
              (chartPt (RS := CRS.toRiemannSurface) pp.1) < r pp
          simpa [dist_eq_norm] using hqBallNorm
        have hqV : q ∈ V pp := by
          exact ⟨hqSrc, hqBallMem⟩
        have hqEChart : q ∈ (eChart pp.1).source := by
          change q ∈ (extChartAt 𝓘(ℂ, ℂ) pp.1).source
          exact hqSrc
        have horder_eq :
            chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c₀) q =
              meromorphicOrderAt
                (fun w => chartRep (RS := CRS.toRiemannSurface) f pp.1 w - c₀) z := by
          rw [chartOrderAt_eq_in_chart (RS := CRS.toRiemannSurface) (fun x => f x - c₀) pp.1 q
            (chartMeromorphic_sub_const c₀ hf) hqEChart, chartRep_sub_const, hzEq]
        have hqSupp :
            q ∈ chartOrderSupport (RS := CRS.toRiemannSurface) (fun x => f x - c₀) := by
          refine ⟨?_, ?_⟩
          · intro hq0
            exact hz0 (horder_eq.symm.trans hq0)
          · intro hqTop
            exact hzTop (horder_eq.symm.trans hqTop)
        have hqSuppc : q ∈ suppc := by
          simpa [suppc, hsuppc_def] using
            (chartOrderSupport_sub_const_finite CRS f c₀ hf).mem_toFinset.mpr hqSupp
        have hqT : q ∈ Tsub pp := Finset.mem_filter.mpr ⟨hqSuppc, hqV⟩
        have hzI : z ∈ Ipp pp := by
          refine Finset.mem_image.mpr ⟨q, hqT, ?_⟩
          simpa [q] using hzEq
        exact (hzNotI hzI).elim
  have himages_eq_locals :
      tP.sum (fun pp => (Ipp pp).sum (G pp)) =
        tP.sum (fun pp => (Spp pp).sum (G pp)) := by
    refine Finset.sum_congr rfl ?_
    intro pp hpp
    have hsubset : Ipp pp ⊆ Spp pp := by
      intro z hz
      exact hIpp_subset_Spp pp z hz
    have hsum_subset :
        (Ipp pp).sum (G pp) = (Spp pp).sum (G pp) :=
      Finset.sum_subset hsubset (hzero_outside pp)
    exact hsum_subset
  have hsum_locals_zero : tP.sum (fun pp => (Spp pp).sum (G pp)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro pp hpp
    exact hS_sum pp
  refine ⟨c₀, ?_⟩
  calc
    chartOrderSum CRS (fun x => f x - c₀)
        (chartMeromorphic_sub_const c₀ hf)
        (chartOrderSupport_sub_const_finite CRS f c₀ hf)
        = tP.sum (fun pp => (Ipp pp).sum (G pp)) := hsum_as_images
    _ = tP.sum (fun pp => (Spp pp).sum (G pp)) := himages_eq_locals
    _ = 0 := hsum_locals_zero
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


end RiemannSurfaces.Analytic
