import StringGeometry.RiemannSurfaces.Analytic.Helpers.ChartMeromorphic
import StringGeometry.RiemannSurfaces.Analytic.Helpers.ChartTransition
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Analytic Extension for Meromorphic Functions with Nonneg Order

When a meromorphic function has order ≥ 0 at a point (removable singularity or analytic zero),
there exists an analytic function agreeing with it on a punctured neighborhood.

This infrastructure is used for:
- The maximum principle on compact Riemann surfaces
- Proving chartOrderSum is locally constant
- Proving chartOrderSum = 0 for large c₀

## Main Results

* `exists_analyticExtension_of_nonneg_order` - analytic extension at a single point
* `correctedValue` - the "true value" of a meromorphic function with nonneg order
* `correctedValue_tendsto` - the corrected value is the limit
-/

namespace RiemannSurfaces.Analytic

open Complex Topology Classical Filter
open scoped Manifold Topology

variable {RS : RiemannSurface}

/-!
## Part 1: Analytic Extension at a Point

For a meromorphic function with 0 ≤ order ≠ ⊤, we construct an analytic function
that agrees with the original on a punctured neighborhood.
-/

/-- For a meromorphic function with nonneg finite order, there exists an analytic function
    that agrees with it on a punctured neighborhood.

    If the order is n ≥ 0, the original function satisfies f =ᶠ (z - x)^n • g
    with g analytic. The analytic extension is simply (z - x)^n • g, which is analytic
    since n ≥ 0. -/
theorem exists_analyticExtension_of_nonneg_order {f : ℂ → ℂ} {x : ℂ}
    (hf : MeromorphicAt f x)
    (hne_top : meromorphicOrderAt f x ≠ ⊤)
    (hord : (0 : WithTop ℤ) ≤ meromorphicOrderAt f x) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g x ∧
      f =ᶠ[nhdsWithin x {x}ᶜ] g ∧
      meromorphicOrderAt g x = meromorphicOrderAt f x := by
  -- Get the normal form: f =ᶠ (· - x)^n • h with h analytic, h(x) ≠ 0
  obtain ⟨h, h_ana, h_ne, h_eq⟩ := (meromorphicOrderAt_ne_top_iff hf).mp hne_top
  set n := (meromorphicOrderAt f x).untop₀ with hn_def
  -- n ≥ 0 since order ≥ 0
  have hn_nonneg : 0 ≤ n := by
    rw [hn_def]
    exact (WithTop.untop₀_nonneg).2 hord
  -- Lift n to ℕ
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hn_nonneg
  -- The analytic extension is g(z) = (z - x)^m • h(z)
  refine ⟨fun z => (z - x) ^ m • h z, ?_, ?_, ?_⟩
  · -- g is AnalyticAt
    exact ((analyticAt_id.sub analyticAt_const).pow m).smul h_ana
  · -- f =ᶠ[nhdsWithin x {x}ᶜ] g
    filter_upwards [h_eq] with z hz
    rw [hz]
    congr 1
    rw [← zpow_natCast, hm]
  · -- meromorphicOrderAt g x = meromorphicOrderAt f x
    -- f and g agree on the punctured neighborhood, so their orders are equal
    have hg_eq : f =ᶠ[nhdsWithin x {x}ᶜ] fun z => (z - x) ^ m • h z := by
      filter_upwards [h_eq] with z hz
      rw [hz]; congr 1; rw [← zpow_natCast, hm]
    exact (meromorphicOrderAt_congr hg_eq).symm

/-- The "corrected value" of a meromorphic function with nonneg finite order at a point.
    This is the limit of the function in the punctured neighborhood, which exists
    by `tendsto_nhds_of_meromorphicOrderAt_nonneg`. -/
noncomputable def correctedValue {f : ℂ → ℂ} {x : ℂ}
    (hf : MeromorphicAt f x) (hord : (0 : WithTop ℤ) ≤ meromorphicOrderAt f x) : ℂ :=
  (tendsto_nhds_of_meromorphicOrderAt_nonneg hf (by exact_mod_cast hord)).choose

/-- The corrected value is the limit of f at x (in punctured neighborhood). -/
theorem correctedValue_tendsto {f : ℂ → ℂ} {x : ℂ}
    (hf : MeromorphicAt f x) (hord : (0 : WithTop ℤ) ≤ meromorphicOrderAt f x) :
    Tendsto f (nhdsWithin x {x}ᶜ) (nhds (correctedValue hf hord)) :=
  (tendsto_nhds_of_meromorphicOrderAt_nonneg hf (by exact_mod_cast hord)).choose_spec

/-- If the order is positive, the corrected value is 0. -/
theorem correctedValue_eq_zero_of_pos {f : ℂ → ℂ} {x : ℂ}
    (hf : MeromorphicAt f x) (hord : (0 : WithTop ℤ) < meromorphicOrderAt f x) :
    correctedValue hf (le_of_lt hord) = 0 := by
  have htend := correctedValue_tendsto hf (le_of_lt hord)
  have htend0 : Tendsto f (nhdsWithin x {x}ᶜ) (nhds 0) :=
    tendsto_zero_of_meromorphicOrderAt_pos (by exact_mod_cast hord)
  exact tendsto_nhds_unique htend htend0

/-- If the order is 0, the corrected value is nonzero. -/
theorem correctedValue_ne_zero_of_eq_zero {f : ℂ → ℂ} {x : ℂ}
    (hf : MeromorphicAt f x) (hord : meromorphicOrderAt f x = 0) :
    correctedValue hf (by rw [hord]) ≠ 0 := by
  have htend := correctedValue_tendsto hf (by rw [hord])
  obtain ⟨c, hc_ne, hc_tend⟩ :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hf).mpr hord
  have heq := tendsto_nhds_unique htend hc_tend
  rw [heq]; exact hc_ne

/-- If g is analytic at x and agrees with f on a punctured neighborhood,
    then the corrected value equals g(x). -/
theorem correctedValue_eq_of_analyticAt_agree {f g : ℂ → ℂ} {x : ℂ}
    (hf : MeromorphicAt f x) (hord : (0 : WithTop ℤ) ≤ meromorphicOrderAt f x)
    (hg : AnalyticAt ℂ g x) (hagree : f =ᶠ[nhdsWithin x {x}ᶜ] g) :
    correctedValue hf hord = g x := by
  haveI : Filter.NeBot (nhdsWithin x ({x}ᶜ : Set ℂ)) :=
    ConnectedSpace.neBot_nhdsWithin_compl_of_nontrivial_of_t1space x
  have htend := correctedValue_tendsto hf hord
  have htend_g : Tendsto f (nhdsWithin x {x}ᶜ) (nhds (g x)) :=
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hagree.symm
  exact tendsto_nhds_unique htend htend_g

/-!
## Part 2: Corrected Function on Riemann Surface

For a chart-meromorphic function with all orders ≥ 0 and ≠ ⊤ on a compact RS,
the "corrected function" has the right limiting behavior.
-/

/-- The corrected function on a Riemann surface: at each point p, take the limit
    of chartRep f p at chartPt p. -/
noncomputable def correctedFn (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hno_pole : ∀ q, (0 : WithTop ℤ) ≤
      chartOrderAt (RS := CRS.toRiemannSurface) f q) :
    CRS.toRiemannSurface.carrier → ℂ :=
  fun p => correctedValue (hf p) (hno_pole p)

/-- The corrected function has the right limiting behavior: the chart representative
    of the original function converges to the corrected value at each point. -/
theorem correctedFn_tendsto (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hno_pole : ∀ q, (0 : WithTop ℤ) ≤
      chartOrderAt (RS := CRS.toRiemannSurface) f q) (p : CRS.toRiemannSurface.carrier) :
    let z₀ := chartPt (RS := CRS.toRiemannSurface) p
    Tendsto (chartRep (RS := CRS.toRiemannSurface) f p)
      (nhdsWithin z₀ {z₀}ᶜ)
      (nhds (correctedFn CRS f hf hno_pole p)) :=
  correctedValue_tendsto (hf p) (hno_pole p)

/-- Near each point, correctedFn agrees with an analytic function composed with the chart.
    Specifically, ∃ g analytic at chartPt p₀ with correctedFn =ᶠ g ∘ (extChartAt p₀) near p₀. -/
theorem correctedFn_locally_eq_analytic (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hne_top : ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) f q ≠ ⊤)
    (hno_pole : ∀ q, (0 : WithTop ℤ) ≤
      chartOrderAt (RS := CRS.toRiemannSurface) f q)
    (p₀ : CRS.toRiemannSurface.carrier) :
    letI : TopologicalSpace CRS.toRiemannSurface.carrier := CRS.toRiemannSurface.topology
    letI : ChartedSpace ℂ CRS.toRiemannSurface.carrier := CRS.toRiemannSurface.chartedSpace
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (extChartAt 𝓘(ℂ, ℂ) p₀ p₀) ∧
      correctedFn CRS f hf hno_pole =ᶠ[nhds p₀]
        (fun q => g (extChartAt 𝓘(ℂ, ℂ) p₀ q)) ∧
      meromorphicOrderAt g (chartPt (RS := CRS.toRiemannSurface) p₀) =
        chartOrderAt (RS := CRS.toRiemannSurface) f p₀ := by
  letI := CRS.toRiemannSurface.topology
  letI := CRS.toRiemannSurface.chartedSpace
  haveI := CRS.toRiemannSurface.isManifold
  haveI := CRS.toRiemannSurface.t2
  haveI := CRS.toRiemannSurface.connected
  obtain ⟨g, hg_ana, hg_agree, hg_ord⟩ := exists_analyticExtension_of_nonneg_order
    (hf p₀) (hne_top p₀) (hno_pole p₀)
  refine ⟨g, hg_ana, ?_, hg_ord⟩
  -- Extract the open set where g agrees with chartRep f p₀
  have hg_agree' : ∀ᶠ z in nhdsWithin (chartPt (RS := CRS.toRiemannSurface) p₀)
      {chartPt (RS := CRS.toRiemannSurface) p₀}ᶜ,
      chartRep (RS := CRS.toRiemannSurface) f p₀ z = g z := hg_agree
  rw [eventually_nhdsWithin_iff] at hg_agree'
  obtain ⟨U_g, hU_g_sub, hU_g_open, hU_g_mem⟩ := eventually_nhds_iff.mp hg_agree'
  set e₀ := extChartAt 𝓘(ℂ, ℂ) p₀
  -- g is analytic on a neighborhood of chartPt p₀
  obtain ⟨V_ana, hV_ana_sub, hV_ana_open, hV_ana_mem⟩ :=
    eventually_nhds_iff.mp hg_ana.eventually_analyticAt
  -- Build the open manifold neighborhood
  have hsrc₀ : e₀.source ∈ nhds p₀ :=
    (isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) p₀).mem_nhds (mem_extChartAt_source p₀)
  have hpre_Ug : e₀ ⁻¹' U_g ∈ nhds p₀ :=
    (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) p₀).preimage_mem_nhds
      (hU_g_open.mem_nhds hU_g_mem)
  have hpre_V : e₀ ⁻¹' V_ana ∈ nhds p₀ :=
    (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) p₀).preimage_mem_nhds
      (hV_ana_open.mem_nhds hV_ana_mem)
  rw [Filter.EventuallyEq]
  apply Filter.Eventually.mono (Filter.inter_mem hsrc₀ (Filter.inter_mem hpre_Ug hpre_V))
  intro q ⟨hq_src, hq_Ug, hq_V⟩
  show correctedFn CRS f hf hno_pole q = g (e₀ q)
  -- Set up chart at q and chart transition T : ℂ → ℂ
  set e_q := extChartAt 𝓘(ℂ, ℂ) q
  set T := chartTransition (RS := CRS.toRiemannSurface) p₀ q
  haveI : Filter.NeBot (nhdsWithin (e_q q) ({e_q q}ᶜ : Set ℂ)) :=
    ConnectedSpace.neBot_nhdsWithin_compl_of_nontrivial_of_t1space _
  have hq_tgt : e_q q ∈ e_q.target := e_q.map_source (mem_extChartAt_source q)
  have hq_ovlp : e_q.symm (e_q q) ∈ e₀.source := by
    rw [e_q.left_inv (mem_extChartAt_source q)]; exact hq_src
  have hT_val : T (e_q q) = e₀ q := by
    simp only [T, chartTransition, Function.comp_apply]
    congr 1; exact e_q.left_inv (mem_extChartAt_source q)
  have hT_ana : AnalyticAt ℂ T (e_q q) :=
    chartTransition_analyticAt p₀ q (e_q q) hq_tgt hq_ovlp
  have hg_ana_T : AnalyticAt ℂ g (T (e_q q)) := hT_val ▸ hV_ana_sub (e₀ q) hq_V
  have hgT_ana : AnalyticAt ℂ (g ∘ T) (e_q q) := hg_ana_T.comp hT_ana
  have hgT_val : (g ∘ T) (e_q q) = g (e₀ q) := by simp [Function.comp, hT_val]
  rw [show correctedFn CRS f hf hno_pole q = correctedValue (hf q) (hno_pole q) from rfl,
      ← hgT_val]
  apply correctedValue_eq_of_analyticAt_agree (hf q) (hno_pole q) hgT_ana
  have h_symm_src : ∀ᶠ w in nhds (e_q q), e_q.symm w ∈ e₀.source := by
    apply (continuousAt_extChartAt_symm'' (I := 𝓘(ℂ, ℂ)) hq_tgt).eventually
    rw [e_q.left_inv (mem_extChartAt_source q)]
    exact (isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) p₀).mem_nhds hq_src
  have h_T_Ug : ∀ᶠ w in nhds (e_q q), T w ∈ U_g :=
    hT_ana.continuousAt.eventually (hU_g_open.mem_nhds (hT_val ▸ hq_Ug))
  have h_w_tgt : ∀ᶠ w in nhds (e_q q), w ∈ e_q.target :=
    (isOpen_extChartAt_target (I := 𝓘(ℂ, ℂ)) q).mem_nhds hq_tgt
  have h_T_ne : ∀ᶠ w in nhdsWithin (e_q q) {e_q q}ᶜ,
      T w ≠ chartPt (RS := CRS.toRiemannSurface) p₀ := by
    by_cases hqp : T (e_q q) = chartPt (RS := CRS.toRiemannSurface) p₀
    · have hT_deriv_ne := chartTransition_deriv_ne_zero
        (RS := CRS.toRiemannSurface) p₀ q (e_q q) hq_tgt hq_ovlp
      rw [← hqp]
      exact hT_ana.differentiableAt.hasDerivAt.eventually_ne hT_deriv_ne
    · apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
      exact hT_ana.continuousAt.eventually
        (isOpen_compl_singleton.mem_nhds hqp)
  apply h_T_ne.mp
  apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
  apply (h_symm_src.and (h_T_Ug.and h_w_tgt)).mono
  intro w ⟨hw_src, hw_Ug, _⟩ hw_T_ne
  show chartRep (RS := CRS.toRiemannSurface) f q w = (g ∘ T) w
  simp only [chartRep, Function.comp_apply]
  have h_left_inv : e₀.symm (T w) = e_q.symm w := by
    simp only [T, chartTransition, Function.comp_apply]
    exact e₀.left_inv hw_src
  rw [show f (e_q.symm w) = f (e₀.symm (T w)) by rw [h_left_inv]]
  exact hU_g_sub (T w) hw_Ug hw_T_ne

/-- The corrected function agrees with the original on the meromorphic orders:
    chartOrderAt f p = chartOrderAt (correctedFn) p, because the functions agree on
    punctured neighborhoods. -/
theorem correctedFn_same_order (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hno_pole : ∀ q, (0 : WithTop ℤ) ≤
      chartOrderAt (RS := CRS.toRiemannSurface) f q)
    (p : CRS.toRiemannSurface.carrier) :
    chartOrderAt (RS := CRS.toRiemannSurface) f p =
      chartOrderAt (RS := CRS.toRiemannSurface) (correctedFn CRS f hf hno_pole) p := by
  letI := CRS.toRiemannSurface.topology
  letI := CRS.toRiemannSurface.chartedSpace
  haveI := CRS.toRiemannSurface.isManifold
  haveI := CRS.toRiemannSurface.t2
  haveI := CRS.toRiemannSurface.connected
  by_cases h_exists : ∃ q₀, chartOrderAt (RS := CRS.toRiemannSurface) f q₀ ≠ ⊤
  · -- Case: some order ≠ ⊤ → all orders ≠ ⊤ by identity principle
    obtain ⟨q₀, hq₀⟩ := h_exists
    have hne_top : ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) f q ≠ ⊤ :=
      fun q => chartOrderAt_ne_top_of_ne_top_somewhere f hf q₀ hq₀ q
    -- Get g analytic with correctedFn =ᶠ g ∘ e near p AND order equality
    obtain ⟨g, _, hcf_eq, hg_ord⟩ :=
      correctedFn_locally_eq_analytic CRS f hf hne_top hno_pole p
    -- Derive: chartRep (correctedFn) p =ᶠ[nhdsWithin (chartPt p) {chartPt p}ᶜ] g
    set e₀ := extChartAt 𝓘(ℂ, ℂ) p
    have hmem_tgt : e₀ p ∈ e₀.target := e₀.map_source (mem_extChartAt_source p)
    -- Transfer hcf_eq through e₀.symm to get agreement in chart coordinates
    have h_cf_g_nhds : ∀ᶠ z in nhds (e₀ p),
        correctedFn CRS f hf hno_pole (e₀.symm z) = g z := by
      have h_cont := continuousAt_extChartAt_symm'' (I := 𝓘(ℂ, ℂ)) hmem_tgt
      rw [ContinuousAt, e₀.left_inv (mem_extChartAt_source p)] at h_cont
      have h1 := h_cont.eventually hcf_eq
      -- h1 : correctedFn(e₀.symm z) = g(e₀(e₀.symm z)) eventually
      have h2 : ∀ᶠ z in nhds (e₀ p), z ∈ e₀.target :=
        (isOpen_extChartAt_target (I := 𝓘(ℂ, ℂ)) p).mem_nhds hmem_tgt
      exact (h1.and h2).mono fun z ⟨hz1, hz2⟩ => by
        dsimp only at hz1; rwa [e₀.right_inv hz2] at hz1
    -- chartRep (correctedFn) p agrees with g on punctured nhd
    have h_cf_g : chartRep (RS := CRS.toRiemannSurface) (correctedFn CRS f hf hno_pole) p
        =ᶠ[nhdsWithin (chartPt (RS := CRS.toRiemannSurface) p)
          {chartPt (RS := CRS.toRiemannSurface) p}ᶜ] g :=
      h_cf_g_nhds.filter_mono nhdsWithin_le_nhds
    -- Chain the order equalities
    rw [← hg_ord, show chartOrderAt (correctedFn CRS f hf hno_pole) p =
        meromorphicOrderAt (chartRep (RS := CRS.toRiemannSurface)
          (correctedFn CRS f hf hno_pole) p)
          (chartPt (RS := CRS.toRiemannSurface) p) from rfl]
    exact (meromorphicOrderAt_congr h_cf_g).symm
  · -- Case: all orders = ⊤
    push_neg at h_exists
    -- h_exists : ∀ q, chartOrderAt f q = ⊤
    -- correctedFn ≡ 0 since all orders are ⊤ (positive order ⟹ correctedValue = 0)
    have h_cf_zero : ∀ q, correctedFn CRS f hf hno_pole q = 0 := by
      intro q
      have hord : (0 : WithTop ℤ) < chartOrderAt (RS := CRS.toRiemannSurface) f q := by
        rw [h_exists q]; exact WithTop.coe_lt_top 0
      exact correctedValue_eq_zero_of_pos (hf q) hord
    -- LHS = ⊤
    rw [h_exists p]
    -- RHS: chartRep of zero function has order ⊤
    symm
    show chartOrderAt (RS := CRS.toRiemannSurface) (correctedFn CRS f hf hno_pole) p = ⊤
    rw [show chartOrderAt (RS := CRS.toRiemannSurface) (correctedFn CRS f hf hno_pole) p =
        meromorphicOrderAt (chartRep (RS := CRS.toRiemannSurface)
          (correctedFn CRS f hf hno_pole) p)
          (chartPt (RS := CRS.toRiemannSurface) p) from rfl,
      meromorphicOrderAt_eq_top_iff]
    exact Eventually.of_forall (fun z => h_cf_zero _)

/-- The corrected function is continuous on M.

    In each chart, the corrected function equals the analytic extension of chartRep f p,
    which is analytic (hence continuous). -/
theorem correctedFn_continuous (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hne_top : ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) f q ≠ ⊤)
    (hno_pole : ∀ q, (0 : WithTop ℤ) ≤
      chartOrderAt (RS := CRS.toRiemannSurface) f q) :
    @Continuous _ _ CRS.toRiemannSurface.topology _ (correctedFn CRS f hf hno_pole) := by
  letI := CRS.toRiemannSurface.topology
  letI := CRS.toRiemannSurface.chartedSpace
  haveI := CRS.toRiemannSurface.isManifold
  rw [continuous_iff_continuousAt]
  intro p₀
  obtain ⟨g, hg_ana, heq, _⟩ := correctedFn_locally_eq_analytic CRS f hf hne_top hno_pole p₀
  have hφ_cont : ContinuousAt (fun q => g (extChartAt 𝓘(ℂ, ℂ) p₀ q)) p₀ := by
    apply ContinuousAt.comp _ (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) p₀)
    exact hg_ana.continuousAt
  exact hφ_cont.congr heq.symm

/-- The corrected function is bounded on a compact Riemann surface.
    This is an immediate consequence of continuity + compactness. -/
theorem correctedFn_bounded (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hne_top : ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) f q ≠ ⊤)
    (hno_pole : ∀ q, (0 : WithTop ℤ) ≤
      chartOrderAt (RS := CRS.toRiemannSurface) f q) :
    ∃ C : ℝ, ∀ p, ‖correctedFn CRS f hf hno_pole p‖ ≤ C := by
  letI : TopologicalSpace CRS.toRiemannSurface.carrier := CRS.toRiemannSurface.topology
  haveI : CompactSpace CRS.toRiemannSurface.carrier := CRS.compact
  have hcont := correctedFn_continuous CRS f hf hne_top hno_pole
  have hcomp : IsCompact (Set.univ : Set CRS.toRiemannSurface.carrier) := isCompact_univ
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hcont.continuousOn
  exact ⟨C, fun p => hC p (Set.mem_univ _)⟩

/-!
## Part 3: Maximum Principle for Compact Riemann Surfaces

On a compact connected Riemann surface, a chart-meromorphic function with all
orders ≥ 0 and ≠ ⊤ must have all orders equal to 0.

Equivalently: a holomorphic function on a compact connected RS is constant.
-/

/-- The corrected function on a compact connected RS with all nonneg orders is constant.

    **Proof**: The corrected function is continuous and analytic in charts.
    If non-constant, it is an open map (by the open mapping theorem). But a continuous
    function from a compact space to ℂ has compact image, while an open map has
    open image. A nonempty subset of ℂ that is both open and compact is impossible
    (since ℂ is connected and not compact). Hence the function is constant. -/
theorem correctedFn_constant (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hne_top : ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) f q ≠ ⊤)
    (hno_pole : ∀ q, (0 : WithTop ℤ) ≤
      chartOrderAt (RS := CRS.toRiemannSurface) f q) :
    ∃ a : ℂ, ∀ p, correctedFn CRS f hf hno_pole p = a := by
  letI := CRS.toRiemannSurface.topology
  letI := CRS.toRiemannSurface.chartedSpace
  haveI := CRS.toRiemannSurface.isManifold
  haveI := CRS.toRiemannSurface.t2
  haveI := CRS.toRiemannSurface.connected
  haveI : CompactSpace CRS.toRiemannSurface.carrier := CRS.compact
  set F := correctedFn CRS f hf hno_pole
  have hF_cont := correctedFn_continuous CRS f hf hne_top hno_pole
  -- ‖F‖ achieves maximum at some p_max (compact + continuous)
  obtain ⟨p_max, _, hmax⟩ := (isCompact_univ (X := CRS.toRiemannSurface.carrier)).exists_isMaxOn
    Set.univ_nonempty hF_cont.norm.continuousOn
  -- S = {q | F q = F p_max} is clopen → S = univ → F is constant
  use F p_max; intro q
  have hS_closed : IsClosed {q : CRS.toRiemannSurface.carrier | F q = F p_max} :=
    isClosed_singleton.preimage hF_cont
  -- Key: S is open (maximum modulus principle in each chart)
  have hS_open : IsOpen {q : CRS.toRiemannSurface.carrier | F q = F p_max} := by
    rw [isOpen_iff_forall_mem_open]
    intro q₀ (hq₀ : F q₀ = F p_max)
    -- Get the local analytic representation: F =ᶠ g ∘ (extChartAt q₀) near q₀
    obtain ⟨g, hg_ana, heq, _⟩ := correctedFn_locally_eq_analytic CRS f hf hne_top hno_pole q₀
    set e₀ := extChartAt 𝓘(ℂ, ℂ) q₀
    have hval : F q₀ = g (e₀ q₀) := heq.self_of_nhds
    -- g is differentiable near chartPt q₀
    have hg_diff : ∀ᶠ z in nhds (e₀ q₀), DifferentiableAt ℂ g z :=
      hg_ana.eventually_analyticAt.mono fun z hz => hz.differentiableAt
    -- ‖g‖ has local max at e₀ q₀:
    -- From heq, F(r) = g(e₀ r) near q₀, so ‖g(e₀ r)‖ = ‖F(r)‖ ≤ ‖F p_max‖ = ‖g(e₀ q₀)‖
    have hg_max : IsLocalMax (fun z => ‖g z‖) (e₀ q₀) := by
      -- First bound on nhds q₀, then transfer to nhds (e₀ q₀)
      have hbnd : ∀ᶠ r in nhds q₀, ‖g (e₀ r)‖ ≤ ‖g (e₀ q₀)‖ := by
        apply heq.mono; intro r hr
        -- hr : F r = g (e₀ r), so ‖g(e₀ r)‖ = ‖F r‖ ≤ ‖F p_max‖ = ‖F q₀‖ = ‖g(e₀ q₀)‖
        calc ‖g (e₀ r)‖ = ‖F r‖ := by rw [show F r = g (e₀ r) from hr]
          _ ≤ ‖F p_max‖ := hmax (Set.mem_univ r)
          _ = ‖g (e₀ q₀)‖ := by rw [← hq₀, hval]
      -- Transfer via extChartAt map: map e₀ (nhds q₀) = nhds (e₀ q₀)
      have hmap : Filter.map e₀ (nhds q₀) = nhds (e₀ q₀) :=
        map_extChartAt_nhds_of_boundaryless (I := 𝓘(ℂ, ℂ)) q₀
      rw [IsLocalMax, IsMaxFilter, ← hmap, Filter.eventually_map]
      exact hbnd
    -- Maximum modulus principle: g locally constant near e₀ q₀
    have hg_const : ∀ᶠ z in nhds (e₀ q₀), g z = g (e₀ q₀) :=
      Complex.eventually_eq_of_isLocalMax_norm hg_diff hg_max
    -- Transfer back: F locally constant near q₀
    have hF_const : ∀ᶠ r in nhds q₀, F r = F p_max := by
      apply (heq.and ((continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) q₀).eventually hg_const)).mono
      intro r ⟨hr_eq, hr_const⟩
      -- hr_eq : F r = g(e₀ r), hr_const : g(e₀ r) = g(e₀ q₀)
      calc F r = g (e₀ r) := hr_eq
        _ = g (e₀ q₀) := hr_const
        _ = F q₀ := hval.symm
        _ = F p_max := hq₀
    -- Extract the open set
    obtain ⟨V, hV_sub, hV_open, hV_mem⟩ := mem_nhds_iff.mp hF_const
    exact ⟨V, fun r hr => hV_sub hr, hV_open, hV_mem⟩
  -- Clopen + connected + nonempty → S = univ
  have hS_ne : ({q : CRS.toRiemannSurface.carrier | F q = F p_max}).Nonempty := ⟨p_max, rfl⟩
  exact Set.eq_univ_iff_forall.mp (IsClopen.eq_univ ⟨hS_closed, hS_open⟩ hS_ne) q

end RiemannSurfaces.Analytic
