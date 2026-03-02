import StringGeometry.RiemannSurfaces.Analytic.Helpers.ArgumentPrinciple.DegreeTheory

namespace RiemannSurfaces.Analytic

open Complex Topology Classical Filter
open scoped Manifold Topology
open scoped BigOperators

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

/-- For a chart-meromorphic `f` nonconstant on its regular locus, every shift `f - c`
    has vanishing chart-order sum. This packages the argument-principle theorem in the
    shifted form needed in fiber-multiplicity/degree arguments. -/
theorem chartOrderSum_sub_const_eq_zero_of_nonconstant_regularLocus
    (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hnc : ¬ ∀ p q, p ∈ regularLocus (RS := CRS.toRiemannSurface) f →
      q ∈ regularLocus (RS := CRS.toRiemannSurface) f → f p = f q) :
    ∀ c : ℂ,
      chartOrderSum CRS (fun x => f x - c)
        (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c hf)
        (chartOrderSupport_sub_const_finite CRS f c hf) = 0 := by
  intro c
  obtain ⟨p, hpne⟩ := exists_ne_value_of_nonconstant_regularLocus
    (RS := CRS.toRiemannSurface) f hnc c
  have hne_shift : ∃ q, (fun x => f x - c) q ≠ 0 := ⟨p, by simpa [sub_eq_zero] using hpne⟩
  exact chartOrderSum_eq_zero CRS (fun x => f x - c)
    (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c hf)
    (chartOrderSupport_sub_const_finite CRS f c hf) hne_shift

/-- Reduction principle for `fiberMultiplicity_constant`.
    Once fiber multiplicity is identified with the shifted chart-order sum,
    constancy follows immediately from the shifted argument principle. -/
theorem fiberMultiplicity_constant_of_chartOrderSum_bridge
    (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hnc : ¬ ∀ p q, p ∈ regularLocus (RS := CRS.toRiemannSurface) f →
      q ∈ regularLocus (RS := CRS.toRiemannSurface) f → f p = f q)
    (hbridge :
      ∀ (c : ℂ)
        (hfib : {p : CRS.toRiemannSurface.carrier |
          f p = c ∧ (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p}.Finite),
        fiberMultiplicity CRS f c hfib =
          chartOrderSum CRS (fun x => f x - c)
            (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c hf)
            (chartOrderSupport_sub_const_finite CRS f c hf)) :
    ∀ (c₁ c₂ : ℂ)
      (hfib₁ : {p : CRS.toRiemannSurface.carrier |
        f p = c₁ ∧ (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p}.Finite)
      (hfib₂ : {p : CRS.toRiemannSurface.carrier |
        f p = c₂ ∧ (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p}.Finite),
      fiberMultiplicity CRS f c₁ hfib₁ = fiberMultiplicity CRS f c₂ hfib₂ := by
  intro c₁ c₂ hfib₁ hfib₂
  have hsum₁ :
      chartOrderSum CRS (fun x => f x - c₁)
        (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c₁ hf)
        (chartOrderSupport_sub_const_finite CRS f c₁ hf) = 0 :=
    chartOrderSum_sub_const_eq_zero_of_nonconstant_regularLocus CRS f hf hnc c₁
  have hsum₂ :
      chartOrderSum CRS (fun x => f x - c₂)
        (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c₂ hf)
        (chartOrderSupport_sub_const_finite CRS f c₂ hf) = 0 :=
    chartOrderSum_sub_const_eq_zero_of_nonconstant_regularLocus CRS f hf hnc c₂
  calc
    fiberMultiplicity CRS f c₁ hfib₁
        = chartOrderSum CRS (fun x => f x - c₁)
            (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c₁ hf)
            (chartOrderSupport_sub_const_finite CRS f c₁ hf) := hbridge c₁ hfib₁
    _ = 0 := hsum₁
    _ = chartOrderSum CRS (fun x => f x - c₂)
          (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c₂ hf)
          (chartOrderSupport_sub_const_finite CRS f c₂ hf) := hsum₂.symm
    _ = fiberMultiplicity CRS f c₂ hfib₂ := (hbridge c₂ hfib₂).symm

/-- Under regular-point chart continuity, the point-value regular fiber set at `c`
    coincides with the zero set of `f - c`. -/
theorem fiberSet_eq_zeroSet_sub_const_of_continuous_regular
    (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hcont_reg : ∀ p, (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p →
      ContinuousAt (chartRep (RS := CRS.toRiemannSurface) f p)
        (chartPt (RS := CRS.toRiemannSurface) p))
    (c : ℂ)
    (hne_top_shift : ∀ p,
      chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p ≠ ⊤)
    :
    {p : CRS.toRiemannSurface.carrier |
      f p = c ∧ (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p} =
      zeroSet (RS := CRS.toRiemannSurface) (fun x => f x - c) := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨hpEq, hnonneg_f⟩
    have hcont_p : ContinuousAt
        (chartRep (RS := CRS.toRiemannSurface) f p)
        (chartPt (RS := CRS.toRiemannSurface) p) :=
      hcont_reg p hnonneg_f
    have hpos_shift :
        (0 : WithTop ℤ) < chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p :=
      shift_pos_of_eq_const_of_continuousAt (RS := CRS.toRiemannSurface) hf hcont_p hpEq
    exact ⟨hpos_shift, hne_top_shift p⟩
  · intro hp
    rcases hp with ⟨hpos_shift, _hne_top_shift⟩
    have hnonneg_shift :
        (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p :=
      le_of_lt hpos_shift
    have hnonneg_f :
        (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p :=
      (chartOrderAt_sub_const_nonneg_iff (RS := CRS.toRiemannSurface) (f := f) (p := p) c).1
        hnonneg_shift
    have hcont_p : ContinuousAt
        (chartRep (RS := CRS.toRiemannSurface) f p)
        (chartPt (RS := CRS.toRiemannSurface) p) :=
      hcont_reg p hnonneg_f
    have hpEq : f p = c :=
      eq_const_of_shift_pos_of_continuousAt (RS := CRS.toRiemannSurface) hf hcont_p hpos_shift
    exact ⟨hpEq, hnonneg_f⟩

/-- Under regular-point chart continuity, fiber multiplicity equals the shifted zero-order sum. -/
theorem fiberMultiplicity_eq_zeroSum_of_continuous_regular
    (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hcont_reg : ∀ p, (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p →
      ContinuousAt (chartRep (RS := CRS.toRiemannSurface) f p)
        (chartPt (RS := CRS.toRiemannSurface) p))
    (c : ℂ)
    (hne_top_shift : ∀ p,
      chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p ≠ ⊤)
    (hfib : {p : CRS.toRiemannSurface.carrier |
      f p = c ∧ (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p}.Finite) :
    fiberMultiplicity CRS f c hfib =
      (zeroSet_finite CRS (fun x => f x - c)
        (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c hf)
        (chartOrderSupport_sub_const_finite CRS f c hf)).toFinset.sum
          (fun p => (chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p).getD 0) := by
  unfold fiberMultiplicity
  have hset :
      {p : CRS.toRiemannSurface.carrier |
        f p = c ∧ (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p} =
      zeroSet (RS := CRS.toRiemannSurface) (fun x => f x - c) :=
    fiberSet_eq_zeroSet_sub_const_of_continuous_regular CRS f hf hcont_reg c hne_top_shift
  have hfin_eq :
      hfib.toFinset =
        (zeroSet_finite CRS (fun x => f x - c)
          (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c hf)
          (chartOrderSupport_sub_const_finite CRS f c hf)).toFinset := by
    ext p
    simp [Set.Finite.mem_toFinset, hset]
  rw [hfin_eq]

/-- Total pole order of `f - c` is independent of `c`. -/
theorem totalPoleOrder_sub_const_eq_of_chartMeromorphic
    (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (c₁ c₂ : ℂ) :
    totalPoleOrder CRS (fun x => f x - c₁)
      (poleSet_finite CRS (fun x => f x - c₁)
        (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c₁ hf)
        (chartOrderSupport_sub_const_finite CRS f c₁ hf)) =
    totalPoleOrder CRS (fun x => f x - c₂)
      (poleSet_finite CRS (fun x => f x - c₂)
        (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c₂ hf)
        (chartOrderSupport_sub_const_finite CRS f c₂ hf)) := by
  set hpole₁ : (poleSet (RS := CRS.toRiemannSurface) (fun x => f x - c₁)).Finite :=
    poleSet_finite CRS (fun x => f x - c₁)
      (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c₁ hf)
      (chartOrderSupport_sub_const_finite CRS f c₁ hf)
  set hpole₂ : (poleSet (RS := CRS.toRiemannSurface) (fun x => f x - c₂)).Finite :=
    poleSet_finite CRS (fun x => f x - c₂)
      (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c₂ hf)
      (chartOrderSupport_sub_const_finite CRS f c₂ hf)
  have hset :
      poleSet (RS := CRS.toRiemannSurface) (fun x => f x - c₁) =
      poleSet (RS := CRS.toRiemannSurface) (fun x => f x - c₂) := by
    ext p
    exact Iff.trans
      (chartOrderAt_sub_const_lt_zero_iff (RS := CRS.toRiemannSurface)
        (f := f) (p := p) c₁)
      (chartOrderAt_sub_const_lt_zero_iff (RS := CRS.toRiemannSurface)
        (f := f) (p := p) c₂).symm
  have hfin_eq : hpole₁.toFinset = hpole₂.toFinset := by
    ext p
    simp [Set.Finite.mem_toFinset, hset]
  unfold totalPoleOrder
  rw [← hfin_eq]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hpole_shift₁ :
      chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c₁) p < 0 := by
    have hp_mem :
        p ∈ poleSet (RS := CRS.toRiemannSurface) (fun x => f x - c₁) := by
      exact (hpole₁.mem_toFinset.mp hp)
    simpa [poleSet, Set.mem_setOf_eq] using hp_mem
  have hpole_f : chartOrderAt (RS := CRS.toRiemannSurface) f p < 0 :=
    (chartOrderAt_sub_const_lt_zero_iff (RS := CRS.toRiemannSurface)
      (f := f) (p := p) c₁).1 hpole_shift₁
  have hord₁ :
      chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c₁) p =
        chartOrderAt (RS := CRS.toRiemannSurface) f p :=
    chartOrderAt_sub_const_at_pole (RS := CRS.toRiemannSurface) (f := f) (p := p) c₁ hpole_f
  have horder₂ :
      chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c₂) p =
        chartOrderAt (RS := CRS.toRiemannSurface) f p :=
    chartOrderAt_sub_const_at_pole (RS := CRS.toRiemannSurface) (f := f) (p := p) c₂ hpole_f
  rw [hord₁, horder₂]

/-- Under regular-point chart continuity, fiber multiplicity equals total pole order of `f - c`. -/
theorem fiberMultiplicity_eq_totalPoleOrder_sub_const_of_continuous_regular
    (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hcont_reg : ∀ p, (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p →
      ContinuousAt (chartRep (RS := CRS.toRiemannSurface) f p)
        (chartPt (RS := CRS.toRiemannSurface) p))
    (hnc : ¬ ∀ p q, p ∈ regularLocus (RS := CRS.toRiemannSurface) f →
      q ∈ regularLocus (RS := CRS.toRiemannSurface) f → f p = f q)
    (c : ℂ)
    (hfib : {p : CRS.toRiemannSurface.carrier |
      f p = c ∧ (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p}.Finite) :
    fiberMultiplicity CRS f c hfib =
      totalPoleOrder CRS (fun x => f x - c)
        (poleSet_finite CRS (fun x => f x - c)
          (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c hf)
          (chartOrderSupport_sub_const_finite CRS f c hf)) := by
  set Zsum : ℤ :=
    (zeroSet_finite CRS (fun x => f x - c)
      (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c hf)
      (chartOrderSupport_sub_const_finite CRS f c hf)).toFinset.sum
        (fun p => (chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p).getD 0)
  set Psum : ℤ :=
    totalPoleOrder CRS (fun x => f x - c)
      (poleSet_finite CRS (fun x => f x - c)
        (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c hf)
        (chartOrderSupport_sub_const_finite CRS f c hf))
  have hne_top_shift : ∀ p,
      chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p ≠ ⊤ := by
    obtain ⟨p₀, hp₀reg, hp₀ne⟩ := exists_regular_ne_value_of_nonconstant_regularLocus
      (RS := CRS.toRiemannSurface) f hnc c
    have hnonneg₀ :
        (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p₀ := hp₀reg
    have hcont₀ : ContinuousAt
        (chartRep (RS := CRS.toRiemannSurface) f p₀)
        (chartPt (RS := CRS.toRiemannSurface) p₀) :=
      hcont_reg p₀ hnonneg₀
    have hfc : IsChartMeromorphic (RS := CRS.toRiemannSurface) (fun x => f x - c) :=
      chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c hf
    have hrep_sub₀ : chartRep (RS := CRS.toRiemannSurface) (fun x => f x - c) p₀ =
        fun z => chartRep (RS := CRS.toRiemannSurface) f p₀ z - c := by
      ext z
      simp [chartRep, Function.comp]
    have hcont_shift₀ : ContinuousAt
        (chartRep (RS := CRS.toRiemannSurface) (fun x => f x - c) p₀)
        (chartPt (RS := CRS.toRiemannSurface) p₀) := by
      have hcont_sub₀ : ContinuousAt
          (fun z => chartRep (RS := CRS.toRiemannSurface) f p₀ z - c)
          (chartPt (RS := CRS.toRiemannSurface) p₀) := hcont₀.sub continuousAt_const
      simpa [hrep_sub₀] using hcont_sub₀
    have hne_shift₀ : (fun x => f x - c) p₀ ≠ 0 := by
      simpa [sub_eq_zero] using hp₀ne
    have hzero₀ :
        chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p₀ = 0 :=
      chartOrderAt_eq_zero_of_continuousAt_ne_zero (RS := CRS.toRiemannSurface)
        hfc p₀ hcont_shift₀ hne_shift₀
    have hp₀_ne_top :
        chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p₀ ≠ ⊤ := by
      rw [hzero₀]
      exact WithTop.zero_ne_top
    intro p
    exact chartOrderAt_ne_top_of_ne_top_somewhere (RS := CRS.toRiemannSurface)
      (fun x => f x - c) hfc p₀ hp₀_ne_top p
  have hfib_eq_Zsum : fiberMultiplicity CRS f c hfib = Zsum := by
    simpa [Zsum] using
      fiberMultiplicity_eq_zeroSum_of_continuous_regular CRS f hf hcont_reg c
        hne_top_shift hfib
  have hsplit :
      chartOrderSum CRS (fun x => f x - c)
        (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c hf)
        (chartOrderSupport_sub_const_finite CRS f c hf) = Zsum - Psum := by
    simp [Zsum, Psum, chartOrderSum_split]
  have hsum_zero :
      chartOrderSum CRS (fun x => f x - c)
        (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c hf)
        (chartOrderSupport_sub_const_finite CRS f c hf) = 0 :=
    chartOrderSum_sub_const_eq_zero_of_nonconstant_regularLocus CRS f hf hnc c
  have hZ_eq_P : Zsum = Psum := by
    linarith [hsplit, hsum_zero]
  calc
    fiberMultiplicity CRS f c hfib = Zsum := hfib_eq_Zsum
    _ = Psum := hZ_eq_P
    _ = totalPoleOrder CRS (fun x => f x - c)
          (poleSet_finite CRS (fun x => f x - c)
            (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c hf)
            (chartOrderSupport_sub_const_finite CRS f c hf)) := by
          rfl

/-- Continuity-based fiber multiplicity constancy.
    This is the chart-continuous regular-locus variant of `fiberMultiplicity_constant`. -/
theorem fiberMultiplicity_constant_of_continuous_regular
    (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hcont_reg : ∀ p, (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p →
      ContinuousAt (chartRep (RS := CRS.toRiemannSurface) f p)
        (chartPt (RS := CRS.toRiemannSurface) p))
    (hnc : ¬ ∀ p q, p ∈ regularLocus (RS := CRS.toRiemannSurface) f →
      q ∈ regularLocus (RS := CRS.toRiemannSurface) f → f p = f q) :
    ∀ (c₁ c₂ : ℂ)
      (hfib₁ : {p : CRS.toRiemannSurface.carrier |
        f p = c₁ ∧ (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p}.Finite)
      (hfib₂ : {p : CRS.toRiemannSurface.carrier |
        f p = c₂ ∧ (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p}.Finite),
      fiberMultiplicity CRS f c₁ hfib₁ = fiberMultiplicity CRS f c₂ hfib₂ := by
  intro c₁ c₂ hfib₁ hfib₂
  have hfib₁_eq :
      fiberMultiplicity CRS f c₁ hfib₁ =
        totalPoleOrder CRS (fun x => f x - c₁)
          (poleSet_finite CRS (fun x => f x - c₁)
            (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c₁ hf)
            (chartOrderSupport_sub_const_finite CRS f c₁ hf)) :=
    fiberMultiplicity_eq_totalPoleOrder_sub_const_of_continuous_regular
      CRS f hf hcont_reg hnc c₁ hfib₁
  have hfib₂_eq :
      fiberMultiplicity CRS f c₂ hfib₂ =
        totalPoleOrder CRS (fun x => f x - c₂)
          (poleSet_finite CRS (fun x => f x - c₂)
            (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c₂ hf)
            (chartOrderSupport_sub_const_finite CRS f c₂ hf)) :=
    fiberMultiplicity_eq_totalPoleOrder_sub_const_of_continuous_regular
      CRS f hf hcont_reg hnc c₂ hfib₂
  calc
    fiberMultiplicity CRS f c₁ hfib₁
        = totalPoleOrder CRS (fun x => f x - c₁)
            (poleSet_finite CRS (fun x => f x - c₁)
              (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c₁ hf)
              (chartOrderSupport_sub_const_finite CRS f c₁ hf)) := hfib₁_eq
    _ = totalPoleOrder CRS (fun x => f x - c₂)
          (poleSet_finite CRS (fun x => f x - c₂)
            (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c₂ hf)
            (chartOrderSupport_sub_const_finite CRS f c₂ hf)) :=
      totalPoleOrder_sub_const_eq_of_chartMeromorphic CRS f hf c₁ c₂
    _ = fiberMultiplicity CRS f c₂ hfib₂ := hfib₂_eq.symm

/-- If the order is `⊤`, then corrected value is zero. -/
private theorem correctedValue_eq_zero_of_top {g : ℂ → ℂ} {x : ℂ}
    (hg : MeromorphicAt g x)
    (hord : (0 : WithTop ℤ) ≤ meromorphicOrderAt g x)
    (htop : meromorphicOrderAt g x = ⊤) :
    correctedValue hg hord = 0 := by
  have hpos : (0 : WithTop ℤ) < meromorphicOrderAt g x := by
    rw [htop]
    exact lt_of_le_of_ne le_top (by simp)
  exact correctedValue_eq_zero_of_pos hg hpos

/-- Under regular-value compatibility, positive order of `f - c` forces `f p = c`. -/
private theorem eq_const_of_shift_pos_of_regular_value_compat {RS : RiemannSurface}
    {f : RS.carrier → ℂ} {p : RS.carrier} {c : ℂ}
    (hf : IsChartMeromorphic (RS := RS) f)
    (hcompat : ∀ q (hq : (0 : WithTop ℤ) ≤ chartOrderAt (RS := RS) f q),
      f q = correctedValue (hf q) hq)
    (hpos : (0 : WithTop ℤ) < chartOrderAt (RS := RS) (fun x => f x - c) p) :
    f p = c := by
  have hnonneg_shift :
      (0 : WithTop ℤ) ≤ chartOrderAt (RS := RS) (fun x => f x - c) p := le_of_lt hpos
  have hnonneg_f :
      (0 : WithTop ℤ) ≤ chartOrderAt (RS := RS) f p :=
    (chartOrderAt_sub_const_nonneg_iff (RS := RS) (f := f) (p := p) c).1 hnonneg_shift
  have hpos_mord :
      (0 : WithTop ℤ) <
        meromorphicOrderAt
          (fun z => chartRep (RS := RS) f p z - c) (chartPt (RS := RS) p) := by
    simpa [chartOrderAt, chartRep_sub_const] using hpos
  have hcv_eq_c :
      correctedValue (hf p) hnonneg_f = c :=
    correctedValue_eq_const_of_sub_pos (g := chartRep (RS := RS) f p)
      (x := chartPt (RS := RS) p) (c := c) (hg := hf p) (hord_g := hnonneg_f) hpos_mord
  calc
    f p = correctedValue (hf p) hnonneg_f := hcompat p hnonneg_f
    _ = c := hcv_eq_c

/-- Under regular-value compatibility, point-value equality and nonnegative order imply
    nonzero order for the shift `f - c`. -/
private theorem shift_ne_zero_of_eq_const_of_regular_value_compat {RS : RiemannSurface}
    {f : RS.carrier → ℂ} {p : RS.carrier} {c : ℂ}
    (hf : IsChartMeromorphic (RS := RS) f)
    (hcompat : ∀ q (hq : (0 : WithTop ℤ) ≤ chartOrderAt (RS := RS) f q),
      f q = correctedValue (hf q) hq)
    (hnonneg_f : (0 : WithTop ℤ) ≤ chartOrderAt (RS := RS) f p)
    (hEq : f p = c) :
    chartOrderAt (RS := RS) (fun x => f x - c) p ≠ 0 := by
  have hnonneg_shift :
      (0 : WithTop ℤ) ≤ chartOrderAt (RS := RS) (fun x => f x - c) p :=
    (chartOrderAt_sub_const_nonneg_iff (RS := RS) (f := f) (p := p) c).2 hnonneg_f
  have hcv_f_eq_c : correctedValue (hf p) hnonneg_f = c := by
    calc
      correctedValue (hf p) hnonneg_f = f p := (hcompat p hnonneg_f).symm
      _ = c := hEq
  have hnonneg_mord_sub :
      (0 : WithTop ℤ) ≤ meromorphicOrderAt
        (fun z => chartRep (RS := RS) f p z - c) (chartPt (RS := RS) p) := by
    simpa [chartOrderAt, chartRep_sub_const] using hnonneg_shift
  have hcv_sub_eq :
      correctedValue ((hf p).sub (MeromorphicAt.const c _)) hnonneg_mord_sub =
        correctedValue (hf p) hnonneg_f - c :=
    correctedValue_sub_const_eq (g := chartRep (RS := RS) f p) (x := chartPt (RS := RS) p)
      (c := c) (hg := hf p) (hord_g := hnonneg_f) (hord_sub := hnonneg_mord_sub)
  have hcv_sub_zero :
      correctedValue ((hf p).sub (MeromorphicAt.const c _)) hnonneg_mord_sub = 0 := by
    rw [hcv_sub_eq, hcv_f_eq_c, sub_self]
  intro hzero_shift
  have hzero_mord :
      meromorphicOrderAt
        (chartRep (RS := RS) f p - fun _ => c) (chartPt (RS := RS) p) = 0 := by
    simpa [chartOrderAt] using hzero_shift
  have hcv_sub_ne_zero :
      correctedValue ((hf p).sub (MeromorphicAt.const c _))
        (by rw [hzero_mord]) ≠ 0 :=
    correctedValue_ne_zero_of_eq_zero ((hf p).sub (MeromorphicAt.const c _)) hzero_mord
  exact hcv_sub_ne_zero (by simpa [hzero_mord] using hcv_sub_zero)

/-- Under regular-value compatibility, the point-value regular fiber set at `c`
    coincides with the zero set of `f - c`, provided the shift has no `⊤` orders. -/
theorem fiberSet_eq_zeroSet_sub_const_of_regular_value_compat
    (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hcompat : ∀ p (hp : (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p),
      f p = correctedValue (hf p) hp)
    (c : ℂ)
    (hne_top_shift : ∀ p,
      chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p ≠ ⊤) :
    {p : CRS.toRiemannSurface.carrier |
      f p = c ∧ (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p} =
      zeroSet (RS := CRS.toRiemannSurface) (fun x => f x - c) := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨hpEq, hnonneg_f⟩
    have hne_zero_shift :
        chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p ≠ 0 :=
      shift_ne_zero_of_eq_const_of_regular_value_compat (RS := CRS.toRiemannSurface)
        hf hcompat hnonneg_f hpEq
    have hnonneg_shift :
        (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p :=
      (chartOrderAt_sub_const_nonneg_iff (RS := CRS.toRiemannSurface) (f := f) (p := p) c).2 hnonneg_f
    have hpos_shift :
        (0 : WithTop ℤ) < chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p :=
      lt_of_le_of_ne hnonneg_shift (Ne.symm hne_zero_shift)
    exact ⟨hpos_shift, hne_top_shift p⟩
  · intro hp
    rcases hp with ⟨hpos_shift, _hne_top_shift_p⟩
    have hnonneg_shift :
        (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p :=
      le_of_lt hpos_shift
    have hnonneg_f :
        (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p :=
      (chartOrderAt_sub_const_nonneg_iff (RS := CRS.toRiemannSurface) (f := f) (p := p) c).1
        hnonneg_shift
    have hpEq : f p = c :=
      eq_const_of_shift_pos_of_regular_value_compat (RS := CRS.toRiemannSurface)
        hf hcompat hpos_shift
    exact ⟨hpEq, hnonneg_f⟩

/-- Under regular-value compatibility, fiber multiplicity equals the shifted zero-order sum,
    provided the shift has no `⊤` orders. -/
theorem fiberMultiplicity_eq_zeroSum_of_regular_value_compat
    (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hcompat : ∀ p (hp : (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p),
      f p = correctedValue (hf p) hp)
    (c : ℂ)
    (hne_top_shift : ∀ p,
      chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p ≠ ⊤)
    (hfib : {p : CRS.toRiemannSurface.carrier |
      f p = c ∧ (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p}.Finite) :
    fiberMultiplicity CRS f c hfib =
      (zeroSet_finite CRS (fun x => f x - c)
        (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c hf)
        (chartOrderSupport_sub_const_finite CRS f c hf)).toFinset.sum
          (fun p => (chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p).getD 0) := by
  unfold fiberMultiplicity
  have hset :
      {p : CRS.toRiemannSurface.carrier |
        f p = c ∧ (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p} =
      zeroSet (RS := CRS.toRiemannSurface) (fun x => f x - c) :=
    fiberSet_eq_zeroSet_sub_const_of_regular_value_compat CRS f hf hcompat c hne_top_shift
  have hfin_eq :
      hfib.toFinset =
        (zeroSet_finite CRS (fun x => f x - c)
          (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c hf)
          (chartOrderSupport_sub_const_finite CRS f c hf)).toFinset := by
    ext p
    simp [Set.Finite.mem_toFinset, hset]
  rw [hfin_eq]

/-- Under regular-value compatibility, fiber multiplicity equals total pole order of `f - c`. -/
theorem fiberMultiplicity_eq_totalPoleOrder_sub_const_of_regular_value_compat
    (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hcompat : ∀ p (hp : (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p),
      f p = correctedValue (hf p) hp)
    (hnc : ¬ ∀ p q, p ∈ regularLocus (RS := CRS.toRiemannSurface) f →
      q ∈ regularLocus (RS := CRS.toRiemannSurface) f → f p = f q)
    (c : ℂ)
    (hfib : {p : CRS.toRiemannSurface.carrier |
      f p = c ∧ (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p}.Finite) :
    fiberMultiplicity CRS f c hfib =
      totalPoleOrder CRS (fun x => f x - c)
        (poleSet_finite CRS (fun x => f x - c)
          (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c hf)
          (chartOrderSupport_sub_const_finite CRS f c hf)) := by
  set Zsum : ℤ :=
    (zeroSet_finite CRS (fun x => f x - c)
      (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c hf)
      (chartOrderSupport_sub_const_finite CRS f c hf)).toFinset.sum
        (fun p => (chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p).getD 0)
  set Psum : ℤ :=
    totalPoleOrder CRS (fun x => f x - c)
      (poleSet_finite CRS (fun x => f x - c)
        (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c hf)
        (chartOrderSupport_sub_const_finite CRS f c hf))
  have hfc : IsChartMeromorphic (RS := CRS.toRiemannSurface) (fun x => f x - c) :=
    chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c hf
  have hne_top_shift : ∀ p,
      chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p ≠ ⊤ := by
    obtain ⟨p₀, hp₀reg, hp₀ne⟩ := exists_regular_ne_value_of_nonconstant_regularLocus
      (RS := CRS.toRiemannSurface) f hnc c
    have hcv_f0 : correctedValue (hf p₀) hp₀reg = f p₀ := (hcompat p₀ hp₀reg).symm
    have hcv_f0_ne_c : correctedValue (hf p₀) hp₀reg ≠ c := by
      simpa [hcv_f0] using hp₀ne
    have hnonneg_shift₀ :
        (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p₀ :=
      (chartOrderAt_sub_const_nonneg_iff (RS := CRS.toRiemannSurface) (f := f) (p := p₀) c).2 hp₀reg
    have hnonneg_mord_shift₀ :
        (0 : WithTop ℤ) ≤ meromorphicOrderAt
          (fun z => chartRep (RS := CRS.toRiemannSurface) f p₀ z - c)
          (chartPt (RS := CRS.toRiemannSurface) p₀) := by
      simpa [chartOrderAt, chartRep_sub_const] using hnonneg_shift₀
    have hcv_shift_eq :
        correctedValue ((hf p₀).sub (MeromorphicAt.const c _)) hnonneg_mord_shift₀ =
          correctedValue (hf p₀) hp₀reg - c :=
      correctedValue_sub_const_eq (g := chartRep (RS := CRS.toRiemannSurface) f p₀)
        (x := chartPt (RS := CRS.toRiemannSurface) p₀) (c := c)
        (hg := hf p₀) (hord_g := hp₀reg) (hord_sub := hnonneg_mord_shift₀)
    have hcv_shift_ne_zero :
        correctedValue ((hf p₀).sub (MeromorphicAt.const c _)) hnonneg_mord_shift₀ ≠ 0 := by
      rw [hcv_shift_eq]
      exact sub_ne_zero.mpr hcv_f0_ne_c
    have hp₀_ne_top :
        chartOrderAt (RS := CRS.toRiemannSurface) (fun x => f x - c) p₀ ≠ ⊤ := by
      intro htop₀
      have htop_mord :
          meromorphicOrderAt
            (fun z => chartRep (RS := CRS.toRiemannSurface) f p₀ z - c)
            (chartPt (RS := CRS.toRiemannSurface) p₀) = ⊤ := by
        simpa [chartOrderAt, chartRep_sub_const] using htop₀
      have hcv_shift_zero :
          correctedValue ((hf p₀).sub (MeromorphicAt.const c _)) hnonneg_mord_shift₀ = 0 :=
        correctedValue_eq_zero_of_top ((hf p₀).sub (MeromorphicAt.const c _))
          hnonneg_mord_shift₀ htop_mord
      exact hcv_shift_ne_zero hcv_shift_zero
    intro p
    exact chartOrderAt_ne_top_of_ne_top_somewhere (RS := CRS.toRiemannSurface)
      (fun x => f x - c) hfc p₀ hp₀_ne_top p
  have hfib_eq_Zsum : fiberMultiplicity CRS f c hfib = Zsum := by
    simpa [Zsum] using
      fiberMultiplicity_eq_zeroSum_of_regular_value_compat CRS f hf hcompat c
        hne_top_shift hfib
  have hsplit :
      chartOrderSum CRS (fun x => f x - c)
        (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c hf)
        (chartOrderSupport_sub_const_finite CRS f c hf) = Zsum - Psum := by
    simp [Zsum, Psum, chartOrderSum_split]
  have hsum_zero :
      chartOrderSum CRS (fun x => f x - c)
        (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c hf)
        (chartOrderSupport_sub_const_finite CRS f c hf) = 0 :=
    chartOrderSum_sub_const_eq_zero_of_nonconstant_regularLocus CRS f hf hnc c
  have hZ_eq_P : Zsum = Psum := by
    linarith [hsplit, hsum_zero]
  calc
    fiberMultiplicity CRS f c hfib = Zsum := hfib_eq_Zsum
    _ = Psum := hZ_eq_P
    _ = totalPoleOrder CRS (fun x => f x - c)
          (poleSet_finite CRS (fun x => f x - c)
            (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c hf)
            (chartOrderSupport_sub_const_finite CRS f c hf)) := by
          rfl

/-- Fiber multiplicity constancy under regular-value compatibility. -/
theorem fiberMultiplicity_constant_of_regular_value_compat
    (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hcompat : ∀ p (hp : (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p),
      f p = correctedValue (hf p) hp)
    (hnc : ¬ ∀ p q, p ∈ regularLocus (RS := CRS.toRiemannSurface) f →
      q ∈ regularLocus (RS := CRS.toRiemannSurface) f → f p = f q) :
    ∀ (c₁ c₂ : ℂ)
      (hfib₁ : {p : CRS.toRiemannSurface.carrier |
        f p = c₁ ∧ (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p}.Finite)
      (hfib₂ : {p : CRS.toRiemannSurface.carrier |
        f p = c₂ ∧ (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p}.Finite),
      fiberMultiplicity CRS f c₁ hfib₁ = fiberMultiplicity CRS f c₂ hfib₂ := by
  intro c₁ c₂ hfib₁ hfib₂
  have hfib₁_eq :
      fiberMultiplicity CRS f c₁ hfib₁ =
        totalPoleOrder CRS (fun x => f x - c₁)
          (poleSet_finite CRS (fun x => f x - c₁)
            (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c₁ hf)
            (chartOrderSupport_sub_const_finite CRS f c₁ hf)) :=
    fiberMultiplicity_eq_totalPoleOrder_sub_const_of_regular_value_compat
      CRS f hf hcompat hnc c₁ hfib₁
  have hfib₂_eq :
      fiberMultiplicity CRS f c₂ hfib₂ =
        totalPoleOrder CRS (fun x => f x - c₂)
          (poleSet_finite CRS (fun x => f x - c₂)
            (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c₂ hf)
            (chartOrderSupport_sub_const_finite CRS f c₂ hf)) :=
    fiberMultiplicity_eq_totalPoleOrder_sub_const_of_regular_value_compat
      CRS f hf hcompat hnc c₂ hfib₂
  calc
    fiberMultiplicity CRS f c₁ hfib₁
        = totalPoleOrder CRS (fun x => f x - c₁)
            (poleSet_finite CRS (fun x => f x - c₁)
              (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c₁ hf)
              (chartOrderSupport_sub_const_finite CRS f c₁ hf)) := hfib₁_eq
    _ = totalPoleOrder CRS (fun x => f x - c₂)
          (poleSet_finite CRS (fun x => f x - c₂)
            (chartMeromorphic_sub_const (RS := CRS.toRiemannSurface) c₂ hf)
            (chartOrderSupport_sub_const_finite CRS f c₂ hf)) :=
      totalPoleOrder_sub_const_eq_of_chartMeromorphic CRS f hf c₁ c₂
    _ = fiberMultiplicity CRS f c₂ hfib₂ := hfib₂_eq.symm

/-- Continuity-based constancy via the corrected-value compatibility bridge. -/
theorem fiberMultiplicity_constant_of_continuous_regular_via_compat
    (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hcont_reg : ∀ p, (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p →
      ContinuousAt (chartRep (RS := CRS.toRiemannSurface) f p)
        (chartPt (RS := CRS.toRiemannSurface) p))
    (hnc : ¬ ∀ p q, p ∈ regularLocus (RS := CRS.toRiemannSurface) f →
      q ∈ regularLocus (RS := CRS.toRiemannSurface) f → f p = f q) :
    ∀ (c₁ c₂ : ℂ)
      (hfib₁ : {p : CRS.toRiemannSurface.carrier |
        f p = c₁ ∧ (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p}.Finite)
      (hfib₂ : {p : CRS.toRiemannSurface.carrier |
        f p = c₂ ∧ (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p}.Finite),
      fiberMultiplicity CRS f c₁ hfib₁ = fiberMultiplicity CRS f c₂ hfib₂ := by
  have hcompat :
      ∀ p (hp : (0 : WithTop ℤ) ≤ chartOrderAt (RS := CRS.toRiemannSurface) f p),
        f p = correctedValue (hf p) hp :=
    regularValue_compat_of_continuous_regular (RS := CRS.toRiemannSurface) hf hcont_reg
  intro c₁ c₂ hfib₁ hfib₂
  exact fiberMultiplicity_constant_of_regular_value_compat CRS f hf hcompat hnc
    c₁ c₂ hfib₁ hfib₂


end RiemannSurfaces.Analytic
