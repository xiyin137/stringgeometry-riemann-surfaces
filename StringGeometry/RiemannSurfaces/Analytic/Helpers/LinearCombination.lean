import StringGeometry.RiemannSurfaces.Analytic.LineBundles
import StringGeometry.RiemannSurfaces.Analytic.Helpers.AnalyticBridge
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.ClusterPt

/-!
# Linear Combinations of L(D) Elements

This file develops the theory of ℂ-linear combinations of elements of L(D).

The key issue: `AnalyticMeromorphicFunction` (AMF) does not support addition
(the zero function cannot be represented since `leadingCoefficient_ne_zero` is required).
Instead, we work with `regularValue` functions, which are standard `carrier → ℂ` functions
that CAN be added.

## Main Definitions

* `lcRegularValue` — The linear combination function p ↦ Σ cᵢ · (basis i).fn.regularValue p

## Main Results

* `lcRegularValue_mdifferentiableAt` — The linear combination is MDifferentiableAt
  at jointly-regular points
* `lcRegularValue_zero_at_pole` — At a pole of some basis element, regularValue = 0
  contributes 0 to the sum (but other terms might still have poles)
* `lcRegularValue_vanishes_at_pts` — Vanishing at the test points (from hypotheses)

## References

* RiemannRoch.lean — The `zero_counting_linear_combination` theorem uses this infrastructure
-/

namespace RiemannSurfaces.Analytic

open Complex Topology
open scoped Manifold

/-!
## Linear Combination Definition
-/

section Definition

variable {RS : RiemannSurface} {D : Divisor RS}

/-- The ℂ-linear combination of regularValues of elements of L(D).

    Given basis elements f₁,...,fₙ in L(D) and coefficients c₁,...,cₙ ∈ ℂ,
    this is the function p ↦ Σ cᵢ · fᵢ(p).regularValue.

    At non-pole points (where all fᵢ have order ≥ 0), this gives the actual
    ℂ-valued linear combination of the function values.
    At pole points, regularValue returns 0 by convention, so this function
    might not capture the full meromorphic behavior at poles. -/
noncomputable def lcRegularValue
    {n : ℕ} (basis : Fin n → LinearSystem RS D) (c : Fin n → ℂ)
    (p : RS.carrier) : ℂ :=
  Finset.univ.sum (fun i => c i * (basis i).fn.regularValue p)

/-- The linear combination is a standard function RS.carrier → ℂ. -/
theorem lcRegularValue_eq
    {n : ℕ} (basis : Fin n → LinearSystem RS D) (c : Fin n → ℂ) :
    lcRegularValue basis c = fun p =>
      Finset.univ.sum (fun i => c i * (basis i).fn.regularValue p) := rfl

end Definition

/-!
## Linear Combination is MDifferentiableAt at Regular Points
-/

section Holomorphicity

variable {RS : RiemannSurface} {D : Divisor RS}

/-- At a jointly-regular point (where all basis elements have non-negative order),
    the linear combination is MDifferentiableAt.

    This follows from:
    1. Each `(basis i).fn.regularValue` is MDifferentiableAt (from `holomorphicAway`)
    2. Scalar multiples of MDifferentiableAt functions are MDifferentiableAt
    3. Finite sums of MDifferentiableAt functions are MDifferentiableAt -/
theorem lcRegularValue_mdifferentiableAt
    {n : ℕ} (basis : Fin n → LinearSystem RS D) (c : Fin n → ℂ)
    (p : RS.carrier) (hreg : ∀ i, 0 ≤ (basis i).fn.order p) :
    @MDifferentiableAt ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ)
      RS.carrier RS.topology RS.chartedSpace ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ℂ _ _
      (lcRegularValue basis c) p := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  unfold lcRegularValue
  apply mdifferentiableAt_finset_sum
  intro i _
  exact mdifferentiableAt_const_mul (c i) _ p ((basis i).holomorphicAway p (hreg i))

/-- If the linear combination is MDifferentiableAt at all points where all basis
    elements are regular, then it is holomorphic on the complement of the pole locus. -/
theorem lcRegularValue_holomorphicOnComplement
    {n : ℕ} (basis : Fin n → LinearSystem RS D) (c : Fin n → ℂ) :
    ∀ p : RS.carrier, (∀ i, 0 ≤ (basis i).fn.order p) →
    @MDifferentiableAt ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ)
      RS.carrier RS.topology RS.chartedSpace ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ℂ _ _
      (lcRegularValue basis c) p :=
  fun p hreg => lcRegularValue_mdifferentiableAt basis c p hreg

end Holomorphicity

/-!
## The Pole Locus

The set of points where some basis element has a pole is finite.
-/

section PoleLocus

variable {RS : RiemannSurface} {D : Divisor RS}

/-- The joint pole locus: points where at least one basis element has a pole. -/
def jointPoleLocus {n : ℕ} (basis : Fin n → LinearSystem RS D) : Set RS.carrier :=
  ⋃ i : Fin n, { p | (basis i).fn.order p < 0 }

/-- The joint pole locus is finite (each AMF has finitely many poles). -/
theorem jointPoleLocus_finite {n : ℕ} (basis : Fin n → LinearSystem RS D) :
    (jointPoleLocus basis).Finite := by
  apply Set.Finite.subset (Set.finite_iUnion (fun i => (basis i).fn.order_finiteSupport))
  intro p hp
  simp only [jointPoleLocus, Set.mem_iUnion, Set.mem_setOf_eq] at hp
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  obtain ⟨i, hi⟩ := hp
  exact ⟨i, by omega⟩

/-- A point is jointly regular iff it's not in the joint pole locus. -/
theorem jointly_regular_iff_not_pole {n : ℕ} (basis : Fin n → LinearSystem RS D)
    (p : RS.carrier) :
    (∀ i, 0 ≤ (basis i).fn.order p) ↔ p ∉ jointPoleLocus basis := by
  simp only [jointPoleLocus, Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_lt]

/-- The jointly regular locus is the complement of a finite set. -/
theorem jointly_regular_locus_cofinite {n : ℕ} (basis : Fin n → LinearSystem RS D) :
    (jointPoleLocus basis)ᶜ = { p | ∀ i, 0 ≤ (basis i).fn.order p } := by
  ext p
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
  exact (jointly_regular_iff_not_pole basis p).symm

end PoleLocus

/-!
## Vanishing Properties
-/

section Vanishing

variable {RS : RiemannSurface} {D : Divisor RS}

/-- The linear combination at a point where a basis element has a zero (order > 0):
    the regularValue of that element is 0. -/
theorem regularValue_zero_at_positive_order {f : AnalyticMeromorphicFunction RS}
    {p : RS.carrier} (h : 0 < f.order p) :
    f.regularValue p = 0 :=
  AnalyticMeromorphicFunction.regularValue_at_zero h

/-- The linear combination at a point where a basis element has a pole (order < 0):
    the regularValue of that element is 0 by convention. -/
theorem regularValue_zero_at_negative_order {f : AnalyticMeromorphicFunction RS}
    {p : RS.carrier} (h : f.order p < 0) :
    f.regularValue p = 0 :=
  AnalyticMeromorphicFunction.regularValue_at_pole h

/-- If all coefficients are 0, the linear combination is identically 0. -/
theorem lcRegularValue_zero_of_coeffs_zero
    {n : ℕ} (basis : Fin n → LinearSystem RS D) (c : Fin n → ℂ)
    (hc : ∀ i, c i = 0) (p : RS.carrier) :
    lcRegularValue basis c p = 0 := by
  simp [lcRegularValue, hc]

/-- On a compact RS, if the linear combination is MDifferentiable everywhere
    (no poles) and has a zero at some point, then it's identically zero. -/
theorem lcRegularValue_constant_if_holomorphic
    (CRS : CompactRiemannSurface) {D' : Divisor CRS.toRiemannSurface}
    {n : ℕ} (basis : Fin n → LinearSystem CRS.toRiemannSurface D')
    (c : Fin n → ℂ)
    (hholAll : ∀ p, @MDifferentiableAt ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ)
      CRS.toRiemannSurface.carrier CRS.toRiemannSurface.topology
      CRS.toRiemannSurface.chartedSpace ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ℂ _ _
      (lcRegularValue basis c) p)
    (p : CRS.toRiemannSurface.carrier) (hp : lcRegularValue basis c p = 0) :
    ∀ q, lcRegularValue basis c q = 0 := by
  -- The linear combination is holomorphic on all of CRS
  -- By holomorphicIsConstant, it's constant
  -- Since it's 0 at p, it's 0 everywhere
  exact rs_identity_principle_compact CRS _ hholAll p hp

end Vanishing

/-!
## Order Bounds for Linear Combinations

When the linear combination is viewed as a meromorphic function, its poles
are bounded by the divisor D.
-/

section OrderBounds

variable {RS : RiemannSurface} {D : Divisor RS}

/-- For elements of L(D), the order at each point is at least -D.coeff p.
    This is the definition of being in L(D): div(f) + D ≥ 0. -/
theorem linearSystem_order_ge_neg_D (f : LinearSystem RS D) (p : RS.carrier) :
    -D.coeff p ≤ f.fn.order p := by
  have h := f.effective p
  -- h : 0 ≤ (divisorOf f.fn + D).coeff p
  -- Unfold: (divisorOf f.fn + D).coeff p = f.fn.order p + D.coeff p
  change 0 ≤ (Divisor.add (divisorOf f.fn) D).coeff p at h
  simp only [Divisor.add, divisorOf] at h
  omega

/-- The chart-local order of a basis element's regularValue matches its AMF order,
    and hence is at least -D(p). -/
theorem chartOrderAt_basis_ge_neg_D (f : LinearSystem RS D) (p : RS.carrier) :
    (-D.coeff p : WithTop ℤ) ≤ chartOrderAt (RS := RS) f.fn.regularValue p := by
  letI := RS.topology
  letI := RS.chartedSpace
  rw [f.chartOrderAt_eq]
  exact WithTop.coe_le_coe.2 (linearSystem_order_ge_neg_D f p)

/-- The chart-local order of the linear combination Σ cᵢ · fᵢ.regularValue
    is at least -D(q) at every point q.

    This follows from:
    1. Each basis element has chartOrderAt ≥ -D(q) (from chartOrderAt_eq + effective)
    2. Scalar multiples preserve or increase order
    3. The order of a sum is ≥ minimum of the individual orders -/
theorem chartOrderAt_lcRegularValue_ge_neg_D
    {n : ℕ} (basis : Fin n → LinearSystem RS D) (c : Fin n → ℂ) (q : RS.carrier) :
    (-D.coeff q : WithTop ℤ) ≤ chartOrderAt (RS := RS) (lcRegularValue basis c) q := by
  letI := RS.topology
  letI := RS.chartedSpace
  induction n with
  | zero =>
    -- Empty sum = constant 0, order = ⊤ ≥ anything
    have hzero : lcRegularValue basis c = fun _ => (0 : ℂ) := by
      ext p
      simp [lcRegularValue]
    rw [hzero, chartOrderAt]
    have htop : meromorphicOrderAt (chartRep (RS := RS) (fun _ => (0 : ℂ)) q)
        (chartPt (RS := RS) q) = ⊤ := by
      exact meromorphicOrderAt_eq_top_iff.mpr
        (Filter.Eventually.of_forall fun z => by simp [chartRep, Function.comp])
    rw [htop]
    exact le_of_lt (WithTop.coe_lt_top (-D.coeff q))
  | succ n ih =>
    -- Decompose Fin (n+1) sum = first n terms + last term
    have hsplit : lcRegularValue basis c = fun p =>
        lcRegularValue (fun i => basis (Fin.castSucc i)) (fun i => c (Fin.castSucc i)) p +
        c (Fin.last n) * (basis (Fin.last n)).fn.regularValue p := by
      ext p; simp [lcRegularValue, Fin.sum_univ_castSucc]
    rw [hsplit]
    -- Set up the two summands
    set f := lcRegularValue (fun i => basis (Fin.castSucc i)) (fun i => c (Fin.castSucc i))
    set g := fun p => c (Fin.last n) * (basis (Fin.last n)).fn.regularValue p
    -- Both summands are chart-meromorphic
    have hf_cm : IsChartMeromorphic (RS := RS) f := by
      apply chartMeromorphic_linear_combination
      intro i; exact (basis (Fin.castSucc i)).chartMeromorphic
    have hg_cm : IsChartMeromorphic (RS := RS) g := by
      apply chartMeromorphic_smul
      exact fun p => (basis (Fin.last n)).chartMeromorphic p
    -- Use chartOrderAt_add_ge: min(order f, order g) ≤ order(f+g)
    calc (-D.coeff q : WithTop ℤ)
        ≤ min (chartOrderAt f q) (chartOrderAt g q) := by
          refine le_min ?_ ?_
          · exact ih _ _
          · exact le_trans (chartOrderAt_basis_ge_neg_D (basis (Fin.last n)) q)
              (chartOrderAt_smul_ge (c (Fin.last n)) (fun p => (basis (Fin.last n)).chartMeromorphic p) q)
      _ ≤ chartOrderAt (fun x => f x + g x) q := chartOrderAt_add_ge hf_cm hg_cm q

/-- The chart order support of the linear combination is contained in
    supp(D) ∪ {zeros of g} and is finite on compact surfaces.

    For a nonzero chart-meromorphic function on a compact surface,
    zeros are isolated (hence finite), and poles are bounded by supp(D). -/
theorem lcRegularValue_chartOrderSupport_finite
    (CRS : CompactRiemannSurface)
    {D' : Divisor CRS.toRiemannSurface}
    {n : ℕ} (basis : Fin n → LinearSystem CRS.toRiemannSurface D') (c : Fin n → ℂ) :
    (chartOrderSupport (RS := CRS.toRiemannSurface) (lcRegularValue basis c)).Finite := by
  set RS := CRS.toRiemannSurface
  set g := lcRegularValue basis c
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  -- g is chart-meromorphic
  have hcm : IsChartMeromorphic (RS := RS) g := by
    apply chartMeromorphic_linear_combination
    intro i; exact (basis i).chartMeromorphic
  -- The joint pole locus is finite
  have hP_fin := jointPoleLocus_finite basis
  -- chartOrderSupport g ⊆ (jointPoleLocus ∩ support) ∪ (support \ jointPoleLocus)
  -- The first part is finite (subset of finite set). Suffices to show second part is finite.
  have hinter_fin : (chartOrderSupport (RS := RS) g ∩ jointPoleLocus basis).Finite :=
    hP_fin.subset Set.inter_subset_right
  suffices hdiff_fin : (chartOrderSupport (RS := RS) g \ jointPoleLocus basis).Finite by
    exact (hdiff_fin.union hinter_fin).subset (fun p hp => by
      by_cases h : p ∈ jointPoleLocus basis
      · exact Or.inr ⟨hp, h⟩
      · exact Or.inl ⟨hp, h⟩)
  -- Show the support minus poles is finite by contradiction
  by_contra h_inf
  rw [Set.not_finite] at h_inf
  haveI : CompactSpace RS.carrier := CRS.compact
  -- Infinite set in compact space has accumulation point
  obtain ⟨x, hx_acc⟩ := h_inf.exists_accPt_principal
  have hmer := hcm x
  -- Dichotomy: either chartRep g x is eventually zero or eventually nonzero
  rw [accPt_iff_frequently_nhdsNE] at hx_acc
  by_cases h_top : meromorphicOrderAt (chartRep g x) (chartPt (RS := RS) x) = ⊤
  · -- Case 1: order = ⊤ → g is eventually zero near x in charts
    -- Pull back to manifold: g = 0 in punctured nhd of x
    have h_ev_zero := meromorphicOrderAt_eq_top_iff.mp h_top
    have h_mfld_zero := eventually_eq_zero_of_chartRep g x h_ev_zero
    -- Convert to nhds form and extract open neighborhood
    rw [eventually_nhdsWithin_iff] at h_mfld_zero
    -- h_mfld_zero : ∀ᶠ q in 𝓝 x, q ≠ x → g q = 0
    -- i.e., ∃ open V ∋ x, ∀ q ∈ V, q ≠ x → g q = 0
    -- For q ∈ V \ {x}: V \ {x} is open (T1), q ∈ it, g = 0 on it
    -- → chartOrderAt g q = ⊤ → q ∉ support
    -- Derive contradiction: show ∀ᶠ q in 𝓝[≠] x, q ∉ S
    -- Key: use eventually_eventually_nhds to propagate "g = 0 near x"
    -- to "g = 0 near q" for q near x
    have h_prop := h_mfld_zero.eventually_nhds
    -- h_prop : ∀ᶠ q in 𝓝 x, ∀ᶠ z in 𝓝 q, z ≠ x → g z = 0
    exact hx_acc <| by
      rw [eventually_nhdsWithin_iff]
      apply h_prop.mono
      intro q hq_nhds hq_ne hq_mem
      obtain ⟨⟨_, hord_ne_top⟩, _⟩ := hq_mem
      exact hord_ne_top <| chartOrderAt_eq_top_of_zero_on_nhd <| by
        -- hq_nhds : ∀ᶠ z in 𝓝 q, z ≠ x → g z = 0
        -- Since q ≠ x and {x} is closed (T2 → T1), z ≠ x near q
        haveI : T2Space RS.carrier := RS.t2
        have hne_x : ∀ᶠ z in @nhds RS.carrier RS.topology q, z ≠ x :=
          isOpen_ne.mem_nhds hq_ne
        exact hne_x.mp hq_nhds
  · -- Case 2: order ≠ ⊤ → g is eventually nonzero near x in charts
    have h_ev_ne := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hmer).mp h_top
    have h_mfld_ne := eventually_ne_zero_of_chartRep g x h_ev_ne
    -- Show ∀ᶠ q in 𝓝[≠] x, q ∉ S (contradicts hx_acc)
    exact hx_acc <| h_mfld_ne.mono fun q hq hq_mem => by
      obtain ⟨⟨hord_ne, _⟩, hq_reg⟩ := hq_mem
      exact hord_ne (chartOrderAt_eq_zero_of_continuousAt_ne_zero hcm q
        (continuousAt_chartRep_of_mdifferentiableAt g q
          (lcRegularValue_mdifferentiableAt basis c q
            ((jointly_regular_iff_not_pole basis q).mpr hq_reg)))
        hq)

end OrderBounds

end RiemannSurfaces.Analytic
