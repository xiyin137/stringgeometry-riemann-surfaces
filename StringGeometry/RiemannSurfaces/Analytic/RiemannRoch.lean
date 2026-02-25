import StringGeometry.RiemannSurfaces.Analytic.LineBundles
import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.SerreDuality
import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.DolbeaultCohomology
import StringGeometry.RiemannSurfaces.Analytic.Helpers.ArgumentPrinciple
import StringGeometry.RiemannSurfaces.Analytic.Helpers.LinearCombination

/-!
# Riemann-Roch Theorem (Analytic Approach)

This file develops the Riemann-Roch theorem for compact Riemann surfaces
using the analytic approach via correction term invariance.

## The Riemann-Roch Theorem

For a compact Riemann surface X of genus g (topological genus) and a divisor D:

  **h⁰(D) - h⁰(K - D) = deg(D) + 1 - g**  (h⁰ duality form)

where K is the canonical divisor (divisor of any meromorphic 1-form)
with h⁰(K) = g (Hodge theorem).

By Serre duality h¹(D) = h⁰(K - D), this gives the classical form:

  **h⁰(D) - h¹(D) = deg(D) + 1 - g**

where h¹ is properly defined via Dolbeault cohomology (see DolbeaultCohomology.lean).

## Proof Strategy

### Level 1: h⁰ duality (this file, fully proven modulo eval_residue_complementarity)
The correction term f(D) = (h⁰(D) - h⁰(K-D)) - deg(D) is constant:
- eval_residue_complementarity: h⁰(D+[p]) - h⁰(D) + h⁰(K-D) - h⁰(K-D-[p]) = 1
- This gives χ(D + [p]) = χ(D) + 1, so f(D + [p]) = f(D)
- By induction on total variation: f(D) = f(0) = 1 - g
- The base case uses h⁰(0) = 1 (proven) and h⁰(K) = g (hypothesis from Hodge theory)

### Level 2: Classical form (requires Serre duality as separate theorem)
- h¹(D) = dim(Ω^{0,1}(D) / im ∂̄_D) (Dolbeault cohomology — see DolbeaultCohomology.lean)
- Serre duality: h¹(D) = h⁰(K - D) (theorem, not definition)
- Combined with Level 1: h⁰(D) - h¹(D) = deg(D) + 1 - g

### Level 3: h⁰(K) = g (Hodge theorem — connects analytic to topological)
- dim H^{1,0}(X) = g (topological genus): dim_harmonic_10_eq_genus
- H⁰(K) ≅ H^{1,0}(X) (holomorphic 1-forms): harmonic_10_are_canonical_sections

## Main Results

* `riemann_roch_h0_duality` — h⁰(D) - h⁰(K-D) = deg(D) + 1 - g (core)
* `riemann_roch_classical` — h⁰(D) - h¹(D) = deg(D) + 1 - g (via Serre duality)
* `h0_canonical_eq_genus` — h⁰(K) = g (Hodge theorem)

## References

* Griffiths, Harris "Principles of Algebraic Geometry" Ch 2.3
* Forster "Lectures on Riemann Surfaces" §17
-/

namespace RiemannSurfaces.Analytic

open Complex Topology Classical
open scoped Manifold

/-!
## Linear Independence in L(D)

To define h⁰(D) correctly as the dimension of L(D), we use ℂ-linear independence
of meromorphic functions. This avoids the need to construct a full ℂ-module structure
on L(D), while correctly measuring the vector space dimension.

**Key idea:** Functions f₁,...,fₙ in L(D) are ℂ-linearly independent if the only
ℂ-linear combination that vanishes at all non-pole points is the trivial one.
Since poles form a finite set, the non-pole locus is dense, and the identity principle
for meromorphic functions ensures this correctly captures linear independence.
-/

/-- The type H⁰(X, O(D)) of global sections (non-zero meromorphic functions in L(D)).

    For a divisor D, elements are meromorphic functions f with div(f) + D ≥ 0.
    The zero function is NOT included in this type (it is handled separately
    by the IsLinIndepLS definition). -/
noncomputable def H0VectorSpace (CRS : CompactRiemannSurface)
    (D : Divisor CRS.toRiemannSurface) : Type :=
  LinearSystem CRS.toRiemannSurface D

/-- ℂ-linear independence of elements in the linear system L(D).

    Functions f₁,...,fₙ in L(D) are ℂ-linearly independent if:
    for any coefficients c₁,...,cₙ ∈ ℂ, if the ℂ-linear combination
    Σ cᵢ fᵢ vanishes at every point where ALL fᵢ are regular (non-pole),
    then all cᵢ = 0.

    Since each fᵢ has only finitely many poles (by `order_finiteSupport`),
    the set of points where all fᵢ are regular is cofinite, hence dense
    on any connected Riemann surface. By the identity principle for
    meromorphic functions, vanishing on a dense set implies vanishing
    identically. Therefore this correctly captures ℂ-linear independence.

    **Comparison with standard linear algebra:**
    - In a ℂ-vector space V, {v₁,...,vₙ} are independent iff Σ cᵢ vᵢ = 0 ⟹ all cᵢ = 0
    - Here, "Σ cᵢ fᵢ = 0" is expressed pointwise at non-pole points
    - The `regularValue` function gives the ℂ-value at non-poles, and 0 at poles -/
def IsLinIndepLS (CRS : CompactRiemannSurface)
    (D : Divisor CRS.toRiemannSurface) {n : ℕ}
    (basis : Fin n → LinearSystem CRS.toRiemannSurface D) : Prop :=
  ∀ c : Fin n → ℂ,
    (∀ p : CRS.toRiemannSurface.carrier,
      (∀ i, (basis i).fn.order p ≥ 0) →
      Finset.univ.sum (fun i => c i * (basis i).fn.regularValue p) = 0) →
    ∀ i, c i = 0

/-- The empty family is vacuously linearly independent -/
theorem isLinIndepLS_empty (CRS : CompactRiemannSurface)
    (D : Divisor CRS.toRiemannSurface)
    (basis : Fin 0 → LinearSystem CRS.toRiemannSurface D) :
    IsLinIndepLS CRS D basis := by
  intro c _ i; exact Fin.elim0 i

/-- Zero-counting principle for linear combinations in L(D).

    A ℂ-linear combination of elements of L(D) that vanishes at
    deg(D)+1 distinct regular points outside supp(D)
    must vanish at all regular points.

    **Proof idea:**
    The linear combination g(p) = Σ cᵢ · fᵢ(p) is a meromorphic function:
    1. g is holomorphic wherever all fᵢ are regular (from holomorphicAway)
    2. The poles of g are bounded by D: at any point q, if all fᵢ have
       order ≥ -D(q), then g has order ≥ -D(q)
    3. If g vanishes at deg(D)+1 points outside supp(D), counting:
       - Zeros contribute ≥ deg(D)+1 to the degree of div(g)
       - Poles contribute ≥ -deg(D) to the degree of div(g)
       - So deg(div(g)) ≥ 1 > 0
    4. But by the argument principle, deg(div(g)) = 0 for any nonzero
       meromorphic function on a compact surface
    5. Therefore g ≡ 0 on the regular locus -/
theorem zero_counting_linear_combination (CRS : CompactRiemannSurface)
    (D : Divisor CRS.toRiemannSurface) (hdeg : 0 ≤ D.degree)
    {n : ℕ} (basis : Fin n → LinearSystem CRS.toRiemannSurface D)
    (c : Fin n → ℂ)
    (pts : Fin (D.degree.toNat + 1) → CRS.toRiemannSurface.carrier)
    (hpts_inj : Function.Injective pts)
    (hpts_reg : ∀ j i, 0 ≤ (basis i).fn.order (pts j))
    (hpts_out : ∀ j, D.coeff (pts j) = 0)
    (heval : ∀ j, Finset.univ.sum (fun i => c i * (basis i).fn.regularValue (pts j)) = 0) :
    ∀ p, (∀ i, 0 ≤ (basis i).fn.order p) →
      Finset.univ.sum (fun i => c i * (basis i).fn.regularValue p) = 0 := by
  -- Define the linear combination function
  let g : CRS.toRiemannSurface.carrier → ℂ :=
    lcRegularValue basis c
  -- g is holomorphic at all jointly regular points (from LinearCombination infrastructure)
  have g_hol : ∀ p, (∀ i, 0 ≤ (basis i).fn.order p) →
      @MDifferentiableAt ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ)
        CRS.toRiemannSurface.carrier CRS.toRiemannSurface.topology
        CRS.toRiemannSurface.chartedSpace ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ℂ _ _
        g p := fun p hreg => lcRegularValue_mdifferentiableAt basis c p hreg
  -- g is chart-meromorphic: each regularValue is MeromorphicAt in charts (from chartMeromorphic field)
  have g_cm : IsChartMeromorphic (RS := CRS.toRiemannSurface) g := by
    apply chartMeromorphic_linear_combination
    intro i p
    exact (basis i).chartMeromorphic p
  -- g vanishes at the test points
  have g_vanish : ∀ j, g (pts j) = 0 := heval
  -- By contradiction: assume ∃ regular p₀ with g(p₀) ≠ 0
  by_contra h_not
  push_neg at h_not
  obtain ⟨p₀, hreg₀, hne₀⟩ := h_not
  -- Convert hne₀ to use g
  have hne₀' : g p₀ ≠ 0 := hne₀
  -- Set up topology and manifold instances
  letI := CRS.toRiemannSurface.topology
  letI := CRS.toRiemannSurface.chartedSpace
  haveI := CRS.toRiemannSurface.isManifold
  haveI := CRS.toRiemannSurface.t2
  -- Step 1: chartOrderAt g p₀ = 0 (nonzero continuous function)
  have hcont₀ := continuousAt_chartRep_of_mdifferentiableAt g p₀ (g_hol p₀ hreg₀)
  have hord₀ := chartOrderAt_eq_zero_of_continuousAt_ne_zero g_cm p₀ hcont₀ hne₀'
  -- Step 2: Identity principle — chartOrderAt g q ≠ ⊤ for ALL q
  have hne_top : ∀ q, chartOrderAt (RS := CRS.toRiemannSurface) g q ≠ ⊤ :=
    fun q => chartOrderAt_ne_top_of_ne_top_somewhere g g_cm p₀
      (hord₀ ▸ WithTop.coe_ne_top) q
  -- Step 3: chartOrderSupport is finite
  have hsupp := lcRegularValue_chartOrderSupport_finite CRS basis c
  -- Step 4: Argument principle — chartOrderSum = 0
  have harg : chartOrderSum CRS g g_cm hsupp = 0 :=
    chartMeromorphic_argument_principle CRS g g_cm hsupp ⟨p₀, hne₀'⟩
  -- Step 5: Lower bound — chartOrderSum ≥ 1
  -- Key ingredients:
  --   (a) At test points: g(pts j) = 0, g is ContinuousAt, chartOrderAt g ≠ ⊤
  --       → chartOrderAt g (pts j) > 0 → (chartOrderAt g (pts j)).getD 0 ≥ 1
  --   (b) Test points are in chartOrderSupport (order > 0 and ≠ ⊤)
  --   (c) Test points are distinct (hpts_inj), so they contribute ≥ deg(D)+1
  --   (d) At all points: chartOrderAt g q ≥ -D.coeff q (from chartOrderAt_lcRegularValue_ge_neg_D)
  --       Combined with chartOrderAt g q ≠ ⊤: (chartOrderAt g q).getD 0 ≥ -D.coeff q
  --   (e) Non-test support points contribute ≥ -Σ D.coeff ≥ -deg(D)
  --   (f) Total: chartOrderSum ≥ (deg(D)+1) + (-deg(D)) = 1
  have hlower : 0 < chartOrderSum CRS g g_cm hsupp := by
    -- Test points have positive order (zeros of a non-locally-zero function)
    have hord_pos : ∀ j, 0 < chartOrderAt (RS := CRS.toRiemannSurface) g (pts j) := fun j =>
      chartOrderAt_pos_of_zero g_cm (pts j) (g_vanish j)
        (continuousAt_chartRep_of_mdifferentiableAt g (pts j)
          (g_hol (pts j) (fun i => hpts_reg j i)))
    -- Test points are in the support
    have hpts_supp : ∀ j, pts j ∈ hsupp.toFinset := fun j => by
      rw [Set.Finite.mem_toFinset]
      exact ⟨ne_of_gt (hord_pos j), hne_top (pts j)⟩
    -- getD(ord) ≥ 1 at test points (positive integer order)
    have hgetD_pos : ∀ j,
        1 ≤ (chartOrderAt (RS := CRS.toRiemannSurface) g (pts j)).getD 0 := by
      intro j
      have h_ne := hne_top (pts j)
      have h_pos := hord_pos j
      -- chartOrderAt g (pts j) ≠ ⊤, so it's ↑m; and 0 < ↑m gives m ≥ 1
      cases h : chartOrderAt (RS := CRS.toRiemannSurface) g (pts j) with
      | top => exact absurd h h_ne
      | coe m =>
        show 1 ≤ m
        rw [h] at h_pos
        have : (0 : ℤ) < m := by exact_mod_cast h_pos
        omega
    -- getD(ord) + D.coeff ≥ 0 at all points (from L(D) condition)
    have hadj_nonneg : ∀ p,
        0 ≤ (chartOrderAt (RS := CRS.toRiemannSurface) g p).getD 0 + D.coeff p := by
      intro p
      have h_ge := chartOrderAt_lcRegularValue_ge_neg_D basis c p
      cases h : chartOrderAt (RS := CRS.toRiemannSurface) g p with
      | top => exact absurd h (hne_top p)
      | coe m =>
        show 0 ≤ m + D.coeff p
        rw [h] at h_ge
        have : -D.coeff p ≤ m := by exact_mod_cast h_ge
        linarith
    -- Injective image of test points in support
    have himg_sub : Finset.univ.image pts ⊆ hsupp.toFinset :=
      Finset.image_subset_iff.mpr fun j _ => hpts_supp j
    have himg_card : (Finset.univ.image pts).card = D.degree.toNat + 1 :=
      (Finset.card_image_of_injective _ hpts_inj).trans (Finset.card_fin _)
    -- Adjusted sum (getD + D.coeff) over test points ≥ deg(D)+1
    have hsum_test_adj : (D.degree.toNat + 1 : ℤ) ≤
        (Finset.univ.image pts).sum (fun p =>
          (chartOrderAt (RS := CRS.toRiemannSurface) g p).getD 0 + D.coeff p) := by
      calc (D.degree.toNat + 1 : ℤ)
          = (Finset.univ.image pts).sum (fun _ => (1 : ℤ)) := by
              simp [himg_card]
        _ ≤ _ := Finset.sum_le_sum fun p hp => by
              obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
              rw [hpts_out j, add_zero]; exact hgetD_pos j
    -- Adjusted sum over all of S ≥ adjusted sum over test points
    have hsum_S_adj : (Finset.univ.image pts).sum (fun p =>
          (chartOrderAt (RS := CRS.toRiemannSurface) g p).getD 0 + D.coeff p) ≤
        hsupp.toFinset.sum (fun p =>
          (chartOrderAt (RS := CRS.toRiemannSurface) g p).getD 0 + D.coeff p) :=
      Finset.sum_le_sum_of_subset_of_nonneg himg_sub fun x _ _ => hadj_nonneg x
    -- Sum of D.coeff over S ≤ deg(D)
    -- Argument: for p ∈ supp(D) \ S, D.coeff p > 0 (because ord p = 0 ≥ -D.coeff p
    -- and D.coeff p ≠ 0), so Σ_{supp(D)\S} D.coeff ≥ 0, hence Σ_S D.coeff ≤ deg(D)
    have hDcoeff_le : hsupp.toFinset.sum D.coeff ≤ D.degree := by
      unfold Divisor.degree
      -- Step 1: D.degree = Σ_{S ∪ D.supp} D.coeff (terms in S \ D.supp have D.coeff = 0)
      have h_eq : D.finiteSupport.toFinset.sum D.coeff =
          (hsupp.toFinset ∪ D.finiteSupport.toFinset).sum D.coeff := by
        apply Finset.sum_subset Finset.subset_union_right
        intro p _ hp_not
        simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq, not_not] at hp_not
        exact hp_not
      rw [h_eq]
      -- Step 2: Σ_S D.coeff ≤ Σ_{S ∪ D.supp} D.coeff (terms in D.supp \ S have D.coeff ≥ 0)
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      intro p _ hp_not
      -- p ∉ S means chartOrderAt g p = 0 (since ⊤ excluded)
      have h_not_S : p ∉ chartOrderSupport (RS := CRS.toRiemannSurface) g := by
        rwa [Set.Finite.mem_toFinset] at hp_not
      simp only [chartOrderSupport, Set.mem_setOf_eq, not_and_or, not_not] at h_not_S
      have h_ord_zero : chartOrderAt (RS := CRS.toRiemannSurface) g p = 0 := by
        cases h_not_S with
        | inl h => exact h
        | inr h => exact absurd h (hne_top p)
      -- From chartOrderAt g p ≥ -D.coeff p and chartOrderAt g p = 0: D.coeff p ≥ 0
      have h_ge := chartOrderAt_lcRegularValue_ge_neg_D basis c p
      rw [h_ord_zero] at h_ge
      have : -D.coeff p ≤ 0 := by exact_mod_cast h_ge
      linarith
    -- Combine: chartOrderSum = Σ_S (getD + D.coeff) - Σ_S D.coeff
    simp only [chartOrderSum]
    have hrewrite : hsupp.toFinset.sum (fun p =>
          (chartOrderAt (RS := CRS.toRiemannSurface) g p).getD 0) =
        hsupp.toFinset.sum (fun p =>
          (chartOrderAt (RS := CRS.toRiemannSurface) g p).getD 0 + D.coeff p) -
        hsupp.toFinset.sum D.coeff := by
      rw [← Finset.sum_sub_distrib]; congr 1; ext p; ring
    rw [hrewrite]
    have h_deg_nat : (D.degree.toNat : ℤ) = D.degree := Int.toNat_of_nonneg hdeg
    linarith
  -- Step 6: Contradiction
  linarith

/-- L(D) is finite-dimensional on compact Riemann surfaces:
    there exists N such that no family of N+1 elements in L(D) is ℂ-linearly independent.

    **Proof (Riemann inequality):**
    Any deg(D)+2 elements of L(D) must be linearly dependent. Choose deg(D)+1
    distinct points outside supp(D) and evaluate. The evaluation vectors live in
    ℂ^{deg(D)+1}, so deg(D)+2 of them are linearly dependent. By the zero-counting
    principle, the nontrivial relation extends to all regular points, contradicting
    linear independence. -/
theorem h0_bounded (CRS : CompactRiemannSurface)
    (D : Divisor CRS.toRiemannSurface) :
    ∃ N : ℕ, ∀ m, m > N →
      ¬ ∃ (basis : Fin m → LinearSystem CRS.toRiemannSurface D),
        IsLinIndepLS CRS D basis := by
  -- Case 1: deg(D) < 0 → L(D) is empty
  by_cases hdeg : D.degree < 0
  · exact ⟨0, fun m hm ⟨basis, _⟩ =>
      (linearSystem_empty_negative_degree CRS D hdeg).false (basis ⟨0, by omega⟩)⟩
  -- Case 2: deg(D) ≥ 0
  push_neg at hdeg
  -- Bound: N = deg(D) + 1 (the Riemann inequality bound)
  refine ⟨D.degree.toNat + 1, fun m hm ⟨basis, hli⟩ => ?_⟩
  -- Define S = supp(D) ∪ ⋃ᵢ supp(basis(i).fn)
  let S : Set CRS.toRiemannSurface.carrier :=
    { p | D.coeff p ≠ 0 } ∪ (⋃ i : Fin m, { p | (basis i).fn.order p ≠ 0 })
  have hS_finite : S.Finite := by
    apply Set.Finite.union D.finiteSupport
    exact Set.finite_iUnion (fun i => (basis i).fn.order_finiteSupport)
  -- Sᶜ is infinite (carrier is infinite, S is finite)
  haveI : Infinite CRS.toRiemannSurface.carrier :=
    RiemannSurface.carrier_infinite CRS.toRiemannSurface
  have hSc_inf : Sᶜ.Infinite := Set.Finite.infinite_compl hS_finite
  -- Choose deg(D)+1 distinct points in Sᶜ using the natural embedding
  let k := D.degree.toNat + 1
  let emb := hSc_inf.natEmbedding
  let pts : Fin k → CRS.toRiemannSurface.carrier := fun j => (emb j.val).val
  have hpts_inj : Function.Injective pts := by
    intro a b hab
    exact Fin.val_injective (emb.injective (Subtype.val_injective hab))
  -- The chosen points are outside S
  have hpts_out : ∀ j : Fin k, pts j ∉ S := fun j => (emb j.val).property
  -- Therefore: regular for all basis elements
  have hpts_reg : ∀ (j : Fin k) (i : Fin m), 0 ≤ (basis i).fn.order (pts j) := by
    intro j i
    have h := hpts_out j
    simp only [S, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_exists] at h
    have := h.2 i
    push_neg at this
    omega
  -- And outside supp(D)
  have hpts_D : ∀ j : Fin k, D.coeff (pts j) = 0 := by
    intro j
    have h := hpts_out j
    simp only [S, Set.mem_union, Set.mem_setOf_eq, not_or, Set.mem_iUnion, not_exists] at h
    push_neg at h
    exact h.1
  -- Define evaluation vectors: v(i)(j) = basis(i).fn.regularValue(pts(j))
  let v : Fin m → (Fin k → ℂ) := fun i j => (basis i).fn.regularValue (pts j)
  -- v cannot be linearly independent (m > k = dim of codomain)
  have hnotli : ¬LinearIndependent ℂ v := by
    intro hli_v
    have hcard := hli_v.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hcard
    have hfr : Module.finrank ℂ (Fin k → ℂ) = k := by
      rw [Module.finrank_pi, Fintype.card_fin]
    rw [hfr] at hcard
    omega
  -- Extract nontrivial linear relation
  rw [Fintype.linearIndependent_iff] at hnotli
  push_neg at hnotli
  obtain ⟨c, hsum, i₀, hi₀⟩ := hnotli
  -- hsum : ∑ i, c i • v i = 0 (vector equation in Fin k → ℂ)
  -- Extract component-wise: for each j, ∑ i, c i * basis(i).regularValue(pts j) = 0
  have heval : ∀ j : Fin k,
      Finset.univ.sum (fun i => c i * (basis i).fn.regularValue (pts j)) = 0 := by
    intro j
    have := congr_fun hsum j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact this
  -- Apply zero-counting principle
  have hzc := zero_counting_linear_combination CRS D hdeg basis c pts hpts_inj
    hpts_reg hpts_D heval
  -- Apply IsLinIndepLS to get all c i = 0
  have hall := hli c (fun p hreg => hzc p (fun i => hreg i))
  -- But c i₀ ≠ 0, contradiction
  exact hi₀ (hall i₀)

/-- Helper: reformulation for Nat.find -/
private theorem h0_find_pred (CRS : CompactRiemannSurface)
    (D : Divisor CRS.toRiemannSurface) :
    ∃ N : ℕ, ¬ ∃ (basis : Fin (N + 1) → LinearSystem CRS.toRiemannSurface D),
      IsLinIndepLS CRS D basis := by
  obtain ⟨N, hN⟩ := h0_bounded CRS D
  exact ⟨N, hN (N + 1) (Nat.lt_succ_of_le le_rfl)⟩

/-- The dimension h⁰(D) = dim H⁰(X, O(D)).

    This is the maximum number of ℂ-linearly independent meromorphic functions
    with poles bounded by D.

    **Definition:** h⁰(D) is the smallest N such that no family of N+1 elements
    in L(D) is ℂ-linearly independent. Equivalently, it is the maximum n such
    that there exist n linearly independent elements.

    **Key properties:**
    - h⁰(0) = 1 (only constant functions on compact surfaces)
    - h⁰(D) = 0 if deg(D) < 0 (no non-zero sections)
    - h⁰(K) = g (holomorphic 1-forms have dimension g) -/
noncomputable def h0 (CRS : CompactRiemannSurface)
    (D : Divisor CRS.toRiemannSurface) : ℕ :=
  Nat.find (h0_find_pred CRS D)

/-- h⁰(D) satisfies: no h⁰(D)+1 linearly independent elements exist -/
theorem h0_spec (CRS : CompactRiemannSurface)
    (D : Divisor CRS.toRiemannSurface) :
    ¬ ∃ (basis : Fin (h0 CRS D + 1) → LinearSystem CRS.toRiemannSurface D),
      IsLinIndepLS CRS D basis := by
  unfold h0
  exact Nat.find_spec (h0_find_pred CRS D)

/-- h⁰ vanishes for divisors of negative degree.

    When deg(D) < 0, L(D) is empty: no meromorphic function f satisfies
    div(f) + D ≥ 0 (since deg(div(f)) = 0 by the argument principle,
    we'd need deg(D) ≥ 0). So no single element exists, hence h⁰ = 0. -/
theorem h0_vanishes_negative_degree (CRS : CompactRiemannSurface)
    (D : Divisor CRS.toRiemannSurface) (hdeg : D.degree < 0) :
    h0 CRS D = 0 := by
  have hempty := linearSystem_empty_negative_degree CRS D hdeg
  -- h0 = Nat.find (...), and we need to show the predicate holds at 0
  unfold h0
  rw [Nat.find_eq_zero]
  -- Need: ¬ ∃ basis : Fin 1 → LinearSystem, IsLinIndepLS
  intro ⟨basis, _⟩
  -- LinearSystem is empty, so Fin 1 → LinearSystem is impossible
  exact hempty.false (basis ⟨0, Nat.zero_lt_one⟩)

/-!
## The Canonical Bundle

The canonical bundle K on a Riemann surface X is the cotangent bundle T*X,
whose sections are holomorphic 1-forms.
-/

/-- The canonical divisor class on a compact Riemann surface.
    This is the divisor of any meromorphic 1-form.
    All such divisors are linearly equivalent, defining a unique divisor class.

    The degree of the canonical divisor is 2g - 2 (Riemann-Hurwitz formula).

    **Mathematical definition:**
    K = div(ω) for any non-zero meromorphic 1-form ω on Σ.
    The canonical class [K] ∈ Pic(Σ) is well-defined since any two
    meromorphic 1-forms differ by a meromorphic function.

    **Note on h0(K) = g:**
    The property h⁰(K) = g is a THEOREM (from Hodge theory: H⁰(K) ≅ H^{1,0}
    and dim H^{1,0} = g = topological genus), NOT a definition.
    See `h0_canonical_eq_genus` below. -/
structure CanonicalDivisor (CRS : CompactRiemannSurface) where
  /-- A representative divisor in the canonical class -/
  representative : Divisor CRS.toRiemannSurface
  /-- The degree equals 2g - 2 -/
  degree_eq : representative.degree = 2 * CRS.genus - 2

/-- h⁰(K) = g: holomorphic 1-forms have dimension equal to the topological genus.

    This is the Hodge theorem connecting analytic and topological data:
    H⁰(K) ≅ H^{1,0}(X) (holomorphic 1-forms) and dim H^{1,0} = g (topological genus).
    Here g = CRS.genus is the TOPOLOGICAL genus of the surface.

    **Proof path:**
    1. H⁰(K) ≅ Harmonic10Forms (via harmonic_10_are_canonical_sections)
    2. dim Harmonic10Forms = g (via dim_harmonic_10_eq_genus — Hodge theorem) -/
theorem h0_canonical_eq_genus (CRS : CompactRiemannSurface) (K : CanonicalDivisor CRS) :
    h0 CRS K.representative = CRS.genus := by
  sorry

/-- Existence of a canonical divisor on any compact Riemann surface.
    This follows from the existence of non-zero meromorphic 1-forms
    and the Hodge theory identification H⁰(K) ≅ H^{1,0}(X). -/
theorem canonical_divisor_exists (CRS : CompactRiemannSurface) :
    Nonempty (CanonicalDivisor CRS) := by
  sorry  -- Requires: existence of meromorphic 1-forms

/-- The degree of the canonical divisor is 2g - 2 (Riemann-Hurwitz).
    This fundamental formula connects the genus to the canonical bundle. -/
theorem deg_canonical_eq_2g_minus_2 (CRS : CompactRiemannSurface)
    (K : CanonicalDivisor CRS) :
    K.representative.degree = 2 * CRS.genus - 2 :=
  K.degree_eq

/-!
## h⁰(0) = 1: Constant Functions

Infrastructure to prove h⁰(0) = 1, needed for the base case of Riemann-Roch.
-/

/-- The constant function 1 is in the linear system L(0) -/
theorem one_in_linearSystem_zero (RS : RiemannSurface) :
    Divisor.Effective (divisorOf (1 : AnalyticMeromorphicFunction RS) + 0) := by
  rw [add_zero, divisorOf_one]
  intro p
  rfl

/-- The constant 1 as a LinearSystem element of L(0), with holomorphicity proof -/
noncomputable def one_linearSystem (RS : RiemannSurface) : LinearSystem RS 0 where
  fn := 1
  effective := one_in_linearSystem_zero RS
  holomorphicAway := by
    intro p _
    letI := RS.topology
    letI := RS.chartedSpace
    haveI := RS.isManifold
    suffices h : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (fun _ : RS.carrier => (1 : ℂ)) p by
      exact h.congr_of_eventuallyEq
        (Filter.Eventually.of_forall
          (fun q => (AnalyticMeromorphicFunction.regularValue_one q).symm))
    exact contMDiffAt_const.mdifferentiableAt one_ne_zero
  chartMeromorphic := by
    intro p
    letI := RS.topology
    letI := RS.chartedSpace
    -- regularValue of 1 is the constant function 1
    -- Constant functions are meromorphic
    have : (1 : AnalyticMeromorphicFunction RS).regularValue ∘
        (extChartAt 𝓘(ℂ, ℂ) p).symm = fun _ => 1 := by
      ext z; simp [AnalyticMeromorphicFunction.regularValue_one, Function.comp]
    rw [this]
    exact analyticAt_const.meromorphicAt
  chartOrderAt_eq := by
    intro p
    letI := RS.topology
    letI := RS.chartedSpace
    -- chartOrderAt of the constant 1 function = 0 = order of AMF 1
    unfold chartOrderAt chartRep chartPt
    have hrv : (1 : AnalyticMeromorphicFunction RS).regularValue ∘
        (extChartAt 𝓘(ℂ, ℂ) p).symm = fun _ => (1 : ℂ) := by
      ext z; simp [AnalyticMeromorphicFunction.regularValue_one]
    have hord : (1 : AnalyticMeromorphicFunction RS).order p = 0 := rfl
    rw [hrv, hord]
    simp [meromorphicOrderAt_const, one_ne_zero]

/-- L(0) is nonempty -/
theorem linearSystem_zero_nonempty (RS : RiemannSurface) :
    Nonempty (LinearSystem RS 0) :=
  ⟨one_linearSystem RS⟩

/-- The order of the constant 1 function is 0 at every point -/
private theorem order_one_eq_zero (RS : RiemannSurface) (p : RS.carrier) :
    (1 : AnalyticMeromorphicFunction RS).order p = 0 := by
  show AnalyticMeromorphicFunction.one.order p = 0
  rfl

/-- The singleton {1} in L(0) is linearly independent -/
theorem one_linIndep_in_L0 (CRS : CompactRiemannSurface) :
    IsLinIndepLS CRS 0
      (fun _ : Fin 1 => one_linearSystem CRS.toRiemannSurface) := by
  intro c hzero i
  fin_cases i
  have ⟨p⟩ := CRS.toRiemannSurface.connected.toNonempty
  have hreg : ∀ (j : Fin 1),
      ((fun _ => one_linearSystem CRS.toRiemannSurface) j).fn.order p ≥ 0 := by
    intro j
    show (1 : AnalyticMeromorphicFunction CRS.toRiemannSurface).order p ≥ 0
    rw [order_one_eq_zero]
  have hzp := hzero p hreg
  simp only [Fin.sum_univ_one] at hzp
  have hval : ((fun _ : Fin 1 => one_linearSystem CRS.toRiemannSurface)
        (0 : Fin 1)).fn.regularValue p = 1 :=
    AnalyticMeromorphicFunction.regularValue_one p
  rw [hval, mul_one] at hzp
  exact hzp

/-- Elements of L(0) have no poles (order ≥ 0 everywhere) -/
private lemma effective_zero_implies_nonneg_order {RS : RiemannSurface}
    (f : LinearSystem RS 0) (p : RS.carrier) :
    0 ≤ f.fn.order p := by
  have h := f.effective p
  rw [add_zero] at h
  exact h

/-- On a compact Riemann surface, an analytic meromorphic function without poles
    has constant nonzero regularValue. -/
theorem amf_no_poles_is_nonzero_constant (CRS : CompactRiemannSurface)
    (f : AnalyticMeromorphicFunction CRS.toRiemannSurface)
    (hord : ∀ p, 0 ≤ f.order p)
    (hhol : ∀ p, @MDifferentiableAt ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ)
      CRS.toRiemannSurface.carrier CRS.toRiemannSurface.topology
      CRS.toRiemannSurface.chartedSpace ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ℂ _ _
      f.regularValue p) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ p, f.regularValue p = c := by
  have hholAll : CRS.toRiemannSurface.IsHolomorphic f.regularValue := hhol
  obtain ⟨c, hc⟩ := CRS.holomorphicIsConstant f.regularValue hholAll
  refine ⟨c, ?_, hc⟩
  intro hc0
  have hfun_zero : ∀ p, f.toFun p = Sum.inl 0 := by
    intro p
    have hval := hc p
    rw [hc0] at hval
    unfold AnalyticMeromorphicFunction.regularValue at hval
    have hnotpole : ¬(f.order p < 0) := not_lt.mpr (hord p)
    cases hfp : f.toFun p with
    | inl z =>
      simp only [hfp] at hval
      rw [hval]
    | inr _ =>
      exact absurd ((f.order_neg_iff_pole p).mpr hfp) hnotpole
  have hord_pos : ∀ p, 0 < f.order p := fun p =>
    (f.order_pos_iff_zero p).mpr (hfun_zero p)
  have hsub : (Set.univ : Set CRS.toRiemannSurface.carrier) ⊆
      { p | f.order p ≠ 0 } := by
    intro p _
    exact ne_of_gt (hord_pos p)
  haveI := RiemannSurface.carrier_infinite CRS.toRiemannSurface
  exact (Set.infinite_univ.mono hsub) f.order_finiteSupport

/-- Any two elements of L(0) on a compact RS are proportional. -/
theorem linearSystem_zero_no_two_indep (CRS : CompactRiemannSurface) :
    ¬ ∃ (basis : Fin 2 → LinearSystem CRS.toRiemannSurface 0),
      IsLinIndepLS CRS 0 basis := by
  intro ⟨basis, hli⟩
  obtain ⟨c₀, hc₀ne, hc₀⟩ := amf_no_poles_is_nonzero_constant CRS (basis 0).fn
    (fun p => effective_zero_implies_nonneg_order (basis 0) p)
    (fun p => (basis 0).holomorphicAway p (effective_zero_implies_nonneg_order (basis 0) p))
  obtain ⟨c₁, hc₁ne, hc₁⟩ := amf_no_poles_is_nonzero_constant CRS (basis 1).fn
    (fun p => effective_zero_implies_nonneg_order (basis 1) p)
    (fun p => (basis 1).holomorphicAway p (effective_zero_implies_nonneg_order (basis 1) p))
  have h := hli (fun i : Fin 2 => if i = 0 then c₁ else -c₀) (fun p hreg => by
    simp only [Fin.sum_univ_two]
    simp only [ite_true, show ¬((1 : Fin 2) = 0) from by decide, ite_false]
    rw [hc₀ p, hc₁ p]; ring)
  have hc₁_zero := h ⟨0, by omega⟩
  simp only [show (⟨0, by omega⟩ : Fin 2) = 0 from rfl, ite_true] at hc₁_zero
  exact hc₁ne hc₁_zero

/-- For the trivial bundle (D = 0), h⁰ = 1 (constant functions) -/
theorem h0_trivial (CRS : CompactRiemannSurface) :
    h0 CRS (0 : Divisor CRS.toRiemannSurface) = 1 := by
  show Nat.find (h0_find_pred CRS 0) = 1
  apply le_antisymm
  · exact Nat.find_le (linearSystem_zero_no_two_indep CRS)
  · have h0ne : Nat.find (h0_find_pred CRS 0) ≠ 0 := by
      intro heq
      rw [Nat.find_eq_zero] at heq
      exact heq ⟨fun _ => one_linearSystem CRS.toRiemannSurface,
             one_linIndep_in_L0 CRS⟩
    omega

/-!
## Euler Characteristic and Correction Term

The proof of Riemann-Roch uses the "correction term" approach:
1. Define χ(D) = h⁰(D) - h⁰(K-D) (using h⁰ of the "dual" divisor K-D)
2. Show f(D) = χ(D) - deg(D) is invariant under D → D ± [p]
   via eval_residue_complementarity
3. By induction on total variation, f(D) = f(0) = 1 - g

Note: χ(D) = h⁰(D) - h⁰(K-D) is the h⁰-only form of the Euler characteristic.
By Serre duality (a separate theorem), h⁰(K-D) = h¹(D) (Dolbeault cohomology),
giving the classical χ(D) = h⁰(D) - h¹(D).
-/

/-- The Euler characteristic χ(D) = h⁰(D) - h⁰(K - D).

    This is the h⁰-only form. By Serre duality, h⁰(K-D) = h¹(D),
    so this equals the classical Euler characteristic h⁰(D) - h¹(D). -/
noncomputable def chi (CRS : CompactRiemannSurface)
    (D : Divisor CRS.toRiemannSurface) (K : CanonicalDivisor CRS) : ℤ :=
  (h0 CRS D : ℤ) - (h0 CRS (K.representative + (-D)) : ℤ)

/-- **Evaluation-residue complementarity.**

    For any divisor D and point p on a compact Riemann surface with canonical
    divisor K, exactly one of the following holds:
    - h⁰(D + [p]) = h⁰(D) + 1 (the evaluation map L(D+[p]) → ℂ is surjective)
    - h⁰(K - D) = h⁰(K - D - [p]) + 1 (there exists ω ∈ L(K-D) not vanishing at p)

    Precisely: the sum of the two "jumps" equals 1.

    **Mathematical content:**
    This follows from the long exact cohomology sequence associated to
    0 → O(D) → O(D + [p]) → k_p → 0, which gives:
    0 → H⁰(O(D)) → H⁰(O(D+[p])) →^{ev} ℂ →^{δ} H¹(O(D)) → H¹(O(D+[p])) → 0

    The alternating sum of dimensions of an exact sequence is 0:
    h⁰(D) - h⁰(D+[p]) + 1 - h¹(D) + h¹(D+[p]) = 0

    Equivalently, using h¹(D) = h⁰(K-D):
    [h⁰(D+[p]) - h⁰(D)] + [h⁰(K-D) - h⁰(K-D-[p])] = 1

    **Proof approaches:**
    1. Sheaf cohomology long exact sequence (requires sheaf theory infrastructure)
    2. Residue pairing: the obstruction to extending a polar part at p is
       measured by the residue pairing with sections of K-D
    3. ∂̄-equation solvability (Hodge theory approach) -/
theorem eval_residue_complementarity (CRS : CompactRiemannSurface)
    (K : CanonicalDivisor CRS)
    (D : Divisor CRS.toRiemannSurface) (p : CRS.toRiemannSurface.carrier) :
    (h0 CRS (D + Divisor.point p) : ℤ) - (h0 CRS D : ℤ) +
    ((h0 CRS (K.representative + (-D)) : ℤ) -
     (h0 CRS (K.representative + (-(D + Divisor.point p))) : ℤ)) = 1 := by
  sorry -- Requires: residue pairing / ∂̄-equation solvability / sheaf cohomology

/-- The Euler characteristic step: χ(D + [p]) = χ(D) + 1.

    This encodes the long exact cohomology sequence from
    0 → O(D) → O(D + [p]) →^{ev_p} k_p → 0:
    0 → H⁰(O(D)) → H⁰(O(D+[p])) → ℂ → H¹(O(D)) → H¹(O(D+[p])) → 0

    Taking alternating sum of dimensions: χ(D+[p]) - χ(D) = 1. -/
theorem chi_add_point (CRS : CompactRiemannSurface) (K : CanonicalDivisor CRS)
    (D : Divisor CRS.toRiemannSurface) (p : CRS.toRiemannSurface.carrier) :
    chi CRS (D + Divisor.point p) K = chi CRS D K + 1 := by
  unfold chi
  have hcomp := eval_residue_complementarity CRS K D p
  omega

/-- The correction term f(D) = χ(D) - deg(D).
    The key insight is that f is constant across all divisors. -/
noncomputable def correction (CRS : CompactRiemannSurface) (K : CanonicalDivisor CRS)
    (D : Divisor CRS.toRiemannSurface) : ℤ :=
  chi CRS D K - D.degree

/-- Adding a point preserves the correction term:
    f(D + [p]) = (χ(D) + 1) - (deg(D) + 1) = χ(D) - deg(D) = f(D) -/
theorem correction_add_point (CRS : CompactRiemannSurface) (K : CanonicalDivisor CRS)
    (D : Divisor CRS.toRiemannSurface) (p : CRS.toRiemannSurface.carrier) :
    correction CRS K (D + Divisor.point p) = correction CRS K D := by
  unfold correction
  rw [chi_add_point, Divisor.degree_add, Divisor.degree_point]
  omega

/-- Subtracting a point preserves the correction term -/
theorem correction_sub_point (CRS : CompactRiemannSurface) (K : CanonicalDivisor CRS)
    (D : Divisor CRS.toRiemannSurface) (p : CRS.toRiemannSurface.carrier) :
    correction CRS K (D + (-(Divisor.point p))) = correction CRS K D := by
  have h := correction_add_point CRS K (D + (-(Divisor.point p))) p
  rw [show D + -(Divisor.point p) + Divisor.point p = D from by
    rw [add_assoc, neg_add_cancel, add_zero]] at h
  exact h.symm

/-!
## Total Variation and Descent
-/

/-- Total variation of a divisor: TV(D) = Σ_{p ∈ supp(D)} |D(p)| -/
noncomputable def totalVariation {RS : RiemannSurface} (D : Divisor RS) : ℕ :=
  D.finiteSupport.toFinset.sum (fun p => (D.coeff p).natAbs)

-- Helper: coefficient at different point from Divisor.point is 0
private lemma coeff_point_ne' {RS : RiemannSurface} {p q : RS.carrier} (h : q ≠ p) :
    (Divisor.point p).coeff q = 0 := if_neg h

-- Helper: coefficient at same point from Divisor.point is 1
private lemma coeff_point_self' {RS : RiemannSurface} (p : RS.carrier) :
    (Divisor.point (RS := RS) p).coeff p = 1 := if_pos rfl

-- Helper for natAbs comparison
private lemma natAbs_sub_one_lt (n : ℤ) (hn : 0 < n) : (n - 1).natAbs < n.natAbs := by
  have h1 : (0 : ℤ) ≤ n - 1 := by omega
  have e1 : ((n - 1).natAbs : ℤ) = n - 1 := Int.natAbs_of_nonneg h1
  have e2 : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg (by omega)
  exact_mod_cast show ((n - 1).natAbs : ℤ) < (n.natAbs : ℤ) by rw [e1, e2]; omega

private lemma natAbs_add_one_lt_of_neg (n : ℤ) (hn : n < 0) : (n + 1).natAbs < n.natAbs := by
  -- Reduce to natAbs_sub_one_lt applied to -n > 0
  have h := natAbs_sub_one_lt (-n) (by omega)
  rwa [show -n - 1 = -(n + 1) from by ring, Int.natAbs_neg, Int.natAbs_neg] at h

/-- Subtracting [p] when D(p) > 0 decreases total variation -/
theorem tv_desc_sub {RS : RiemannSurface} (D : Divisor RS) (p : RS.carrier)
    (hp : 0 < D.coeff p) :
    totalVariation (D + (-(Divisor.point p))) < totalVariation D := by
  set D' := D + (-(Divisor.point p)) with hD'_def
  -- Coefficient relationships
  have coeff_ne : ∀ q, q ≠ p → D'.coeff q = D.coeff q := by
    intro q hq
    show D.coeff q + (-(Divisor.point p)).coeff q = D.coeff q
    rw [show (-(Divisor.point p)).coeff q = -((Divisor.point p).coeff q) from rfl,
        coeff_point_ne' hq, neg_zero, add_zero]
  have coeff_p : D'.coeff p = D.coeff p - 1 := by
    show D.coeff p + (-(Divisor.point p)).coeff p = D.coeff p - 1
    rw [show (-(Divisor.point p)).coeff p = -((Divisor.point p).coeff p) from rfl,
        coeff_point_self']; omega
  -- supp(D') ⊆ supp(D)
  have supp_sub : D'.finiteSupport.toFinset ⊆ D.finiteSupport.toFinset := by
    intro q hq
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hq ⊢
    by_cases hqp : q = p
    · subst hqp; omega
    · rwa [coeff_ne q hqp] at hq
  -- Extend TV(D') to sum over supp(D)
  have hTV' : totalVariation D' =
      D.finiteSupport.toFinset.sum (fun q => (D'.coeff q).natAbs) := by
    unfold totalVariation
    exact Finset.sum_subset supp_sub (fun q _ hq => by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hq; simp [hq])
  rw [hTV']; unfold totalVariation
  apply Finset.sum_lt_sum
  · intro q _
    by_cases hqp : q = p
    · subst hqp; rw [coeff_p]; exact le_of_lt (natAbs_sub_one_lt _ hp)
    · rw [coeff_ne q hqp]
  · exact ⟨p, by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]; omega,
      by rw [coeff_p]; exact natAbs_sub_one_lt _ hp⟩

/-- Adding [p] when D(p) < 0 decreases total variation -/
theorem tv_desc_add {RS : RiemannSurface} (D : Divisor RS) (p : RS.carrier)
    (hp : D.coeff p < 0) :
    totalVariation (D + Divisor.point p) < totalVariation D := by
  set D' := D + Divisor.point p with hD'_def
  -- Coefficient relationships
  have coeff_ne : ∀ q, q ≠ p → D'.coeff q = D.coeff q := by
    intro q hq
    show D.coeff q + (Divisor.point p).coeff q = D.coeff q
    rw [coeff_point_ne' hq, add_zero]
  have coeff_p : D'.coeff p = D.coeff p + 1 := by
    show D.coeff p + (Divisor.point p).coeff p = D.coeff p + 1
    rw [coeff_point_self']
  -- supp(D') ⊆ supp(D)
  have supp_sub : D'.finiteSupport.toFinset ⊆ D.finiteSupport.toFinset := by
    intro q hq
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hq ⊢
    by_cases hqp : q = p
    · subst hqp; omega
    · rwa [coeff_ne q hqp] at hq
  -- Extend TV(D') to sum over supp(D)
  have hTV' : totalVariation D' =
      D.finiteSupport.toFinset.sum (fun q => (D'.coeff q).natAbs) := by
    unfold totalVariation
    exact Finset.sum_subset supp_sub (fun q _ hq => by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hq; simp [hq])
  rw [hTV']; unfold totalVariation
  apply Finset.sum_lt_sum
  · intro q _
    by_cases hqp : q = p
    · subst hqp; rw [coeff_p]; exact le_of_lt (natAbs_add_one_lt_of_neg _ hp)
    · rw [coeff_ne q hqp]
  · exact ⟨p, by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]; omega,
      by rw [coeff_p]; exact natAbs_add_one_lt_of_neg _ hp⟩

/-- The correction term is constant: f(D) = f(0) for all D.

    **Proof:** By strong induction on total variation TV(D).
    - Base: TV(D) = 0 implies D = 0.
    - Step: Pick p with D(p) ≠ 0. If D(p) > 0, subtract [p];
      if D(p) < 0, add [p]. This preserves f and decreases TV. -/
theorem correction_eq_zero_correction (CRS : CompactRiemannSurface)
    (K : CanonicalDivisor CRS) (D : Divisor CRS.toRiemannSurface) :
    correction CRS K D = correction CRS K 0 := by
  suffices h : ∀ (n : ℕ) (D : Divisor CRS.toRiemannSurface),
      totalVariation D ≤ n → correction CRS K D = correction CRS K 0 from
    h _ D le_rfl
  intro n
  induction n with
  | zero =>
    intro D hD
    have hzero : totalVariation D = 0 := Nat.eq_zero_of_le_zero hD
    have hDeq : D = 0 := by
      ext p
      change D.coeff p = 0
      unfold totalVariation at hzero
      by_cases hp : p ∈ D.finiteSupport.toFinset
      · exact Int.natAbs_eq_zero.mp (Finset.sum_eq_zero_iff.mp hzero p hp)
      · rwa [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hp
    rw [hDeq]
  | succ n ih =>
    intro D hD
    by_cases hDz : D = 0
    · rw [hDz]
    · -- Find p with D(p) ≠ 0
      have ⟨p, hp⟩ : ∃ p, D.coeff p ≠ 0 := by
        by_contra hall; push_neg at hall
        exact hDz (Divisor.ext (fun q => by change D.coeff q = 0; exact hall q))
      rcases lt_or_gt_of_ne hp with hneg | hpos
      · -- D(p) < 0: add [p], preserves f and decreases TV
        rw [← correction_add_point CRS K D p]
        exact ih _ (by have := tv_desc_add D p hneg; omega)
      · -- D(p) > 0: subtract [p], preserves f and decreases TV
        rw [← correction_sub_point CRS K D p]
        exact ih _ (by have := tv_desc_sub D p hpos; omega)

/-!
## The Riemann-Roch Formula (h⁰ duality form)

The core content of Riemann-Roch, stated purely in terms of h⁰:

  h⁰(D) - h⁰(K - D) = deg(D) + 1 - g

This is proven via:
1. eval_residue_complementarity ⟹ χ(D + [p]) = χ(D) + 1
2. Correction term f(D) = χ(D) - deg(D) is invariant
3. Base case: f(0) = h⁰(0) - h⁰(K) - 0 = 1 - g (uses h⁰(K) = g as hypothesis)
-/

/-- **Riemann-Roch Theorem (h⁰ duality form)**

    For a compact Riemann surface X of genus g, canonical divisor K, and any divisor D:

      h⁰(D) - h⁰(K - D) = deg(D) + 1 - g

    This is the core identity. Combined with Serre duality h¹(D) = h⁰(K-D),
    it gives the classical Riemann-Roch formula h⁰(D) - h¹(D) = deg(D) + 1 - g.

    The hypothesis hK : h⁰(K) = g is a consequence of the Hodge theorem
    (see h0_canonical_eq_genus), which we take as an explicit hypothesis here
    to cleanly separate the R-R argument from Hodge theory.

    **Proof:** The correction term f(D) = χ(D) - deg(D) is constant
    (by chi_add_point and induction on total variation).
    At D = 0: f(0) = h⁰(0) - h⁰(K) - 0 = 1 - g.
    Therefore χ(D) = deg(D) + 1 - g for all D. -/
theorem riemann_roch_h0_duality (CRS : CompactRiemannSurface)
    (D : Divisor CRS.toRiemannSurface) (K : CanonicalDivisor CRS)
    (hK : h0 CRS K.representative = CRS.genus) :
    (h0 CRS D : ℤ) - (h0 CRS (K.representative + (-D)) : ℤ) =
      D.degree + 1 - CRS.genus := by
  -- f(D) = f(0): the correction term is constant
  have h_corr := correction_eq_zero_correction CRS K D
  unfold correction chi at h_corr
  -- h_corr : h0(D) - h0(K-D) - deg(D) = h0(0) - h0(K-0) - deg(0)
  -- Base case: h0(0) - h0(K) - 0 = 1 - g
  have h_base : (h0 CRS (0 : Divisor CRS.toRiemannSurface) : ℤ) -
      (h0 CRS (K.representative + -(0 : Divisor CRS.toRiemannSurface)) : ℤ) -
      (0 : Divisor CRS.toRiemannSurface).degree = 1 - CRS.genus := by
    rw [neg_zero, add_zero, h0_trivial, hK, Divisor.degree_zero]
    omega
  omega

/-!
## Corollaries of Riemann-Roch
-/

/-- For a divisor of degree > 2g - 2, we have h⁰(K - D) = 0 -/
theorem h0_KminusD_vanishes_high_degree (CRS : CompactRiemannSurface)
    (D : Divisor CRS.toRiemannSurface) (K : CanonicalDivisor CRS)
    (hdeg : D.degree > 2 * CRS.genus - 2) :
    h0 CRS (K.representative + (-D)) = 0 := by
  -- deg(K - D) = 2g - 2 - deg(D) < 0
  have hdeg_neg : (K.representative + (-D)).degree < 0 := by
    rw [Divisor.degree_add, Divisor.degree_neg, K.degree_eq]
    omega
  exact h0_vanishes_negative_degree CRS _ hdeg_neg

/-- For a divisor of degree > 2g - 2, Riemann-Roch simplifies:
    h⁰(D) = deg(D) + 1 - g -/
theorem riemann_roch_high_degree (CRS : CompactRiemannSurface)
    (D : Divisor CRS.toRiemannSurface) (K : CanonicalDivisor CRS)
    (hK : h0 CRS K.representative = CRS.genus)
    (hdeg : D.degree > 2 * CRS.genus - 2) :
    (h0 CRS D : ℤ) = D.degree + 1 - CRS.genus := by
  have h0_zero := h0_KminusD_vanishes_high_degree CRS D K hdeg
  have rr := riemann_roch_h0_duality CRS D K hK
  simp only [h0_zero, CharP.cast_eq_zero, sub_zero] at rr
  exact rr

/-!
## Connection to Hodge Theory

Our Hodge theory development provides the analytical foundation:
-/

/-- Dimension of holomorphic 1-forms equals topological genus -/
theorem dim_holomorphic_1forms_eq_genus (CRS : CompactRiemannSurface) :
    ∃ (basis : Fin CRS.genus → Harmonic10Forms CRS.toRiemannSurface),
      Function.Injective basis :=
  dim_harmonic_10_eq_genus CRS

/-- Harmonic (1,0)-forms correspond to sections of the canonical bundle.

    More precisely, there is an isomorphism:
    Harmonic10Forms(Σ) ≅ H⁰(Σ, K)

    This identifies holomorphic 1-forms (which are automatically harmonic
    on a Riemann surface) with sections of the canonical bundle. -/
theorem harmonic_10_are_canonical_sections (CRS : CompactRiemannSurface)
    (K : CanonicalDivisor CRS) :
    ∃ (iso : Harmonic10Forms CRS.toRiemannSurface →
             H0VectorSpace CRS K.representative),
      Function.Bijective iso := by
  sorry  -- Requires: identification of holomorphic 1-forms with K-sections

/-!
## Dolbeault Cohomology and Serre Duality

The proper definition of h¹(D) is via Dolbeault cohomology:
  h¹(D) = dim(Ω^{0,1}(D) / im ∂̄_D)

For the trivial bundle D = 0, this is defined in DolbeaultCohomology.lean.
For general D, it requires twisted ∂̄-operators on sections of O(D).

Serre duality h¹(D) = h⁰(K - D) is a THEOREM, not a definition.
Combined with riemann_roch_h0_duality, it gives the classical formula.
-/

/-- A (0,1)-connection form A represents the holomorphic line bundle O(D) if
    its local singularity structure matches the divisor D.

    **Characterization**: In local coordinates z around each point p, a (0,1)-form
    ω = f(z) dz̄ is a connection form for D if:
      f(z) = D(p) / (2(z̄ - ā)) + h(z)
    where a = chart(p) and h is continuous (hence smooth) near a.

    This encodes the curvature condition ∂A = 2πi Σ D(p) δ_p:
    - At p with D(p) = 0: A is smooth (h is the full coefficient)
    - At p with D(p) = n: A has a prescribed 1/z̄ singularity with residue n/2

    For D = 0, A = 0 satisfies this condition (h = 0 everywhere). -/
def IsConnectionFormFor (CRS : CompactRiemannSurface)
    (D : Divisor CRS.toRiemannSurface) (A : Form_01 CRS.toRiemannSurface) : Prop :=
  let RS := CRS.toRiemannSurface
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  -- For each point p, the (0,1)-form coefficient A.toSection has the prescribed
  -- singularity structure D(p)/(2(z̄-ā)) in local coordinates.
  ∀ (p : RS.carrier),
    let e := extChartAt (I := 𝓘(ℂ, ℂ)) p
    let a := e p
    -- There exists a continuous regularization near p
    ∃ (h : ℂ → ℂ), ContinuousAt h a ∧
      ∀ᶠ z in nhdsWithin a {a}ᶜ,
        A.toSection (e.symm z) =
          (D.coeff p : ℂ) / (2 * starRingEnd ℂ (z - a)) + h z

/-- Every divisor D on a compact Riemann surface has a (0,1)-connection form.
    Follows from smooth triviality of complex line bundles on surfaces. -/
theorem connectionForm_exists (CRS : CompactRiemannSurface)
    (D : Divisor CRS.toRiemannSurface) :
    ∃ A : Form_01 CRS.toRiemannSurface, IsConnectionFormFor CRS D A := by
  sorry -- Requires: smooth triviality of line bundles, partition of unity

/-- h¹(D) via twisted Dolbeault cohomology with values in O(D).

    h¹(D) = dim_ℂ H^{0,1}(O(D)) = dim_ℂ (Ω^{0,1} / im(∂̄_A))

    where A is a (0,1)-connection form for O(D) and ∂̄_A = ∂̄ + A is the
    twisted ∂̄ operator. The dimension is independent of the choice of A
    (by gauge equivalence).

    For D = 0, A = 0 gives the standard Dolbeault cohomology `DolbeaultH01`. -/
noncomputable def h1_dolbeault (CRS : CompactRiemannSurface)
    (D : Divisor CRS.toRiemannSurface) : ℕ :=
  Module.finrank ℂ (TwistedDolbeaultH01 CRS.toRiemannSurface
    (connectionForm_exists CRS D).choose)

/-- **Serre duality** (analytic): h¹(D) = h⁰(K - D).

    This is a THEOREM relating Dolbeault cohomology to sections of the dual bundle,
    NOT a definition. It follows from the residue pairing and Hodge theory. -/
theorem serre_duality_h1 (CRS : CompactRiemannSurface) (K : CanonicalDivisor CRS)
    (D : Divisor CRS.toRiemannSurface) :
    h1_dolbeault CRS D = h0 CRS (K.representative + (-D)) := by
  sorry -- Requires: twisted Dolbeault cohomology, residue pairing, Hodge theory

/-- **Riemann-Roch Theorem (classical form)**

    h⁰(D) - h¹(D) = deg(D) + 1 - g

    where h¹ is defined via Dolbeault cohomology.
    This follows from the h⁰-duality form + Serre duality. -/
theorem riemann_roch_classical (CRS : CompactRiemannSurface)
    (D : Divisor CRS.toRiemannSurface) (K : CanonicalDivisor CRS)
    (hK : h0 CRS K.representative = CRS.genus) :
    (h0 CRS D : ℤ) - (h1_dolbeault CRS D : ℤ) = D.degree + 1 - CRS.genus := by
  rw [serre_duality_h1 CRS K]
  exact riemann_roch_h0_duality CRS D K hK

/-- The Euler characteristic χ(O) = 1 - g -/
theorem euler_characteristic_structure_sheaf (CRS : CompactRiemannSurface)
    (K : CanonicalDivisor CRS)
    (hK : h0 CRS K.representative = CRS.genus) :
    (h0 CRS (0 : Divisor CRS.toRiemannSurface) : ℤ) -
    (h0 CRS (K.representative + (-(0 : Divisor CRS.toRiemannSurface))) : ℤ) =
      1 - CRS.genus := by
  have rr := riemann_roch_h0_duality CRS 0 K hK
  simp only [Divisor.degree_zero] at rr
  exact rr

end RiemannSurfaces.Analytic
