import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Analytic k-th Roots of Nonvanishing Analytic Functions

## Main Result

`analytic_kth_root`: If g is analytic at z₀ with g(z₀) ≠ 0, then g has an analytic
k-th root near z₀. That is, there exists h analytic at z₀ with h(z)^k = g(z)
in a neighborhood of z₀ and h(z₀) ≠ 0.

## Proof Strategy

Use the analytic inverse function theorem for Φ(w) = w^k.
Since Φ'(ω₀) = k * ω₀^(k-1) ≠ 0 at any ω₀ ≠ 0, Φ has an analytic local inverse Ψ.
Then h = Ψ ∘ g is the desired k-th root.

## References

* Forster, "Lectures on Riemann Surfaces", Chapter 1
-/

namespace AnalyticKthRoot

open Complex Topology
open scoped Polynomial

/-!
## k-th roots in ℂ

Every nonzero complex number has a k-th root (for k ≥ 1), since ℂ is algebraically closed.
-/

/-- Every nonzero element of ℂ has a k-th root (for k ≥ 1). -/
theorem exists_kth_root (a : ℂ) (ha : a ≠ 0) (k : ℕ) (hk : 0 < k) :
    ∃ ω : ℂ, ω ^ k = a ∧ ω ≠ 0 := by
  -- ℂ is algebraically closed, so X^k - a has a root
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  have h_deg : (Polynomial.X ^ k - Polynomial.C a : ℂ[X]).degree ≠ 0 := by
    rw [Polynomial.degree_X_pow_sub_C hk a]
    exact_mod_cast hk.ne'
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root _ h_deg
  simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hω
  exact ⟨ω, hω, fun h => ha (by rw [← hω, h, zero_pow (by omega)])⟩

/-!
## Analytic inverse function theorem for the power map

The map w ↦ w^k is analytic with derivative k * w^(k-1), which is nonzero when w ≠ 0.
By the analytic IFT, it has an analytic local inverse near any nonzero point.
-/

/-- The power map w ↦ w^k is analytic everywhere. -/
theorem analyticAt_pow (k : ℕ) (w₀ : ℂ) : AnalyticAt ℂ (· ^ k) w₀ :=
  analyticAt_id.pow k

/-- The derivative of w ↦ w^k at w₀. -/
theorem deriv_pow_eq (k : ℕ) (w₀ : ℂ) :
    deriv (· ^ k : ℂ → ℂ) w₀ = k * w₀ ^ (k - 1) :=
  (hasDerivAt_pow k w₀).deriv

/-- The derivative of w ↦ w^k is nonzero when w₀ ≠ 0 and k ≥ 1. -/
theorem deriv_pow_ne_zero (k : ℕ) (hk : 1 ≤ k) (w₀ : ℂ) (hw₀ : w₀ ≠ 0) :
    deriv (· ^ k : ℂ → ℂ) w₀ ≠ 0 := by
  rw [deriv_pow_eq]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (pow_ne_zero _ hw₀)

/-!
## Main theorem: analytic k-th root
-/

/-- **Analytic k-th root theorem.**

If g is analytic at z₀ with g(z₀) ≠ 0 and k ≥ 1, then there exists an analytic
function h near z₀ with h(z)^k = g(z) for z near z₀ and h(z₀) ≠ 0.

**Proof:** Choose ω₀ with ω₀^k = g(z₀). The map Φ(w) = w^k has an analytic
local inverse Ψ at ω₀ (by the analytic IFT, since Φ'(ω₀) ≠ 0). Then
h = Ψ ∘ g is the desired k-th root. -/
theorem analytic_kth_root {g : ℂ → ℂ} {z₀ : ℂ} {k : ℕ} (hk : 1 ≤ k)
    (hg : AnalyticAt ℂ g z₀) (hg_ne : g z₀ ≠ 0) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h z₀ ∧ h z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, h z ^ k = g z := by
  -- Step 1: Find ω₀ with ω₀^k = g(z₀) and ω₀ ≠ 0
  obtain ⟨ω₀, hω₀_pow, hω₀_ne⟩ := exists_kth_root (g z₀) hg_ne k (by omega)
  -- Step 2: The power map Φ(w) = w^k
  set Φ : ℂ → ℂ := (· ^ k) with hΦ_def
  have hΦ_ana : AnalyticAt ℂ Φ ω₀ := analyticAt_pow k ω₀
  have hΦ'_ne : deriv Φ ω₀ ≠ 0 := deriv_pow_ne_zero k hk ω₀ hω₀_ne
  -- Step 3: Local inverse Ψ of Φ at ω₀
  set hsd := hΦ_ana.hasStrictDerivAt
  set Ψ := hsd.localInverse Φ (deriv Φ ω₀) ω₀ hΦ'_ne
  -- Ψ is analytic at Φ(ω₀) = g(z₀)
  have hΨ_ana_at_Φω₀ : AnalyticAt ℂ Ψ (Φ ω₀) := hΦ_ana.analyticAt_localInverse hΦ'_ne
  -- Φ(ω₀) = ω₀^k = g(z₀)
  have hΦω₀ : Φ ω₀ = g z₀ := hω₀_pow
  -- Ψ(Φ(ω₀)) = ω₀ (from left inverse at ω₀)
  have hΨ_id : Ψ (Φ ω₀) = ω₀ :=
    (hsd.eventually_left_inverse hΦ'_ne).self_of_nhds
  -- Φ(Ψ(y)) = y for y near Φ(ω₀)
  have hΦΨ : ∀ᶠ y in 𝓝 (Φ ω₀), Φ (Ψ y) = y :=
    hsd.eventually_right_inverse hΦ'_ne
  -- Step 4: Define h = Ψ ∘ g
  refine ⟨Ψ ∘ g, ?_, ?_, ?_⟩
  · -- h is analytic at z₀
    have hΨ_ana : AnalyticAt ℂ Ψ (g z₀) := hΦω₀ ▸ hΨ_ana_at_Φω₀
    exact hΨ_ana.comp hg
  · -- h(z₀) = Ψ(g(z₀)) = Ψ(Φ(ω₀)) = ω₀ ≠ 0
    show Ψ (g z₀) ≠ 0
    rw [show g z₀ = Φ ω₀ from hΦω₀.symm, hΨ_id]
    exact hω₀_ne
  · -- h(z)^k = g(z) for z near z₀
    -- Φ(h(z)) = Φ(Ψ(g(z))) = g(z) by right inverse, for z near z₀
    have hΦΨ_at_g : ∀ᶠ y in 𝓝 (g z₀), Φ (Ψ y) = y := hΦω₀ ▸ hΦΨ
    exact (hg.continuousAt.eventually hΦΨ_at_g).mono fun z hz => hz

/-- Variant of `analytic_kth_root` stating h(z₀)^k = g(z₀) (not just eventually). -/
theorem analytic_kth_root_with_value {g : ℂ → ℂ} {z₀ : ℂ} {k : ℕ} (hk : 1 ≤ k)
    (hg : AnalyticAt ℂ g z₀) (hg_ne : g z₀ ≠ 0) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h z₀ ∧ h z₀ ≠ 0 ∧ h z₀ ^ k = g z₀ ∧
      ∀ᶠ z in 𝓝 z₀, h z ^ k = g z := by
  obtain ⟨h, hh_ana, hh_ne, hh_eq⟩ := analytic_kth_root hk hg hg_ne
  exact ⟨h, hh_ana, hh_ne, hh_eq.self_of_nhds, hh_eq⟩

/-!
## Counting k-th roots

For w ≠ 0 in ℂ and k ≥ 1, the set {ζ : ζ^k = w} has exactly k elements.
-/

/-- The set of k-th roots of a nonzero complex number has exactly k elements. -/
theorem ncard_kthRoots (w : ℂ) (hw : w ≠ 0) (k : ℕ) (hk : 0 < k) :
    {ζ : ℂ | ζ ^ k = w}.ncard = k := by
  -- Use nthRoots = roots of X^k - C w
  set p := (Polynomial.X ^ k - Polynomial.C w : ℂ[X])
  -- p is separable (char 0, w ≠ 0)
  have hsep : p.Separable :=
    Polynomial.separable_X_pow_sub_C w (Nat.cast_ne_zero.mpr (by omega)) hw
  -- p.roots is nodup
  have hnodup : p.roots.Nodup := Polynomial.nodup_roots hsep
  -- p ≠ 0
  have hp_ne : p ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by omega) w
  -- p splits over ℂ (algebraically closed)
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  have hsplit : p.Splits := IsAlgClosed.splits p
  -- p.roots.card = k
  have hcard : p.roots.card = k := by
    rw [← hsplit.natDegree_eq_card_roots, Polynomial.natDegree_X_pow_sub_C]
  -- {ζ : ζ^k = w} = ↑(nthRoots k w).toFinset
  have hset : {ζ : ℂ | ζ ^ k = w} = ↑(Polynomial.nthRoots k w).toFinset := by
    ext ζ
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset,
      Polynomial.mem_nthRoots hk]
  -- nthRoots k w = p.roots
  have hnth_eq : Polynomial.nthRoots k w = p.roots := rfl
  rw [hset, Set.ncard_coe_finset, hnth_eq, Multiset.toFinset_card_of_nodup hnodup, hcard]

/-- All k-th roots of a nonzero complex number have the same modulus. -/
theorem norm_kthRoot_eq (w : ℂ) (k : ℕ) (ζ : ℂ) (hζ : ζ ^ k = w) :
    ‖ζ‖ ^ k = ‖w‖ := by
  rw [← Complex.norm_pow, hζ]

end AnalyticKthRoot
