import StringGeometry.RiemannSurfaces.Analytic.RiemannRoch

/-!
# Riemann-Roch Helper Lemmas

Infrastructure lemmas for the analytic Riemann-Roch theorem, including:
- Monotonicity of L(D) and h0(D) with respect to divisor ordering
- Point evaluation / inclusion maps
- Dimension bounds

## Key Results

* `linearSystem_inclusion` - Inclusion L(D') ↪ L(D) when D' ≤ D
* `linIndepLS_of_le` - Independence transfers across inclusions
* `h0_mono` - h0 is monotone: D' ≤ D → h0(D') ≤ h0(D)

## References

* Farkas, Kra "Riemann Surfaces" Ch III
* Forster "Lectures on Riemann Surfaces" §16
-/

namespace RiemannSurfaces.Analytic

open Divisor Classical

variable {RS : RiemannSurface}

/-!
## Divisor Coefficient Unfolding

Helper lemmas to make `linarith` work with divisor coefficients.
The add/neg operations on divisors are definitionally pointwise,
but `linarith` cannot see through the instance chain.
-/

/-- Coefficients of a sum of divisors add pointwise. -/
theorem coeff_add (D₁ D₂ : Divisor RS) (p : RS.carrier) :
    (D₁ + D₂).coeff p = D₁.coeff p + D₂.coeff p := rfl

/-- Coefficients of negated divisors negate pointwise. -/
theorem coeff_neg (D : Divisor RS) (p : RS.carrier) :
    (-D).coeff p = -(D.coeff p) := rfl

/-- Coefficients of divisorOf are the order function. -/
theorem coeff_divisorOf (f : AnalyticMeromorphicFunction RS) (p : RS.carrier) :
    (divisorOf f).coeff p = f.order p := rfl

/-!
## Divisor Ordering and Linear System Inclusion

If D' ≤ D (i.e., D'(p) ≤ D(p) for all p), then L(D') ⊆ L(D):
any meromorphic function with div(f) + D' ≥ 0 also satisfies div(f) + D ≥ 0.
-/

/-- The ordering D₁ ≤ D₂ means D₂ - D₁ is effective, i.e., D₂(p) ≥ D₁(p) for all p. -/
theorem divisor_le_iff (D₁ D₂ : Divisor RS) :
    D₁ ≤ D₂ ↔ ∀ p, D₁.coeff p ≤ D₂.coeff p := by
  constructor
  · intro h p
    -- h : Effective (D₂ + (-D₁)), i.e., ∀ q, 0 ≤ (D₂ + (-D₁)).coeff q
    have hp : 0 ≤ D₂.coeff p + -(D₁.coeff p) := by
      have := h p; rwa [coeff_add, coeff_neg] at this
    linarith
  · intro h p
    -- Goal: 0 ≤ (D₂ + (-D₁)).coeff p
    rw [coeff_add, coeff_neg]
    linarith [h p]

/-- If D' ≤ D, then any element of L(D') is also in L(D).
    The inclusion preserves the underlying meromorphic function. -/
def linearSystem_inclusion {D' D : Divisor RS} (hle : D' ≤ D) :
    LinearSystem RS D' → LinearSystem RS D := fun ls => by
  refine ⟨ls.fn, ?_, ls.holomorphicAway, ls.chartMeromorphic, ls.chartOrderAt_eq⟩
  intro p
  have h_eff : 0 ≤ ls.fn.order p + D'.coeff p := by
    have := ls.effective p; rwa [coeff_add, coeff_divisorOf] at this
  have h_le := (divisor_le_iff D' D).mp hle p
  show 0 ≤ (divisorOf ls.fn + D).coeff p
  rw [coeff_add, coeff_divisorOf]
  linarith

/-- The inclusion preserves the underlying function. -/
theorem linearSystem_inclusion_fn {D' D : Divisor RS} (hle : D' ≤ D)
    (ls : LinearSystem RS D') :
    (linearSystem_inclusion hle ls).fn = ls.fn := rfl

/-- Linear independence transfers through inclusion: if f₁,...,fₙ are
    LinIndepLS in L(D'), they are also LinIndepLS in L(D) for D' ≤ D.

    This holds because LinIndepLS only depends on the functions themselves,
    not on the divisor D. -/
theorem linIndepLS_of_le (CRS : CompactRiemannSurface)
    {D' D : Divisor CRS.toRiemannSurface} (hle : D' ≤ D) {n : ℕ}
    (basis' : Fin n → LinearSystem CRS.toRiemannSurface D')
    (hli : IsLinIndepLS CRS D' basis') :
    IsLinIndepLS CRS D (fun i => linearSystem_inclusion hle (basis' i)) := by
  intro c hzero i
  apply hli c _ i
  intro p hreg
  apply hzero p
  intro j
  rw [linearSystem_inclusion_fn]
  exact hreg j

/-- h0 is monotone: if D' ≤ D, then h0(D') ≤ h0(D).

    **Proof:** L(D') ⊆ L(D), and independence is preserved,
    so the maximum number of independent elements in L(D')
    is at most that in L(D). -/
theorem h0_mono (CRS : CompactRiemannSurface)
    {D' D : Divisor CRS.toRiemannSurface} (hle : D' ≤ D) :
    h0 CRS D' ≤ h0 CRS D := by
  by_contra hlt
  push_neg at hlt
  -- hlt : h0(D) < h0(D')
  -- Below the D-threshold for D', there exist enough independent elements in L(D')
  have h_fail : ∃ (basis : Fin (h0 CRS D + 1) → LinearSystem CRS.toRiemannSurface D'),
      IsLinIndepLS CRS D' basis := by
    by_contra h_succ
    have : h0 CRS D' ≤ h0 CRS D := Nat.find_le h_succ
    omega
  obtain ⟨basis', hli'⟩ := h_fail
  have hli_D := linIndepLS_of_le CRS hle basis' hli'
  exact h0_spec CRS D ⟨fun i => linearSystem_inclusion hle (basis' i), hli_D⟩

/-!
## Point Divisor and Subtraction

For the inductive step of Riemann-Roch, we need to relate
L(D) and L(D - [p]) for a point p.
-/

/-- Coefficient of a point divisor. -/
theorem coeff_point_self (p : RS.carrier) :
    (Divisor.point p).coeff p = 1 := by
  simp only [Divisor.point, ite_true]

/-- Coefficient of a point divisor at a different point. -/
theorem coeff_point_ne {p q : RS.carrier} (h : q ≠ p) :
    (Divisor.point p).coeff q = 0 := by
  simp only [Divisor.point]
  exact if_neg h

/-- D - [p] ≤ D: subtracting a point gives a smaller divisor. -/
theorem sub_point_le (D : Divisor RS) (p : RS.carrier) :
    D + (-(Divisor.point p)) ≤ D := by
  rw [divisor_le_iff]
  intro q
  rw [coeff_add, coeff_neg]
  by_cases hqp : q = p
  · subst hqp; rw [coeff_point_self]; omega
  · rw [coeff_point_ne hqp]; omega

/-- h0(D - [p]) ≤ h0(D) for any divisor D and point p.
    This is the "inclusion direction" of the point exact sequence. -/
theorem h0_sub_point_le (CRS : CompactRiemannSurface)
    (D : Divisor CRS.toRiemannSurface) (p : CRS.toRiemannSurface.carrier) :
    h0 CRS (D + (-(Divisor.point p))) ≤ h0 CRS D :=
  h0_mono CRS (sub_point_le D p)

/-- D ≤ D + [p]: adding a point gives a larger divisor. -/
theorem le_add_point (D : Divisor RS) (p : RS.carrier) :
    D ≤ D + Divisor.point p := by
  rw [divisor_le_iff]
  intro q
  rw [coeff_add]
  by_cases hqp : q = p
  · subst hqp; rw [coeff_point_self]; omega
  · rw [coeff_point_ne hqp]; omega

/-- h0(D) ≤ h0(D + [p]) for any divisor D and point p. -/
theorem h0_le_add_point (CRS : CompactRiemannSurface)
    (D : Divisor CRS.toRiemannSurface) (p : CRS.toRiemannSurface.carrier) :
    h0 CRS D ≤ h0 CRS (D + Divisor.point p) :=
  h0_mono CRS (le_add_point D p)

/-!
## Evaluation Map Infrastructure

The evaluation at a point p defines a map L(D) → ℂ (when D(p) ≥ 0).
The kernel is L(D - [p]).
-/

/-- At a point where D(p) = 0, elements of L(D) are regular (order ≥ 0). -/
theorem linearSystem_regular_at_zero_coeff
    {D : Divisor RS} (ls : LinearSystem RS D) {p : RS.carrier}
    (hp : D.coeff p = 0) : 0 ≤ ls.fn.order p := by
  have h : 0 ≤ ls.fn.order p + D.coeff p := by
    have := ls.effective p; rwa [coeff_add, coeff_divisorOf] at this
  linarith

/-- For elements of L(D) with D(p) = 0: regularValue at p is nonzero iff order = 0. -/
theorem regularValue_nonzero_iff_order_zero
    {D : Divisor RS} (ls : LinearSystem RS D) {p : RS.carrier}
    (hp : D.coeff p = 0) :
    ls.fn.regularValue p ≠ 0 ↔ ls.fn.order p = 0 := by
  constructor
  · intro hrv
    have hge := linearSystem_regular_at_zero_coeff ls hp
    by_contra hne
    push_neg at hne
    have hpos : 0 < ls.fn.order p := by omega
    exact hrv (AnalyticMeromorphicFunction.regularValue_at_zero hpos)
  · exact AnalyticMeromorphicFunction.regularValue_ne_zero_of_regular

/-- An element of L(D) with a zero at p (when D(p) = 0) is in L(D - [p]). -/
def linearSystem_vanishing_at {D : Divisor RS} (ls : LinearSystem RS D)
    {p : RS.carrier} (hp : D.coeff p = 0)
    (hvan : ls.fn.regularValue p = 0) :
    LinearSystem RS (D + (-(Divisor.point p))) := by
  refine ⟨ls.fn, ?_, ls.holomorphicAway, ls.chartMeromorphic, ls.chartOrderAt_eq⟩
  intro q
  rw [coeff_add, coeff_divisorOf, coeff_add, coeff_neg]
  by_cases hqp : q = p
  · rw [hqp, coeff_point_self]
    -- At p: need ls.fn.order p + D.coeff p - 1 ≥ 0
    -- D.coeff p = 0, so need ls.fn.order p ≥ 1
    have hge := linearSystem_regular_at_zero_coeff ls hp
    have hpos : 0 < ls.fn.order p := by
      rcases eq_or_lt_of_le hge with heq | hlt
      · exfalso
        exact (AnalyticMeromorphicFunction.regularValue_ne_zero_of_regular heq.symm) hvan
      · exact hlt
    rw [hp]; omega
  · rw [coeff_point_ne hqp, neg_zero, add_zero]
    have h : 0 ≤ ls.fn.order q + D.coeff q := by
      have := ls.effective q; rwa [coeff_add, coeff_divisorOf] at this
    linarith

/-- If all elements of a LinIndepLS family in L(D) vanish at a point p
    (where D(p) = 0), then they form a LinIndepLS family in L(D - [p]).

    This is because: (1) vanishing at p means they're in L(D - [p]),
    and (2) IsLinIndepLS only depends on the functions, not on D. -/
theorem linIndepLS_vanishing_at (CRS : CompactRiemannSurface)
    (D : Divisor CRS.toRiemannSurface) (p : CRS.toRiemannSurface.carrier)
    (hp : D.coeff p = 0) {n : ℕ}
    (basis : Fin n → LinearSystem CRS.toRiemannSurface D)
    (hli : IsLinIndepLS CRS D basis)
    (hvan : ∀ i, (basis i).fn.regularValue p = 0) :
    IsLinIndepLS CRS (D + (-(Divisor.point p)))
      (fun i => linearSystem_vanishing_at (basis i) hp (hvan i)) := by
  intro c hzero j
  apply hli c _ j
  intro q hreg
  apply hzero q
  intro i
  show (basis i).fn.order q ≥ 0
  exact hreg i

/-!
## Tightening: L(D+[p]) → L(D) when pole order allows

If f ∈ L(D+[p]) has order ≥ -D(p) at p (i.e., it doesn't use the extra
pole allowance at p), then f is already in L(D).
-/

/-- If f ∈ L(D+[p]) has order at p high enough to also be in L(D),
    we can construct f as an element of L(D). -/
def linearSystem_tighten {D : Divisor RS} {p : RS.carrier}
    (ls : LinearSystem RS (D + Divisor.point p))
    (hord : 0 ≤ ls.fn.order p + D.coeff p) :
    LinearSystem RS D := by
  refine ⟨ls.fn, ?_, ls.holomorphicAway, ls.chartMeromorphic, ls.chartOrderAt_eq⟩
  intro q
  show 0 ≤ (divisorOf ls.fn + D).coeff q
  by_cases hqp : q = p
  · subst hqp
    rw [coeff_add, coeff_divisorOf]
    exact hord
  · have h := ls.effective q
    simp only [coeff_add, coeff_divisorOf, coeff_point_ne hqp] at h ⊢
    linarith

/-- Tightening preserves the underlying function. -/
theorem linearSystem_tighten_fn {D : Divisor RS} {p : RS.carrier}
    (ls : LinearSystem RS (D + Divisor.point p))
    (hord : 0 ≤ ls.fn.order p + D.coeff p) :
    (linearSystem_tighten ls hord).fn = ls.fn := rfl

/-!
## Degree Lemmas for Point Operations
-/

/-- deg(D + [p]) = deg(D) + 1 -/
theorem degree_add_point (D : Divisor RS) (p : RS.carrier) :
    (D + Divisor.point p).degree = D.degree + 1 := by
  rw [Divisor.degree_add, Divisor.degree_point]

/-- deg(D - [p]) = deg(D) - 1 -/
theorem degree_sub_point (D : Divisor RS) (p : RS.carrier) :
    (D + -(Divisor.point p)).degree = D.degree - 1 := by
  rw [Divisor.degree_add, Divisor.degree_neg, Divisor.degree_point]; ring

end RiemannSurfaces.Analytic
