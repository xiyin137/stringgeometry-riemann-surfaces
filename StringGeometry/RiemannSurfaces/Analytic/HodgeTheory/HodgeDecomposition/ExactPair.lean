import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.HodgeDecomposition.DeRhamCore

/-!
# Exact-Pair Helper Lemmas

Reusable algebraic lemmas around `(∂f, ∂̄f)` pairs.
These are infrastructure for the common-potential bridge and de Rham reductions.
-/

namespace RiemannSurfaces.Analytic

open Complex Topology
open scoped Manifold

variable {RS : RiemannSurface}

/-- Negation compatibility for `∂̄` on `RealSmoothFunction`. -/
theorem dbar_real_hd_neg (f : RealSmoothFunction RS) :
    dbar_real_hd (-f) = -dbar_real_hd f := by
  calc
    dbar_real_hd (-f) = dbar_real_hd ((-1 : ℂ) • f) := by
      ext p
      simp
    _ = (-1 : ℂ) • dbar_real_hd f := dbar_real_hd_smul (RS := RS) (-1) f
    _ = -dbar_real_hd f := by simp

/-- Subtraction compatibility for `∂̄` on `RealSmoothFunction`. -/
theorem dbar_real_hd_sub (f g : RealSmoothFunction RS) :
    dbar_real_hd (f - g) = dbar_real_hd f - dbar_real_hd g := by
  calc
    dbar_real_hd (f - g) = dbar_real_hd (f + (-g)) := by
      rfl
    _ = dbar_real_hd f + dbar_real_hd (-g) := dbar_real_hd_add (RS := RS) f (-g)
    _ = dbar_real_hd f + (-dbar_real_hd g) := by rw [dbar_real_hd_neg (RS := RS)]
    _ = dbar_real_hd f - dbar_real_hd g := by
      simp [sub_eq_add_neg]

/-- Negation compatibility for `∂` on `RealSmoothFunction`. -/
theorem del_real_neg (f : RealSmoothFunction RS) :
    del_real (-f) = -del_real f := by
  calc
    del_real (-f) = del_real ((-1 : ℂ) • f) := by
      ext p
      simp
    _ = (-1 : ℂ) • del_real f := del_real_smul (RS := RS) (-1) f
    _ = -del_real f := by simp

/-- Subtraction compatibility for `∂` on `RealSmoothFunction`. -/
theorem del_real_sub (f g : RealSmoothFunction RS) :
    del_real (f - g) = del_real f - del_real g := by
  calc
    del_real (f - g) = del_real (f + (-g)) := by
      rfl
    _ = del_real f + del_real (-g) := del_real_add (RS := RS) f (-g)
    _ = del_real f + (-del_real g) := by rw [del_real_neg (RS := RS)]
    _ = del_real f - del_real g := by
      simp [sub_eq_add_neg]

/-- `∂(f-g)=0` iff `∂f = ∂g`. -/
theorem del_real_sub_eq_zero_iff (f g : RealSmoothFunction RS) :
    del_real (f - g) = 0 ↔ del_real f = del_real g := by
  constructor
  · intro hsub
    have hsub' : del_real f - del_real g = 0 := by
      simpa [del_real_sub (RS := RS)] using hsub
    exact sub_eq_zero.mp hsub'
  · intro heq
    have hsub' : del_real f - del_real g = 0 := sub_eq_zero.mpr heq
    simpa [del_real_sub (RS := RS)] using hsub'

/-- `∂̄(f-g)=0` iff `∂̄f = ∂̄g`. -/
theorem dbar_real_hd_sub_eq_zero_iff (f g : RealSmoothFunction RS) :
    dbar_real_hd (f - g) = 0 ↔ dbar_real_hd f = dbar_real_hd g := by
  constructor
  · intro hsub
    have hsub' : dbar_real_hd f - dbar_real_hd g = 0 := by
      simpa [dbar_real_hd_sub (RS := RS)] using hsub
    exact sub_eq_zero.mp hsub'
  · intro heq
    have hsub' : dbar_real_hd f - dbar_real_hd g = 0 := sub_eq_zero.mpr heq
    simpa [dbar_real_hd_sub (RS := RS)] using hsub'

/-- `∂̄(∂(f-g))` distributes over subtraction. -/
theorem dbar_10_del_real_sub (f g : RealSmoothFunction RS) :
    dbar_10 (del_real (f - g)) = dbar_10 (del_real f) - dbar_10 (del_real g) := by
  calc
    dbar_10 (del_real (f - g))
        = dbar_10 (del_real f - del_real g) := by rw [del_real_sub (RS := RS)]
    _ = dbar_10 (del_real f) + dbar_10 (-del_real g) := by
          simp [sub_eq_add_neg, dbar_10_add]
    _ = dbar_10 (del_real f) + -dbar_10 (del_real g) := by
          have hneg : dbar_10 (-del_real g) = -dbar_10 (del_real g) := by
            calc
              dbar_10 (-del_real g)
                  = dbar_10 ((-1 : ℂ) • del_real g) := by
                      congr
                      ext p
                      simp
              _ = (-1 : ℂ) • dbar_10 (del_real g) := dbar_10_smul (RS := RS) (-1) (del_real g)
              _ = -dbar_10 (del_real g) := by simp
          rw [hneg]
    _ = dbar_10 (del_real f) - dbar_10 (del_real g) := by
          simp [sub_eq_add_neg]

/-- `∂(∂̄(f-g))` distributes over subtraction. -/
theorem del_01_dbar_real_hd_sub (f g : RealSmoothFunction RS) :
    del_01 (dbar_real_hd (f - g)) = del_01 (dbar_real_hd f) - del_01 (dbar_real_hd g) := by
  calc
    del_01 (dbar_real_hd (f - g))
        = del_01 (dbar_real_hd f - dbar_real_hd g) := by rw [dbar_real_hd_sub (RS := RS)]
    _ = del_01 (dbar_real_hd f) + del_01 (-dbar_real_hd g) := by
          simp [sub_eq_add_neg, del_01_add]
    _ = del_01 (dbar_real_hd f) + -del_01 (dbar_real_hd g) := by
          have hneg : del_01 (-dbar_real_hd g) = -del_01 (dbar_real_hd g) := by
            calc
              del_01 (-dbar_real_hd g)
                  = del_01 ((-1 : ℂ) • dbar_real_hd g) := by
                      congr
                      ext p
                      simp
              _ = (-1 : ℂ) • del_01 (dbar_real_hd g) := del_01_smul (RS := RS) (-1) (dbar_real_hd g)
              _ = -del_01 (dbar_real_hd g) := by simp
          rw [hneg]
    _ = del_01 (dbar_real_hd f) - del_01 (dbar_real_hd g) := by
          simp [sub_eq_add_neg]

/-- Membership criterion for `closedForms1` in pair coordinates. -/
theorem mem_closedForms1_iff (ω10 : Form_10 RS) (ω01 : Form_01 RS) :
    ((ω10, ω01) : Form_10 RS × Form_01 RS) ∈ closedForms1 RS ↔
      dbar_10 ω10 + del_01 ω01 = 0 :=
  Iff.rfl

/-- Membership criterion for `exactForms1` in pair coordinates. -/
theorem mem_exactForms1_iff (ω10 : Form_10 RS) (ω01 : Form_01 RS) :
    ((ω10, ω01) : Form_10 RS × Form_01 RS) ∈ exactForms1 RS ↔
      ∃ f : RealSmoothFunction RS, ω10 = del_real f ∧ ω01 = dbar_real_hd f :=
  Iff.rfl

/-- Every potential gives an exact pair `(∂f, ∂̄f)`. -/
theorem exactForms1_pair_mem (f : RealSmoothFunction RS) :
    ((del_real f, dbar_real_hd f) : Form_10 RS × Form_01 RS) ∈ exactForms1 RS := by
  exact ⟨f, rfl, rfl⟩

/-- Common-potential reduction:
if the derivative pair of `f10 - f01` vanishes, then `f10` and `f01`
yield the same exact pair and one common potential exists. -/
theorem exactPair_commonPotential_of_sub_derivatives_zero
    (ω10 : Form_10 RS) (ω01 : Form_01 RS)
    (f10 f01 : RealSmoothFunction RS)
    (hω10 : ω10 = del_real f10)
    (hω01 : ω01 = dbar_real_hd f01)
    (hdelSub : del_real (f10 - f01) = 0)
    (hdbarSub : dbar_real_hd (f10 - f01) = 0) :
    ∃ f : RealSmoothFunction RS,
      ω10 = del_real f ∧ ω01 = dbar_real_hd f := by
  have hdelEq : del_real f10 = del_real f01 := by
    have hsub : del_real f10 - del_real f01 = 0 := by
      simpa [del_real_sub (RS := RS)] using hdelSub
    exact sub_eq_zero.mp hsub
  have hdbarEq : dbar_real_hd f10 = dbar_real_hd f01 := by
    have hsub : dbar_real_hd f10 - dbar_real_hd f01 = 0 := by
      simpa [dbar_real_hd_sub (RS := RS)] using hdbarSub
    exact sub_eq_zero.mp hsub
  refine ⟨f10, hω10, ?_⟩
  calc
    ω01 = dbar_real_hd f01 := hω01
    _ = dbar_real_hd f10 := hdbarEq.symm

/-- Common-potential reduction:
if `f10` and `f01` have matching `∂` and `∂̄` derivatives, then one
common potential gives both components. -/
theorem exactPair_commonPotential_of_equal_derivatives
    (ω10 : Form_10 RS) (ω01 : Form_01 RS)
    (f10 f01 : RealSmoothFunction RS)
    (hω10 : ω10 = del_real f10)
    (hω01 : ω01 = dbar_real_hd f01)
    (hdelEq : del_real f10 = del_real f01)
    (_hdbarEq : dbar_real_hd f10 = dbar_real_hd f01) :
    ∃ f : RealSmoothFunction RS,
      ω10 = del_real f ∧ ω01 = dbar_real_hd f := by
  refine ⟨f01, ?_, hω01⟩
  calc
    ω10 = del_real f10 := hω10
    _ = del_real f01 := hdelEq

/-- Rewrite the closedness condition in terms of primitive data. -/
theorem closed_exactPair_primitives_relation
    (ω10 : Form_10 RS) (ω01 : Form_01 RS)
    (f10 f01 : RealSmoothFunction RS)
    (hclosed : dbar_10 ω10 + del_01 ω01 = 0)
    (hω10 : ω10 = del_real f10)
    (hω01 : ω01 = dbar_real_hd f01) :
    dbar_10 (del_real f10) + del_01 (dbar_real_hd f01) = 0 := by
  simpa [hω10, hω01] using hclosed

/-- Primitive-data form of the closedness condition, solved for `dbar_10 (del_real f10)`. -/
theorem closed_exactPair_primitives_relation_eq_neg
    (ω10 : Form_10 RS) (ω01 : Form_01 RS)
    (f10 f01 : RealSmoothFunction RS)
    (hclosed : dbar_10 ω10 + del_01 ω01 = 0)
    (hω10 : ω10 = del_real f10)
    (hω01 : ω01 = dbar_real_hd f01) :
    dbar_10 (del_real f10) = -del_01 (dbar_real_hd f01) := by
  have hrel :
      dbar_10 (del_real f10) + del_01 (dbar_real_hd f01) = 0 :=
    closed_exactPair_primitives_relation (RS := RS) ω10 ω01 f10 f01 hclosed hω10 hω01
  simpa [eq_neg_iff_add_eq_zero] using hrel

/-- Common-potential bridge from two reusable analytic inputs:
1. mixed-derivative compatibility `dbar_10 (del_real f) + del_01 (dbar_real_hd f) = 0`,
2. exact-harmonic `(0,1)` vanishing.

This isolates the core reduction used by `closed_exactPair_commonPotential`. -/
theorem exactPair_commonPotential_of_closed_of_mixed_and_exact_harmonic01_vanishes
    (hvanish01 :
      ∀ f : RealSmoothFunction RS,
        (dbar_real_hd f).IsHarmonic →
          dbar_real_hd f = 0)
    (hmixed :
      ∀ f : RealSmoothFunction RS,
        dbar_10 (del_real f) + del_01 (dbar_real_hd f) = 0)
    (ω10 : Form_10 RS) (ω01 : Form_01 RS)
    (f10 f01 : RealSmoothFunction RS)
    (hclosed : dbar_10 ω10 + del_01 ω01 = 0)
    (hω10 : ω10 = del_real f10)
    (hω01 : ω01 = dbar_real_hd f01) :
    ∃ f : RealSmoothFunction RS,
      ω10 = del_real f ∧ ω01 = dbar_real_hd f := by
  have hprim :
      dbar_10 (del_real f10) = -del_01 (dbar_real_hd f01) :=
    closed_exactPair_primitives_relation_eq_neg (RS := RS)
      ω10 ω01 f10 f01 hclosed hω10 hω01
  have hmix10 :
      dbar_10 (del_real f10) = -del_01 (dbar_real_hd f10) := by
    have hmix10' :
        dbar_10 (del_real f10) + del_01 (dbar_real_hd f10) = 0 := hmixed f10
    simpa [eq_neg_iff_add_eq_zero] using hmix10'
  have hdel01_eq :
      del_01 (dbar_real_hd f10) = del_01 (dbar_real_hd f01) := by
    have hneg :
        -del_01 (dbar_real_hd f10) = -del_01 (dbar_real_hd f01) := by
      calc
        -del_01 (dbar_real_hd f10) = dbar_10 (del_real f10) := hmix10.symm
        _ = -del_01 (dbar_real_hd f01) := hprim
    exact neg_injective hneg
  have hdel01_sub_zero :
      del_01 (dbar_real_hd (f01 - f10)) = 0 := by
    have hsub :
        del_01 (dbar_real_hd (f01 - f10)) =
          del_01 (dbar_real_hd f01) - del_01 (dbar_real_hd f10) :=
      del_01_dbar_real_hd_sub (RS := RS) f01 f10
    rw [hsub, sub_eq_zero]
    exact hdel01_eq.symm
  have hharm :
      (dbar_real_hd (f01 - f10)).IsHarmonic :=
    isHarmonic01_of_del_01_eq_zero (RS := RS) hdel01_sub_zero
  have hdbar_sub_zero :
      dbar_real_hd (f01 - f10) = 0 :=
    hvanish01 (f01 - f10) hharm
  have hdbar_eq : dbar_real_hd f01 = dbar_real_hd f10 := by
    exact (dbar_real_hd_sub_eq_zero_iff (RS := RS) f01 f10).1 hdbar_sub_zero
  refine ⟨f10, hω10, ?_⟩
  calc
    ω01 = dbar_real_hd f01 := hω01
    _ = dbar_real_hd f10 := hdbar_eq

/-- Common-potential bridge from chart-local selector stabilization and
exact-harmonic `(0,1)` vanishing. -/
theorem exactPair_commonPotential_of_closed_of_chartAtLocallyConstant_and_exact_harmonic01_vanishes
    (hchart : Infrastructure.ChartAtLocallyConstant RS)
    (hvanish01 :
      ∀ f : RealSmoothFunction RS,
        (dbar_real_hd f).IsHarmonic →
          dbar_real_hd f = 0)
    (ω10 : Form_10 RS) (ω01 : Form_01 RS)
    (f10 f01 : RealSmoothFunction RS)
    (hclosed : dbar_10 ω10 + del_01 ω01 = 0)
    (hω10 : ω10 = del_real f10)
    (hω01 : ω01 = dbar_real_hd f01) :
    ∃ f : RealSmoothFunction RS,
      ω10 = del_real f ∧ ω01 = dbar_real_hd f := by
  refine exactPair_commonPotential_of_closed_of_mixed_and_exact_harmonic01_vanishes
    (RS := RS) hvanish01 ?_ ω10 ω01 f10 f01 hclosed hω10 hω01
  intro g
  exact dbar_10_del_real_add_del_01_dbar_real_hd_eq_zero_of_chartAtLocallyConstant
    (RS := RS) hchart g

end RiemannSurfaces.Analytic
