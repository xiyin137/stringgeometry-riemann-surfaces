import StringGeometry.RiemannSurfaces.GAGA.AlgebraicCurves.ZariskiTopology
import StringGeometry.RiemannSurfaces.GAGA.AlgebraicCurves.Core.Divisors
import StringGeometry.RiemannSurfaces.GAGA.AlgebraicCurves.FunctionField
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Cohomology on Algebraic Curves (Pure Algebraic Approach)

This file develops cohomology theory for algebraic curves using the Riemann-Roch space.

## Main Definitions

* `RiemannRochSpace` - The space L(D) = {f : (f) + D ≥ 0} ∪ {0}
* `RiemannRochSubmodule` - L(D) as a ℂ-submodule of K(C)

## Key Theorems (with sorrys to be proved)

* `h0_zero` - h⁰(O) = 1 (properness: regular functions on proper curves are constant)
* `h1_zero` - h¹(O) = g (algebraic definition of genus)
* `eulerChar_point_exact` - χ(D) - χ(D-p) = 1 (algebraic long exact sequence)
* `riemann_roch_algebraic` - χ(D) = deg(D) + 1 - g

## Proof Strategy (Purely Algebraic)

All theorems can be proved using purely algebraic methods:

1. **h⁰(O) = 1**: On a proper (complete) algebraic curve over an algebraically closed
   field, a rational function with no poles is regular everywhere, hence constant.
   This is the algebraic analogue of Liouville's theorem, proved via properness.

2. **h¹(O) = g**: Define genus algebraically as g := 1 - χ(O) = 1 - (h⁰(O) - h¹(O)).
   With h⁰(O) = 1, this gives h¹(O) = g by definition. Alternatively, use Serre duality
   h¹(O) = h⁰(K) and the fact that h⁰(K) = g for the canonical divisor.

3. **χ(D) - χ(D-p) = 1**: The short exact sequence of sheaves
   0 → O(D-p) → O(D) → k(p) → 0 induces a long exact sequence in algebraic
   sheaf cohomology. Since H⁰(k(p)) = k and H¹(k(p)) = 0 for a skyscraper sheaf,
   the alternating sum gives χ(D) - χ(D-p) = χ(k(p)) = 1.

## References

* Hartshorne "Algebraic Geometry" III.4, IV.1
* Silverman "The Arithmetic of Elliptic Curves" II.5
-/

namespace RiemannSurfaces.Algebraic.Cohomology

open Set Finset Classical

variable (C : AlgebraicCurve)

/-!
## The Riemann-Roch Space L(D)
-/

/-- The Riemann-Roch space L(D) as a set.
    L(D) = {f ∈ K(C) : f = 0 ∨ (f) + D ≥ 0}
    This is H⁰(C, O(D)). -/
def RiemannRochSpace (D : Core.Divisor C) : Set C.FunctionField :=
  { f | f = 0 ∨ (∀ p : C.Point, C.valuation p f + D.coeff p ≥ 0) }

/-- 0 is in L(D) -/
theorem zero_mem_RiemannRochSpace (D : Core.Divisor C) : (0 : C.FunctionField) ∈ RiemannRochSpace C D := by
  left; rfl

/-- L(D) is closed under addition -/
theorem add_mem_RiemannRochSpace (D : Core.Divisor C) {f g : C.FunctionField}
    (hf : f ∈ RiemannRochSpace C D) (hg : g ∈ RiemannRochSpace C D) :
    f + g ∈ RiemannRochSpace C D := by
  -- Handle cases based on whether f, g, or f+g is zero
  by_cases hf0 : f = 0
  · simp only [hf0, zero_add]; exact hg
  by_cases hg0 : g = 0
  · simp only [hg0, add_zero]; exact hf
  by_cases hfg : f + g = 0
  · left; exact hfg
  -- All nonzero: use ultrametric inequality
  · right
    intro p
    -- Extract the valuation bounds from hf and hg
    have hfv : C.valuation p f + D.coeff p ≥ 0 := by
      rcases hf with rfl | hf'; exact absurd rfl hf0; exact hf' p
    have hgv : C.valuation p g + D.coeff p ≥ 0 := by
      rcases hg with rfl | hg'; exact absurd rfl hg0; exact hg' p
    have hmin := C.valuation_add_min p f g hfg
    omega

/-- L(D) is closed under scalar multiplication (using field multiplication).
    Since K(C) is a ℂ-algebra, scalar multiplication c • f = (algebraMap ℂ K(C) c) * f. -/
theorem smul_mem_RiemannRochSpace [alg : FunctionFieldAlgebra C] (D : Core.Divisor C)
    {f : C.FunctionField} {c : ℂ} (hf : f ∈ RiemannRochSpace C D) :
    c • f ∈ RiemannRochSpace C D := by
  -- v(c • f) = v(algebraMap c * f) = v(algebraMap c) + v(f) = 0 + v(f) = v(f) for c ≠ 0
  -- For c = 0, c • f = 0 ∈ L(D)
  by_cases hc : c = 0
  · simp only [hc, zero_smul]; left; rfl
  by_cases hf0 : f = 0
  · simp only [hf0, smul_zero]; left; rfl
  -- Both c and f nonzero
  right
  intro p
  -- Extract the valuation bound from hf
  have hfv : C.valuation p f + D.coeff p ≥ 0 := by
    rcases hf with rfl | hf'; exact absurd rfl hf0; exact hf' p
  -- c • f = algebraMap c * f
  have hsmul : c • f = algebraMap ℂ C.FunctionField c * f := Algebra.smul_def c f
  rw [hsmul]
  have hcnz : algebraMap ℂ C.FunctionField c ≠ 0 := by
    intro heq
    simp only [map_eq_zero] at heq
    exact hc heq
  rw [C.valuation_mul p _ _ hcnz hf0, alg.valuation_algebraMap p c hc]
  simp only [zero_add]
  exact hfv

/-!
## L(D-p) ⊆ L(D): The Key Inclusion

For the point exact sequence, we need that L(D-p) is a subspace of L(D).
This follows from the fact that the condition for L(D-p) is stronger at p.
-/

/-- L(D - point(p)) ⊆ L(D).

    **Proof**: For f ∈ L(D-p):
    - At q ≠ p: condition v_q(f) ≥ -D(q) is the same since (D-p)(q) = D(q)
    - At q = p: f satisfies v_p(f) ≥ -(D(p)-1) = -D(p)+1 > -D(p)

    So L(D-p) ⊆ L(D). -/
theorem RiemannRochSpace_sub_point_subset (D : Core.Divisor C) (p : C.Point) :
    RiemannRochSpace C (D - Core.Divisor.point p) ⊆ RiemannRochSpace C D := by
  intro f hf
  simp only [RiemannRochSpace, Set.mem_setOf_eq] at hf ⊢
  rcases hf with rfl | hf_val
  · left; rfl
  · right
    intro q
    specialize hf_val q
    simp only [Core.Divisor.sub_coeff, Core.Divisor.point] at hf_val ⊢
    by_cases hqp : q = p
    · subst hqp
      simp only [if_true] at hf_val ⊢
      omega
    · simp only [if_neg hqp] at hf_val ⊢
      omega

/-- The canonical divisor K on an algebraic curve.

    This is just a divisor claimed to be canonical (div(ω) for some meromorphic 1-form ω).
    The degree property deg(K) = 2g - 2 must be proved via Riemann-Hurwitz (see
    `canonical_divisor_degree_algebraic`), NOT assumed as a structure field.

    Similarly, h⁰(K) = g must be proved (see `h0_canonical_eq_genus`), not assumed.

    **Note on the Residue Theorem:** The property L(K + point(p)) = L(K) for all p
    is a THEOREM (the residue theorem: no 1-form has exactly one simple pole), not
    a defining property. It should NOT be bundled here - see `NoExtraPole` in
    ResidueTheory.lean for the explicit hypothesis when needed. -/
structure CanonicalDivisor (C : Algebraic.CompactAlgebraicCurve) where
  K : Core.Divisor C.toAlgebraicCurve

/-- Riemann-Hurwitz theorem (algebraic): deg(K) = 2g - 2 for the canonical divisor.

    **Proof approaches:**
    1. Kähler differentials: K = div(Ω¹_{C/k}), compute degree via local generators
    2. Branched covering: Consider π : C → P¹ and use Riemann-Hurwitz ramification formula
    3. Algebraic Euler characteristic: χ(C) = 2 - 2g and deg(K) = -χ(C)

    This requires substantial infrastructure not yet available. -/
theorem canonical_divisor_degree_algebraic (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C) :
    K.K.degree = (2 : ℤ) * C.genus - 2 := by
  sorry

/-!
## Cohomology Dimensions

h⁰(D) and h¹(D) are defined as dimensions of concrete vector spaces.
The finite-dimensionality theorems have sorrys - these are the actual
mathematical content that needs to be proved.
-/

/-- The FunctionFieldAlgebra instance for a CompactAlgebraicCurve -/
instance CompactAlgebraicCurve.functionFieldAlgebraInst (C : Algebraic.CompactAlgebraicCurve) :
    FunctionFieldAlgebra C.toAlgebraicCurve := C.algebraInst

/-- The Module instance on the function field from the algebra structure -/
instance CompactAlgebraicCurve.functionFieldModule (C : Algebraic.CompactAlgebraicCurve) :
    Module ℂ C.FunctionField := C.algebraInst.algebraInst.toModule

/-- L(D) as a submodule of the function field K(C).
    This uses the ℂ-algebra structure from CompactAlgebraicCurve. -/
noncomputable def RiemannRochSubmodule (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) : Submodule ℂ C.FunctionField where
  carrier := RiemannRochSpace C.toAlgebraicCurve D
  add_mem' := fun {_ _} ha hb => add_mem_RiemannRochSpace C.toAlgebraicCurve D ha hb
  zero_mem' := zero_mem_RiemannRochSpace C.toAlgebraicCurve D
  smul_mem' := fun _ {_} hf => smul_mem_RiemannRochSpace C.toAlgebraicCurve D hf

/-- The underlying type of `L(D)` (elements of the Riemann-Roch submodule). -/
abbrev RiemannRochSubmoduleType (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) : Type _ :=
  ↥(RiemannRochSubmodule C D)

noncomputable instance RiemannRochSubmoduleType.addCommGroup (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) :
    AddCommGroup (RiemannRochSubmoduleType C D) :=
  (RiemannRochSubmodule C D).addCommGroup

noncomputable instance RiemannRochSubmoduleType.module (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) :
    Module ℂ (RiemannRochSubmoduleType C D) :=
  (RiemannRochSubmodule C D).module

/-- Finite-dimensionality of `L(D)` with an explicit module structure argument.

This avoids fragile typeclass inference through coercions of nontrivial submodule terms. -/
abbrev RiemannRochSubmoduleFiniteDimensional (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) : Prop :=
  @FiniteDimensional ℂ (RiemannRochSubmoduleType C D)
    inferInstance inferInstance (RiemannRochSubmodule C D).module

/-- `finrank` of `L(D)` with explicit module instance. -/
noncomputable abbrev RiemannRochSubmoduleFinrank (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) : ℕ :=
  @Module.finrank ℂ (RiemannRochSubmoduleType C D)
    inferInstance inferInstance (RiemannRochSubmodule C D).module

/-- **Key lemma for finiteness**: If L(D-p) is finite-dimensional, then L(D) is finite-dimensional.

    The proof uses leading coefficient uniqueness to show that L(D) is spanned by
    L(D-p) together with at most one additional element.

    This does NOT assume L(D) is finite-dimensional upfront. -/
theorem RiemannRochSubmodule_finiteDimensional_step (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point)
    (hFD : RiemannRochSubmoduleFiniteDimensional C (D - Core.Divisor.point p)) :
    RiemannRochSubmoduleFiniteDimensional C D := by
  sorry

/-- L(D) is finite-dimensional (finiteness for coherent sheaves on proper curves).

    **Algebraic proof outline:**
    1. O(D) is a coherent sheaf on a proper curve C
    2. Global sections of coherent sheaves on proper schemes are finite-dimensional
    3. L(D) = H⁰(C, O(D)) is therefore finite-dimensional over the base field

    This is the algebraic version of "Cartan-Serre finiteness" - it follows from
    coherence + properness, not from analytic arguments. -/
theorem RiemannRochSubmodule_finiteDimensional (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) :
    RiemannRochSubmoduleFiniteDimensional C D := by
  sorry

/-- L(D-p) as a submodule of L(D).
    This is the submodule inclusion used in the point exact sequence. -/
noncomputable def RiemannRochSubmodule_sub_point (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) :
    Submodule ℂ ↥(RiemannRochSubmodule C D) :=
  Submodule.comap (RiemannRochSubmodule C D).subtype (RiemannRochSubmodule C (D - Core.Divisor.point p))

/-- The inclusion L(D-p) → L(D) is well-defined. -/
theorem RiemannRochSubmodule_sub_point_le (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) :
    RiemannRochSubmodule C (D - Core.Divisor.point p) ≤ RiemannRochSubmodule C D := by
  intro f hf
  exact RiemannRochSpace_sub_point_subset C.toAlgebraicCurve D p hf

/-- **Quotient dimension bound**: dim(L(D)/L(D-p)) ≤ 1.

    **Proof sketch**:
    The quotient is parametrized by the "leading coefficient" at p.
    If f, g ∈ L(D) have v_p(f) = v_p(g) = -D(p), then f - cg ∈ L(D-p) for suitable c.
    So the quotient embeds into ℂ (the space of leading coefficients).

    This uses `leadingCoefficientUniqueness` from CompactAlgebraicCurve:
    any two functions with the same pole order at p are proportional modulo
    functions with higher valuation. -/
theorem quotient_dim_le_one (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point)
    [RiemannRochSubmoduleFiniteDimensional C D]
    [RiemannRochSubmoduleFiniteDimensional C (D - Core.Divisor.point p)] :
    RiemannRochSubmoduleFinrank C D ≤
    RiemannRochSubmoduleFinrank C (D - Core.Divisor.point p) + 1 := by
  sorry

/-!
## Evaluation Map at a Point

The evaluation map L(D) → ℂ extracts the "leading coefficient" at a point p.
This is the key map for the short exact sequence 0 → L(D-p) → L(D) → ℂ.

The kernel of this map is precisely L(D-p), and the image is either 0 or ℂ
depending on whether there exists a function in L(D) with exact pole order D(p) at p.
-/

/-!
### Point Exact Formula Proof Approach

**Key lemma for point exact formula**: The sum of quotient dimensions equals 1.

This is the algebraic content of the long exact sequence:
  0 → L(D-p) → L(D) → ℂ → H¹(D-p) → H¹(D) → 0

The alternating sum of dimensions is 0, which gives:
  dim L(D-p) - dim L(D) + 1 - dim H¹(D-p) + dim H¹(D) = 0

Using Serre duality h¹(E) = h⁰(K-E):
  (dim L(D) - dim L(D-p)) + (dim L(K-D+p) - dim L(K-D)) = 1

**Proof approach:**
The formula follows from the snake lemma applied to the short exact sequence
of sheaves 0 → O(D-p) → O(D) → ℂ_p → 0, where:
- The inclusion L(D-p) → L(D) has kernel 0 (injective)
- The evaluation map L(D) → ℂ has kernel L(D-p)
- The connecting map ℂ → H¹(D-p) is defined via residue pairing
- H¹(ℂ_p) = 0 (skyscraper is acyclic)

The key input is that χ(ℂ_p) = h⁰(ℂ_p) - h¹(ℂ_p) = 1 - 0 = 1.

**Infrastructure needed:**
1. Snake lemma for the short exact sequence of Čech complexes
2. Connecting homomorphism construction
3. Verification of exactness at each step
4. Skyscraper acyclicity (H¹(ℂ_p) = 0)

All of these are provable from the existing axioms of CompactAlgebraicCurve
using the local parameter and DVR structure. The proof is deferred pending
development of this infrastructure.
-/

/-- h⁰(D) = dim L(D).
    Properly defined as finrank of the Riemann-Roch submodule.
    If not finite-dimensional, finrank returns 0 by convention. -/
noncomputable def h0 (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) : ℕ :=
  RiemannRochSubmoduleFinrank C D

/-- h⁰(K) = g: The dimension of holomorphic 1-forms equals genus.

    This is a deep theorem connecting:
    - Algebraic h⁰(K) = dim L(K) (dimension of space of meromorphic functions with poles ≤ K)
    - Topological genus g (from CompactAlgebraicCurve structure)

    **Proof approaches:**
    1. Hodge theory: H⁰(K) ≅ H⁰'¹(Σ) has dimension = g
    2. Algebraic: Construct K from Kähler differentials, count dimensions using
       regularity of differentials on smooth curves
    3. GAGA: Analytic h⁰(K) = g transfers to algebraic via comparison theorem

    This requires substantial infrastructure not yet available. -/
theorem h0_canonical_eq_genus (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C) :
    h0 C K.K = C.genus := by
  sorry

/-- h¹(D) = dim H¹(C, O(D)).
    Defined via Serre duality: h¹(D) = h⁰(K - D) where K is the canonical divisor.

    **Mathematical note**: The canonical divisor K is unique up to linear equivalence
    and has degree 2g - 2. The Serre duality theorem states h¹(D) = h⁰(K - D).

    This definition takes the canonical divisor K as an explicit parameter.
    The value is independent of the choice of K (up to linear equivalence). -/
noncomputable def h1 (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C) (D : Core.Divisor C.toAlgebraicCurve) : ℕ :=
  -- Use Serre duality: h¹(D) = h⁰(K - D)
  h0 C (K.K - D)

/-- Euler characteristic χ(D) = h⁰(D) - h¹(D).
    Takes the canonical divisor K as a parameter (needed for h¹ via Serre duality). -/
noncomputable def eulerChar (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C) (D : Core.Divisor C.toAlgebraicCurve) : ℤ :=
  (h0 C D : ℤ) - (h1 C K D : ℤ)

/-- **Arithmetic genus** g_a = h¹(O) = h⁰(K) (by Serre duality definition).

    The arithmetic genus is defined purely algebraically as the dimension of the
    space of holomorphic 1-forms H⁰(K). By Serre duality (h¹(D) = h⁰(K-D)),
    we have h¹(O) = h¹(0) = h⁰(K-0) = h⁰(K), so this equals h¹(O).

    **Key insight**: This definition allows the base case χ(0) = 1 - g_a to be
    proved trivially, since:
    - χ(0) = h⁰(0) - h¹(0) = 1 - h⁰(K) = 1 - arithmeticGenus

    The bridge between arithmetic genus and topological genus requires Hodge
    theory (g_a = g_top for smooth curves over ℂ) and is deferred. -/
noncomputable def arithmeticGenus (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C) : ℕ :=
  h0 C K.K

/-!
## Key Lemmas for Riemann-Roch

These theorems have sorrys - they represent the actual mathematical
work that needs to be done.
-/

/-- **h⁰(O) = 1**: Only constant functions have no poles.

    **Algebraic proof**:
    1. L(0) = {f ∈ K(C) : (f) ≥ 0} = {f : f has no poles}
    2. A rational function with no poles on a proper curve is regular everywhere
    3. On a proper (complete) variety over an algebraically closed field,
       a regular function is constant (this is properness, not maximum principle!)
    4. Therefore L(0) = k = ℂ, so h⁰(O) = dim L(0) = 1

    **Key point**: This uses PROPERNESS of algebraic curves, not analytic arguments. -/
theorem h0_zero (C : Algebraic.CompactAlgebraicCurve) : h0 C 0 = 1 := by
  letI : Module ℂ ↥(RiemannRochSubmodule C 0) := (RiemannRochSubmodule C 0).module
  -- h0 C 0 = finrank ℂ (RiemannRochSubmodule C 0)
  -- RiemannRochSubmodule C 0 = L(0) = {f : v_p(f) ≥ 0 for all p} ∪ {0}
  -- By regularIsConstant, this is exactly the image of ℂ under algebraMap
  unfold h0
  -- We need to show finrank ℂ (RiemannRochSubmodule C 0) = 1
  -- This follows from L(0) being isomorphic to ℂ as a ℂ-module

  -- Step 1: L(0) ⊆ constants
  have h_const : ∀ f ∈ RiemannRochSubmodule C 0, ∃ c : ℂ, f = algebraMap ℂ C.FunctionField c := by
    intro f hf
    simp only [RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
               RiemannRochSpace] at hf
    rcases hf with rfl | hf_val
    · use 0; simp only [map_zero]
    · have hf_reg : ∀ p, 0 ≤ C.valuation p f := by
        intro p; have := hf_val p; simp only [Core.Divisor.zero_coeff, add_zero] at this; exact this
      exact Algebraic.CompactAlgebraicCurve.regularIsConstant C f hf_reg

  -- Step 2: Constants ⊆ L(0)
  have h_const_mem : ∀ c : ℂ, algebraMap ℂ C.FunctionField c ∈ RiemannRochSubmodule C 0 := by
    intro c
    simp only [RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
               RiemannRochSpace]
    by_cases hc : c = 0
    · left; simp only [hc, map_zero]
    · right
      intro p
      simp only [Core.Divisor.zero_coeff, add_zero]
      exact le_of_eq (C.algebraInst.valuation_algebraMap p c hc).symm

  -- Step 3: Construct a linear equivalence L(0) ≃ₗ[ℂ] ℂ
  -- The map ℂ → L(0) given by c ↦ algebraMap c is surjective (by h_const)
  -- and injective (algebraMap is injective for field extensions)

  -- Define the linear map ℂ → L(0)
  let toL0 : ℂ →ₗ[ℂ] ↥(RiemannRochSubmodule C 0) := {
    toFun := fun c => ⟨algebraMap ℂ C.FunctionField c, h_const_mem c⟩
    map_add' := by
      intros x y
      apply Subtype.ext
      simp only [AddMemClass.mk_add_mk, map_add]
    map_smul' := by
      intros m x
      apply Subtype.ext
      simp only [RingHom.id_apply, SetLike.val_smul, Algebra.smul_def, map_mul,
                 Algebra.algebraMap_self]
  }

  -- toL0 is surjective
  have h_surj : Function.Surjective toL0 := by
    intro ⟨f, hf⟩
    obtain ⟨c, hc⟩ := h_const f hf
    use c
    apply Subtype.ext
    exact hc.symm

  -- toL0 is injective (algebraMap is injective)
  have h_inj : Function.Injective toL0 := by
    intro c₁ c₂ heq
    have : (toL0 c₁).val = (toL0 c₂).val := congrArg Subtype.val heq
    exact (algebraMap ℂ C.FunctionField).injective this

  -- toL0 is a linear equivalence
  let equiv : ℂ ≃ₗ[ℂ] ↥(RiemannRochSubmodule C 0) :=
    LinearEquiv.ofBijective toL0 ⟨h_inj, h_surj⟩

  -- finrank is preserved by linear equivalence
  unfold RiemannRochSubmoduleFinrank
  rw [← LinearEquiv.finrank_eq equiv]
  -- finrank ℂ ℂ = 1
  exact Module.finrank_self ℂ

/-- **h¹(O) = g**: First cohomology dimension equals genus.

    **Algebraic definition of genus**: The genus g of an algebraic curve is defined as
    g := dim H¹(C, O_C) = h¹(O). This is the DEFINITION of genus in algebraic geometry.

    **Consistency check**: This agrees with the topological genus via:
    - Algebraic: g = h¹(O) = h⁰(K) (by Serre duality)
    - Topological: g = (first Betti number) / 2
    - GAGA theorem shows these coincide for complex algebraic curves

    **For the pure algebraic path**: If genus is defined topologically in
    `CompactAlgebraicCurve`, we need GAGA or the comparison theorem.
    If genus is defined as h¹(O), this theorem is definitional.

    **Current status**: Uses `C.genus` from CompactAlgebraicCurve structure.
    This requires `h0_canonical_eq_genus` theorem (currently with sorry). -/
theorem h1_zero (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C) : h1 C K 0 = C.genus := by
  -- h1 C K 0 = h0 C (K.K - 0) = h0 C K.K = C.genus
  unfold h1
  -- K.K - 0 = K.K
  have hK0 : K.K - 0 = K.K := sub_zero _
  rw [hK0]
  exact h0_canonical_eq_genus C K

/-- **Alternating sum lemma for exact sequences**.

    For a six-term exact sequence of finite-dimensional vector spaces:
      0 → V₁ → V₂ → V₃ → V₄ → V₅ → V₆ → 0
    we have: dim V₁ - dim V₂ + dim V₃ - dim V₄ + dim V₅ - dim V₆ = 0

    This is a standard result in homological algebra (Euler-Poincaré principle). -/
theorem exact_sequence_alternating_sum
    (V₁ V₂ V₃ V₄ V₅ V₆ : Type*) [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃]
    [AddCommGroup V₄] [AddCommGroup V₅] [AddCommGroup V₆]
    [Module ℂ V₁] [Module ℂ V₂] [Module ℂ V₃] [Module ℂ V₄] [Module ℂ V₅] [Module ℂ V₆]
    [FiniteDimensional ℂ V₁] [FiniteDimensional ℂ V₂] [FiniteDimensional ℂ V₃]
    [FiniteDimensional ℂ V₄] [FiniteDimensional ℂ V₅] [FiniteDimensional ℂ V₆]
    (f₁ : V₁ →ₗ[ℂ] V₂) (f₂ : V₂ →ₗ[ℂ] V₃) (f₃ : V₃ →ₗ[ℂ] V₄)
    (f₄ : V₄ →ₗ[ℂ] V₅) (f₅ : V₅ →ₗ[ℂ] V₆)
    (hinj : Function.Injective f₁) (hsurj : Function.Surjective f₅)
    (hex₂ : LinearMap.ker f₂ = LinearMap.range f₁)
    (hex₃ : LinearMap.ker f₃ = LinearMap.range f₂)
    (hex₄ : LinearMap.ker f₄ = LinearMap.range f₃)
    (hex₅ : LinearMap.ker f₅ = LinearMap.range f₄) :
    (Module.finrank ℂ V₁ : ℤ) - Module.finrank ℂ V₂ + Module.finrank ℂ V₃ -
    Module.finrank ℂ V₄ + Module.finrank ℂ V₅ - Module.finrank ℂ V₆ = 0 := by
  -- Rank-nullity: finrank V = finrank (ker f) + finrank (range f)
  -- By exactness:
  --   ker f₂ = range f₁ ≅ V₁ (since f₁ is injective)
  --   ker f₃ = range f₂
  --   ker f₄ = range f₃
  --   ker f₅ = range f₄
  --   range f₅ = V₆ (since f₅ is surjective)

  -- Let a = finrank V₁, b = finrank (range f₂), c = finrank (range f₃),
  -- d = finrank (range f₄), e = finrank V₆

  -- By rank-nullity:
  --   finrank V₂ = finrank (ker f₂) + finrank (range f₂) = a + b
  --   finrank V₃ = finrank (ker f₃) + finrank (range f₃) = b + c
  --   finrank V₄ = finrank (ker f₄) + finrank (range f₄) = c + d
  --   finrank V₅ = finrank (ker f₅) + finrank (range f₅) = d + e

  -- Alternating sum: a - (a+b) + (b+c) - (c+d) + (d+e) - e = 0

  -- Rank-nullity lemmas
  have rn₂ := Submodule.finrank_quotient_add_finrank (LinearMap.ker f₂)
  have rn₃ := Submodule.finrank_quotient_add_finrank (LinearMap.ker f₃)
  have rn₄ := Submodule.finrank_quotient_add_finrank (LinearMap.ker f₄)
  have rn₅ := Submodule.finrank_quotient_add_finrank (LinearMap.ker f₅)

  -- Convert quotient dimensions to range dimensions using quotKerEquivRange
  rw [LinearEquiv.finrank_eq f₂.quotKerEquivRange] at rn₂
  rw [LinearEquiv.finrank_eq f₃.quotKerEquivRange] at rn₃
  rw [LinearEquiv.finrank_eq f₄.quotKerEquivRange] at rn₄
  rw [LinearEquiv.finrank_eq f₅.quotKerEquivRange] at rn₅

  -- Exactness: ker = range of previous map
  have hk₂ : Module.finrank ℂ (LinearMap.ker f₂) = Module.finrank ℂ V₁ := by
    rw [hex₂]
    -- range f₁ ≅ V₁ since f₁ is injective, so V₁/ker(f₁) ≅ range(f₁) and ker(f₁) = 0
    rw [LinearEquiv.finrank_eq (LinearEquiv.ofInjective f₁ hinj)]
  have hk₃ : Module.finrank ℂ (LinearMap.ker f₃) = Module.finrank ℂ (LinearMap.range f₂) := by
    rw [hex₃]
  have hk₄ : Module.finrank ℂ (LinearMap.ker f₄) = Module.finrank ℂ (LinearMap.range f₃) := by
    rw [hex₄]
  have hk₅ : Module.finrank ℂ (LinearMap.ker f₅) = Module.finrank ℂ (LinearMap.range f₄) := by
    rw [hex₅]
  have hr₅ : Module.finrank ℂ (LinearMap.range f₅) = Module.finrank ℂ V₆ := by
    rw [LinearMap.range_eq_top.mpr hsurj]
    exact finrank_top ℂ V₆

  -- Now the algebra
  omega

/-- L(D-p) as a subspace of L(D) via inclusion -/
noncomputable def RiemannRochSpace_sub_point_subset_submodule (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) :
    RiemannRochSubmodule C (D - Core.Divisor.point p) ≤ RiemannRochSubmodule C D := by
  intro x hx; exact RiemannRochSpace_sub_point_subset C.toAlgebraicCurve D p hx

/-- L(K-D) as a subspace of L(K-D+p) via inclusion -/
noncomputable def RiemannRochSpace_KD_subset (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) :
    RiemannRochSubmodule C (K.K - D) ≤ RiemannRochSubmodule C (K.K - D + Core.Divisor.point p) := by
  intro x hx
  simp only [RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk, RiemannRochSpace] at hx ⊢
  rcases hx with rfl | hx
  · left; rfl
  · right; intro q
    simp only [Core.Divisor.add_coeff, Core.Divisor.point]
    by_cases hqp : q = p
    · simp only [hqp, if_true]
      have hp := hx p
      linarith
    · simp only [if_neg hqp, add_zero]
      exact hx q

end RiemannSurfaces.Algebraic.Cohomology
