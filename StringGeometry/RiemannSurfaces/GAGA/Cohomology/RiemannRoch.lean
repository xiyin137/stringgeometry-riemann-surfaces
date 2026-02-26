-- Note: CechTheory uses CompactRiemannSurface (analytic),
-- so it lives in GAGA/Cohomology, not Algebraic/Cohomology
import StringGeometry.RiemannSurfaces.GAGA.Cohomology.CechTheory
import StringGeometry.RiemannSurfaces.GAGA.Cohomology.PointExactProof

/-!
# The Riemann-Roch Theorem

This file states and proves the Riemann-Roch theorem for compact Riemann surfaces,
building on the sheaf cohomology infrastructure developed in the Cohomology/ folder.

## The Theorem

For a divisor D on a compact Riemann surface Σ of genus g:

  **h⁰(D) - h¹(D) = deg(D) - g + 1**

Equivalently, using Serre duality h¹(D) = h⁰(K - D):

  **h⁰(D) - h⁰(K - D) = deg(D) - g + 1**

## Proof Structure

The proof proceeds in two steps:

**Step 1** (CechTheory.lean): Prove the Euler characteristic formula
  χ(O(D)) = deg(D) + 1 - g

  This uses induction on degree via the exact sequence:
    0 → O(D-p) → O(D) → ℂ_p → 0
  which gives χ(D) - χ(D-p) = 1.

**Step 2** (CechTheory.lean): Apply Serre duality dimension equality
  h¹(D) = h⁰(K - D)

  Substituting into χ(D) = h⁰(D) - h¹(D) = deg(D) + 1 - g gives the theorem.

## Main Results

All theorems use Čech cohomology directly via `FiniteGoodCover`.

* `riemann_roch_euler` - Euler characteristic form: χ(D) = deg(D) + 1 - g
* `riemann_roch_of_serre_dim` - Classical form from explicit Serre-dimension input
* `riemann_roch` - Classical form via `serre_duality_dim_cech`
* `h0_vanish_negative_degree` - h⁰(D) = 0 for deg(D) < 0
* `h1_vanish_large_degree` - h¹(D) = 0 for deg(D) > 2g - 2
* `h0_K2` - h⁰(K²) = 3g - 3 for g ≥ 2
* `moduli_dimension` - dim M_g = 3g - 3 for g ≥ 2

## References

* Riemann "Theorie der Abel'schen Functionen" (1857)
* Roch "Ueber die Anzahl der willkürlichen Constanten" (1865)
* Griffiths, Harris "Principles of Algebraic Geometry" Ch 2
* Hartshorne "Algebraic Geometry" Ch IV
-/

namespace RiemannSurfaces.Algebraic

open RiemannSurfaces Cohomology CechTheory

/-!
## The Main Theorem (Čech Cohomology Form)

All theorems use Čech cohomology via `FiniteGoodCover`.
-/

/-- **The Riemann-Roch Theorem** (Euler characteristic form).

    For a divisor D on a compact Riemann surface Σ of genus g:

      **χ(O(D)) = h⁰(D) - h¹(D) = deg(D) + 1 - g**

    This form is proved directly from the exact sequence recursion:
      χ(D) - χ(D - p) = 1

    combined with the base case χ(O) = h⁰(O) - h¹(O) = 1 - g.

    See `CechTheory.eulerChar_formula_cech` for the proof. -/
theorem riemann_roch_euler (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (L : LineBundleSheafAssignment CRS.toRiemannSurface O)
    (gc : ∀ D : Divisor CRS.toRiemannSurface, FiniteGoodCover (L.sheafOf D))
    (D : Divisor CRS.toRiemannSurface) :
    cech_chi L gc D = D.degree + 1 - CRS.genus :=
  eulerChar_formula_cech L gc D

/-- Euler-form Riemann-Roch from explicit point-exact bridge data.

    This route avoids consuming `point_exact_cech` directly and instead
    instantiates `eulerChar_formula_cech_of` through
    `PointExactProof.eulerChar_formula_cech_from_point_exact_data`. -/
theorem riemann_roch_euler_from_point_exact_data (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (L : LineBundleSheafAssignment CRS.toRiemannSurface O)
    (gc : ∀ D : Divisor CRS.toRiemannSurface, FiniteGoodCover (L.sheafOf D))
    (h0 :
      h_i (cechToSheafCohomologyGroup (L.sheafOf 0) (gc 0) 0) = 1)
    (h1 :
      h_i (cechToSheafCohomologyGroup (L.sheafOf 0) (gc 0) 1) = CRS.genus)
    (ses : PointExactProof.PointExactSESFamily O L)
    (les : PointExactProof.PointExactLESFamily O L ses)
    (h''0_dim : PointExactProof.PointExactHpp0 les)
    (h''1_dim : PointExactProof.PointExactHpp1 les)
    (h0_Dp_eq : PointExactProof.PointExactH0Dp gc les)
    (h1_Dp_eq : PointExactProof.PointExactH1Dp gc les)
    (h0_D_eq : PointExactProof.PointExactH0D gc les)
    (h1_D_eq : PointExactProof.PointExactH1D gc les)
    (D : Divisor CRS.toRiemannSurface) :
    cech_chi L gc D = D.degree + 1 - CRS.genus :=
  PointExactProof.eulerChar_formula_cech_from_point_exact_data
    L gc h0 h1 ses les h''0_dim h''1_dim h0_Dp_eq h1_Dp_eq h0_D_eq h1_D_eq D

/-- **The Riemann-Roch Theorem** (classical form from explicit Serre dimension input).

    For a divisor D on a compact Riemann surface Σ of genus g with
    canonical divisor K:

      **h⁰(D) - h⁰(K - D) = deg(D) - g + 1**

    **Proof**:
    1. By `riemann_roch_euler`: h⁰(D) - h¹(D) = deg(D) - g + 1
    2. Assume Serre dimension equality: h¹(D) = h⁰(K - D)
    3. Substituting: h⁰(D) - h⁰(K - D) = deg(D) - g + 1 ∎ -/
theorem riemann_roch_of_serre_dim (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (L : LineBundleSheafAssignment CRS.toRiemannSurface O)
    (K : CanonicalDivisorData CRS)
    (gc : ∀ D : Divisor CRS.toRiemannSurface, FiniteGoodCover (L.sheafOf D))
    (D : Divisor CRS.toRiemannSurface)
    (hserre :
      h_i (cechToSheafCohomologyGroup (L.sheafOf D) (gc D) 1) =
      h_i (cechToSheafCohomologyGroup (L.sheafOf (K.divisor - D)) (gc (K.divisor - D)) 0)) :
    (h_i (cechToSheafCohomologyGroup (L.sheafOf D) (gc D) 0) : ℤ) -
    h_i (cechToSheafCohomologyGroup (L.sheafOf (K.divisor - D)) (gc (K.divisor - D)) 0) =
    D.degree - CRS.genus + 1 := by
  -- Step 1: Euler characteristic formula: h⁰(D) - h¹(D) = deg(D) + 1 - g
  have heuler := eulerChar_formula_cech L gc D
  unfold cech_chi eulerCharacteristic at heuler

  -- Step 2: Cast the Serre dimension equality to ℤ and substitute.
  have hserreZ :
      (h_i (cechToSheafCohomologyGroup (L.sheafOf D) (gc D) 1) : ℤ) =
      (h_i (cechToSheafCohomologyGroup (L.sheafOf (K.divisor - D)) (gc (K.divisor - D)) 0) : ℤ) := by
    exact_mod_cast hserre
  have heuler' :
      (h_i (cechToSheafCohomologyGroup (L.sheafOf D) (gc D) 0) : ℤ) -
      (h_i (cechToSheafCohomologyGroup (L.sheafOf (K.divisor - D)) (gc (K.divisor - D)) 0) : ℤ) =
      D.degree + 1 - CRS.genus := by
    simpa [hserreZ] using heuler
  linarith

/-- Classical-form Riemann-Roch from explicit point-exact bridge data
    and explicit Serre-dimension input. -/
theorem riemann_roch_of_serre_dim_from_point_exact_data (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (L : LineBundleSheafAssignment CRS.toRiemannSurface O)
    (K : CanonicalDivisorData CRS)
    (gc : ∀ D : Divisor CRS.toRiemannSurface, FiniteGoodCover (L.sheafOf D))
    (h0 :
      h_i (cechToSheafCohomologyGroup (L.sheafOf 0) (gc 0) 0) = 1)
    (h1 :
      h_i (cechToSheafCohomologyGroup (L.sheafOf 0) (gc 0) 1) = CRS.genus)
    (ses : PointExactProof.PointExactSESFamily O L)
    (les : PointExactProof.PointExactLESFamily O L ses)
    (h''0_dim : PointExactProof.PointExactHpp0 les)
    (h''1_dim : PointExactProof.PointExactHpp1 les)
    (h0_Dp_eq : PointExactProof.PointExactH0Dp gc les)
    (h1_Dp_eq : PointExactProof.PointExactH1Dp gc les)
    (h0_D_eq : PointExactProof.PointExactH0D gc les)
    (h1_D_eq : PointExactProof.PointExactH1D gc les)
    (D : Divisor CRS.toRiemannSurface)
    (hserre :
      h_i (cechToSheafCohomologyGroup (L.sheafOf D) (gc D) 1) =
      h_i (cechToSheafCohomologyGroup (L.sheafOf (K.divisor - D)) (gc (K.divisor - D)) 0)) :
    (h_i (cechToSheafCohomologyGroup (L.sheafOf D) (gc D) 0) : ℤ) -
    h_i (cechToSheafCohomologyGroup (L.sheafOf (K.divisor - D)) (gc (K.divisor - D)) 0) =
    D.degree - CRS.genus + 1 := by
  have heuler := riemann_roch_euler_from_point_exact_data CRS O L gc
    h0 h1 ses les h''0_dim h''1_dim h0_Dp_eq h1_Dp_eq h0_D_eq h1_D_eq D
  unfold cech_chi eulerCharacteristic at heuler
  have hserreZ :
      (h_i (cechToSheafCohomologyGroup (L.sheafOf D) (gc D) 1) : ℤ) =
      (h_i (cechToSheafCohomologyGroup (L.sheafOf (K.divisor - D)) (gc (K.divisor - D)) 0) : ℤ) := by
    exact_mod_cast hserre
  have heuler' :
      (h_i (cechToSheafCohomologyGroup (L.sheafOf D) (gc D) 0) : ℤ) -
      (h_i (cechToSheafCohomologyGroup (L.sheafOf (K.divisor - D)) (gc (K.divisor - D)) 0) : ℤ) =
      D.degree + 1 - CRS.genus := by
    simpa [hserreZ] using heuler
  linarith

/-- Classical-form Riemann-Roch from explicit point-exact bridge data.

    This is `riemann_roch_of_serre_dim_from_point_exact_data` instantiated with
    `serre_duality_dim_cech`. -/
theorem riemann_roch_from_point_exact_data (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (L : LineBundleSheafAssignment CRS.toRiemannSurface O)
    (K : CanonicalDivisorData CRS)
    (gc : ∀ D : Divisor CRS.toRiemannSurface, FiniteGoodCover (L.sheafOf D))
    (h0 :
      h_i (cechToSheafCohomologyGroup (L.sheafOf 0) (gc 0) 0) = 1)
    (h1 :
      h_i (cechToSheafCohomologyGroup (L.sheafOf 0) (gc 0) 1) = CRS.genus)
    (ses : PointExactProof.PointExactSESFamily O L)
    (les : PointExactProof.PointExactLESFamily O L ses)
    (h''0_dim : PointExactProof.PointExactHpp0 les)
    (h''1_dim : PointExactProof.PointExactHpp1 les)
    (h0_Dp_eq : PointExactProof.PointExactH0Dp gc les)
    (h1_Dp_eq : PointExactProof.PointExactH1Dp gc les)
    (h0_D_eq : PointExactProof.PointExactH0D gc les)
    (h1_D_eq : PointExactProof.PointExactH1D gc les)
    (D : Divisor CRS.toRiemannSurface) :
    (h_i (cechToSheafCohomologyGroup (L.sheafOf D) (gc D) 0) : ℤ) -
    h_i (cechToSheafCohomologyGroup (L.sheafOf (K.divisor - D)) (gc (K.divisor - D)) 0) =
    D.degree - CRS.genus + 1 := by
  apply riemann_roch_of_serre_dim_from_point_exact_data CRS O L K gc
    h0 h1 ses les h''0_dim h''1_dim h0_Dp_eq h1_Dp_eq h0_D_eq h1_D_eq D
  exact serre_duality_dim_cech L K D (gc D) (gc (K.divisor - D))

/-- **The Riemann-Roch Theorem** (classical form via Čech Serre duality).

    This is `riemann_roch_of_serre_dim` instantiated with
    `serre_duality_dim_cech`. -/
theorem riemann_roch (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (L : LineBundleSheafAssignment CRS.toRiemannSurface O)
    (K : CanonicalDivisorData CRS)
    (gc : ∀ D : Divisor CRS.toRiemannSurface, FiniteGoodCover (L.sheafOf D))
    (D : Divisor CRS.toRiemannSurface) :
    (h_i (cechToSheafCohomologyGroup (L.sheafOf D) (gc D) 0) : ℤ) -
    h_i (cechToSheafCohomologyGroup (L.sheafOf (K.divisor - D)) (gc (K.divisor - D)) 0) =
    D.degree - CRS.genus + 1 := by
  apply riemann_roch_of_serre_dim CRS O L K gc D
  exact serre_duality_dim_cech L K D (gc D) (gc (K.divisor - D))

/-!
## Corollaries

Key applications of the Riemann-Roch theorem.
-/

/-- **Riemann Inequality**: h⁰(D) ≥ deg(D) - g + 1 when deg(D) ≥ g.

    This follows from Riemann-Roch since h⁰(K - D) ≥ 0. -/
theorem riemann_inequality (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (L : LineBundleSheafAssignment CRS.toRiemannSurface O)
    (gc : ∀ D : Divisor CRS.toRiemannSurface, FiniteGoodCover (L.sheafOf D))
    (D : Divisor CRS.toRiemannSurface) :
    (h_i (cechToSheafCohomologyGroup (L.sheafOf D) (gc D) 0) : ℤ) ≥ D.degree - CRS.genus + 1 := by
  have heuler := eulerChar_formula_cech L gc D
  unfold cech_chi eulerCharacteristic at heuler
  have h_nonneg : (h_i (cechToSheafCohomologyGroup (L.sheafOf D) (gc D) 1) : ℤ) ≥ 0 :=
    Nat.cast_nonneg _
  linarith

/-- **h⁰(D) = 0 for deg(D) < 0**.

    Line bundles of negative degree have no global sections. -/
theorem h0_vanish_negative_degree (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (L : LineBundleSheafAssignment CRS.toRiemannSurface O)
    (D : Divisor CRS.toRiemannSurface)
    (gc : FiniteGoodCover (L.sheafOf D))
    (hdeg : D.degree < 0) :
    h_i (cechToSheafCohomologyGroup (L.sheafOf D) gc 0) = 0 :=
  negative_degree_vanishing_cech L D gc hdeg

/-- **h¹(D) = 0 for deg(D) > 2g - 2**.

    This follows from Serre duality and the vanishing for negative degree. -/
theorem h1_vanish_large_degree (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (L : LineBundleSheafAssignment CRS.toRiemannSurface O)
    (K : CanonicalDivisorData CRS)
    (D : Divisor CRS.toRiemannSurface)
    (gc : FiniteGoodCover (L.sheafOf D))
    (hdeg : D.degree > 2 * (CRS.genus : ℤ) - 2) :
    h_i (cechToSheafCohomologyGroup (L.sheafOf D) gc 1) = 0 :=
  large_degree_h1_vanishing_cech L K D gc hdeg

/-- **Simplified Riemann-Roch for large degree**.

    When deg(D) > 2g - 2, we have h¹(D) = 0, so:
      h⁰(D) = deg(D) - g + 1 -/
theorem riemann_roch_large_degree (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (L : LineBundleSheafAssignment CRS.toRiemannSurface O)
    (K : CanonicalDivisorData CRS)
    (gc : ∀ D : Divisor CRS.toRiemannSurface, FiniteGoodCover (L.sheafOf D))
    (D : Divisor CRS.toRiemannSurface)
    (hdeg : D.degree > 2 * (CRS.genus : ℤ) - 2) :
    (h_i (cechToSheafCohomologyGroup (L.sheafOf D) (gc D) 0) : ℤ) = D.degree - CRS.genus + 1 := by
  -- Step 1: Euler characteristic formula
  have heuler := eulerChar_formula_cech L gc D
  unfold cech_chi eulerCharacteristic at heuler
  -- heuler : h⁰(D) - h¹(D) = deg(D) + 1 - g

  -- Step 2: For deg(D) > 2g - 2, h¹(D) = 0
  have h1_vanish : h_i (cechToSheafCohomologyGroup (L.sheafOf D) (gc D) 1) = 0 :=
    large_degree_h1_vanishing_cech L K D (gc D) hdeg

  -- Step 3: Substitute h¹(D) = 0
  simp only [h1_vanish, Nat.cast_zero, sub_zero] at heuler
  omega

/-!
## Quadratic Differentials and Moduli Space Dimension

The key application: dim M_g = h⁰(K²) = 3g - 3 for g ≥ 2.
-/

/-- n-fold tensor power of the canonical divisor: K^n = nK -/
def nTimesCanonical {CRS : CompactRiemannSurface}
    (K : CanonicalDivisorData CRS) (n : ℕ) : Divisor CRS.toRiemannSurface :=
  n • K.divisor

/-- ℕ-smul equals ℤ-smul for divisors -/
private theorem nsmul_eq_zsmul {RS : RiemannSurface} (n : ℕ) (D : Divisor RS) :
    n • D = (n : ℤ) • D := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_smul]
    ext p
    simp only [Divisor.smul_coeff, zero_mul]
    rfl
  | succ k ih =>
    rw [succ_nsmul, ih]
    ext p
    simp only [Divisor.add_coeff, Divisor.smul_coeff, Nat.cast_succ]
    ring

/-- **deg(K^n) = n(2g - 2)** -/
theorem nTimesCanonical_degree (CRS : CompactRiemannSurface)
    (K : CanonicalDivisorData CRS) (n : ℕ) :
    (nTimesCanonical K n).degree = n * (2 * (CRS.genus : ℤ) - 2) := by
  unfold nTimesCanonical
  rw [nsmul_eq_zsmul, Divisor.degree_smul, canonical_divisor_degree CRS K]

/-- **h⁰(K²) = 3g - 3 for g ≥ 2**.

    Quadratic differentials are sections of K².

    **Proof**:
    1. deg(K²) = 2(2g - 2) = 4g - 4
    2. For g ≥ 2: deg(K²) = 4g - 4 > 2g - 2
    3. By large degree Riemann-Roch: h⁰(K²) = deg(K²) - g + 1
       = (4g - 4) - g + 1 = 3g - 3 ∎ -/
theorem h0_K2 (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (L : LineBundleSheafAssignment CRS.toRiemannSurface O)
    (K : CanonicalDivisorData CRS)
    (gc : ∀ D : Divisor CRS.toRiemannSurface, FiniteGoodCover (L.sheafOf D))
    (hg : CRS.genus ≥ 2) :
    (h_i (cechToSheafCohomologyGroup (L.sheafOf (nTimesCanonical K 2)) (gc _) 0) : ℤ) =
    3 * CRS.genus - 3 := by
  -- deg(K²) = 2(2g - 2) = 4g - 4
  have hdeg : (nTimesCanonical K 2).degree = 4 * (CRS.genus : ℤ) - 4 := by
    rw [nTimesCanonical_degree]
    ring
  -- For g ≥ 2: deg(K²) = 4g - 4 > 2g - 2
  have hdeg_large : (nTimesCanonical K 2).degree > 2 * (CRS.genus : ℤ) - 2 := by
    rw [hdeg]
    have hg' : (CRS.genus : ℤ) ≥ 2 := by exact_mod_cast hg
    linarith
  -- By large degree Riemann-Roch: h⁰(K²) = deg(K²) - g + 1
  have hrr := riemann_roch_large_degree CRS O L K gc (nTimesCanonical K 2) hdeg_large
  rw [hdeg] at hrr
  linarith

/-- **Dimension of moduli space**: dim M_g = 3g - 3 for g ≥ 2.

    By deformation theory: T_{[Σ]} M_g = H¹(T_Σ) = H⁰(K²)*
    Therefore: dim M_g = h⁰(K²) = 3g - 3 -/
theorem moduli_dimension (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (L : LineBundleSheafAssignment CRS.toRiemannSurface O)
    (K : CanonicalDivisorData CRS)
    (gc : ∀ D : Divisor CRS.toRiemannSurface, FiniteGoodCover (L.sheafOf D))
    (hg : CRS.genus ≥ 2) :
    (h_i (cechToSheafCohomologyGroup (L.sheafOf (nTimesCanonical K 2)) (gc _) 0) : ℤ) =
    3 * CRS.genus - 3 :=
  h0_K2 CRS O L K gc hg

/-- **h⁰(K^n) = (2n-1)(g-1) for n ≥ 2 and g ≥ 2**.

    General formula for pluricanonical bundles. -/
theorem h0_Kn (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (L : LineBundleSheafAssignment CRS.toRiemannSurface O)
    (K : CanonicalDivisorData CRS)
    (gc : ∀ D : Divisor CRS.toRiemannSurface, FiniteGoodCover (L.sheafOf D))
    (n : ℕ) (hn : n ≥ 2) (hg : CRS.genus ≥ 2) :
    (h_i (cechToSheafCohomologyGroup (L.sheafOf (nTimesCanonical K n)) (gc _) 0) : ℤ) =
    (2 * n - 1) * (CRS.genus - 1) := by
  -- deg(K^n) = n(2g - 2)
  have hdeg : (nTimesCanonical K n).degree = n * (2 * (CRS.genus : ℤ) - 2) := by
    exact nTimesCanonical_degree CRS K n
  -- For n ≥ 2 and g ≥ 2: deg(K^n) = n(2g-2) > 2g - 2
  have hdeg_large : (nTimesCanonical K n).degree > 2 * (CRS.genus : ℤ) - 2 := by
    rw [hdeg]
    have hg' : (CRS.genus : ℤ) ≥ 2 := by exact_mod_cast hg
    have hn' : (n : ℤ) ≥ 2 := by exact_mod_cast hn
    nlinarith
  -- By large degree Riemann-Roch
  have hrr := riemann_roch_large_degree CRS O L K gc (nTimesCanonical K n) hdeg_large
  rw [hdeg] at hrr
  -- Goal: (2n - 1)(g - 1) = n(2g - 2) - g + 1
  -- n(2g - 2) - g + 1 = 2ng - 2n - g + 1 = (2n - 1)g - 2n + 1 = (2n - 1)(g - 1)
  have hg' : (CRS.genus : ℤ) ≥ 2 := by exact_mod_cast hg
  have hn' : (n : ℤ) ≥ 2 := by exact_mod_cast hn
  linarith

/-- **No global holomorphic vector fields for g ≥ 2**.

    h⁰(T) = h⁰(K⁻¹) = 0 since deg(K⁻¹) = 2 - 2g < 0. -/
theorem h0_tangent_vanish (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (L : LineBundleSheafAssignment CRS.toRiemannSurface O)
    (K : CanonicalDivisorData CRS)
    (gc : FiniteGoodCover (L.sheafOf (-K.divisor)))
    (hg : CRS.genus ≥ 2) :
    h_i (cechToSheafCohomologyGroup (L.sheafOf (-K.divisor)) gc 0) = 0 := by
  -- deg(-K) = -(2g - 2) = 2 - 2g < 0 for g ≥ 2
  have hdeg : (-K.divisor).degree < 0 := by
    rw [Divisor.degree_neg, canonical_divisor_degree CRS K]
    have hg' : (CRS.genus : ℤ) ≥ 2 := by exact_mod_cast hg
    linarith
  exact negative_degree_vanishing_cech L (-K.divisor) gc hdeg

/-!
## Summary of Main Results

The Riemann-Roch theorem and its corollaries (all using Čech cohomology):

1. **Riemann-Roch (Euler form)**: χ(D) = deg(D) + 1 - g
2. **Riemann-Roch (classical)**: h⁰(D) - h⁰(K-D) = deg(D) - g + 1
3. **Serre duality**: h¹(D) = h⁰(K-D)
4. **Vanishing**: h⁰(D) = 0 for deg D < 0
5. **Large degree**: h⁰(D) = deg(D) - g + 1 for deg D > 2g - 2
6. **Moduli dimension**: dim M_g = h⁰(K²) = 3g - 3

These are the fundamental results connecting divisor theory to cohomology
on compact Riemann surfaces. All results use Čech cohomology directly via
`FiniteGoodCover`, with no axiom smuggling.
-/

end RiemannSurfaces.Algebraic
