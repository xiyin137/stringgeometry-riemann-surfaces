import StringGeometry.RiemannSurfaces.GAGA.Cohomology.CechTheory
import StringGeometry.RiemannSurfaces.GAGA.Cohomology.ExactSequence
import StringGeometry.Topology.Sheaves.LongExactSequence

/-!
# Point-Exact Euler Characteristic Transfer

This file keeps the point-recursion bridge in hypothesis-driven form:
no bundled "data structures with theorem fields".  Instead, the exact-sequence
and dimension-identification facts are explicit theorem arguments.
-/

namespace RiemannSurfaces.Algebraic.Cohomology.PointExactProof

open RiemannSurfaces.Algebraic.Cohomology
open RiemannSurfaces.Algebraic.Cohomology.CechTheory

/-- Shorthand for the divisor sheaf `O(D)` used in this bridge file. -/
abbrev DivisorSheaf
    {CRS : CompactRiemannSurface}
    (O : StructureSheaf CRS.toRiemannSurface)
    (L : LineBundleSheafAssignment CRS.toRiemannSurface O)
    (D : Divisor CRS.toRiemannSurface) :
    CoherentSheaf CRS.toRiemannSurface O :=
  coherentSheafOfDivisor CRS.toRiemannSurface O L D

/-- If the short exact sequence `0 → O(D-p) → O(D) → C_p → 0` and its cohomology
identifications are provided, then the point recursion
`χ(D) - χ(D-p) = 1` follows. -/
theorem cech_point_exact_of_data
    {CRS : CompactRiemannSurface}
    {O : StructureSheaf CRS.toRiemannSurface}
    (L : LineBundleSheafAssignment CRS.toRiemannSurface O)
    (gc : ∀ D : Divisor CRS.toRiemannSurface, FiniteGoodCover (L.sheafOf D))
    (D : Divisor CRS.toRiemannSurface)
    (p : CRS.toRiemannSurface.carrier)
    (ses : ShortExactSeq CRS.toRiemannSurface O
      (DivisorSheaf O L (D - Divisor.point p))
      (DivisorSheaf O L D)
      (skyscraperSheaf O p))
    (les : LongExactSequence CRS.toRiemannSurface
      (DivisorSheaf O L (D - Divisor.point p))
      (DivisorSheaf O L D)
      (skyscraperSheaf O p)
      ses)
    (h''0_dim : les.H''0.dimension = 1)
    (h''1_dim : les.H''1.dimension = 0)
    (h0_Dp_eq : les.H'0.dimension = (gc (D - Divisor.point p)).dim 0)
    (h1_Dp_eq : les.H'1.dimension = (gc (D - Divisor.point p)).dim 1)
    (h0_D_eq : les.H0.dimension = (gc D).dim 0)
    (h1_D_eq : les.H1.dimension = (gc D).dim 1) :
    cech_chi L gc D - cech_chi L gc (D - Divisor.point p) = 1 := by
  have hskyscraper : eulerCharacteristic les.H''0 les.H''1 = 1 := by
    unfold eulerCharacteristic h_i
    rw [h''0_dim, h''1_dim]
    norm_num

  have hadd := les.eulerChar_additive
  have hpoint : eulerCharacteristic les.H0 les.H1 - eulerCharacteristic les.H'0 les.H'1 = 1 := by
    omega

  have hchi_D : eulerCharacteristic les.H0 les.H1 = cech_chi L gc D := by
    unfold cech_chi eulerCharacteristic h_i
    unfold cechToSheafCohomologyGroup
    simp only [h0_D_eq, h1_D_eq]

  have hchi_Dp : eulerCharacteristic les.H'0 les.H'1 = cech_chi L gc (D - Divisor.point p) := by
    unfold cech_chi eulerCharacteristic h_i
    unfold cechToSheafCohomologyGroup
    simp only [h0_Dp_eq, h1_Dp_eq]

  rw [← hchi_D, ← hchi_Dp]
  exact hpoint

/-- Same statement as `cech_point_exact_of_data`, kept as the public entry point. -/
theorem point_exact_cech_proof
    {CRS : CompactRiemannSurface}
    {O : StructureSheaf CRS.toRiemannSurface}
    (L : LineBundleSheafAssignment CRS.toRiemannSurface O)
    (gc : ∀ D : Divisor CRS.toRiemannSurface, FiniteGoodCover (L.sheafOf D))
    (D : Divisor CRS.toRiemannSurface)
    (p : CRS.toRiemannSurface.carrier)
    (ses : ShortExactSeq CRS.toRiemannSurface O
      (DivisorSheaf O L (D - Divisor.point p))
      (DivisorSheaf O L D)
      (skyscraperSheaf O p))
    (les : LongExactSequence CRS.toRiemannSurface
      (DivisorSheaf O L (D - Divisor.point p))
      (DivisorSheaf O L D)
      (skyscraperSheaf O p)
      ses)
    (h''0_dim : les.H''0.dimension = 1)
    (h''1_dim : les.H''1.dimension = 0)
    (h0_Dp_eq : les.H'0.dimension = (gc (D - Divisor.point p)).dim 0)
    (h1_Dp_eq : les.H'1.dimension = (gc (D - Divisor.point p)).dim 1)
    (h0_D_eq : les.H0.dimension = (gc D).dim 0)
    (h1_D_eq : les.H1.dimension = (gc D).dim 1) :
    cech_chi L gc D - cech_chi L gc (D - Divisor.point p) = 1 := by
  exact cech_point_exact_of_data L gc D p ses les h''0_dim h''1_dim
    h0_Dp_eq h1_Dp_eq h0_D_eq h1_D_eq

/-- Riemann-Roch Euler formula from explicit point-exact sequence data.

    This instantiates `CechTheory.eulerChar_formula_cech_of` by deriving its
    point-recursion hypothesis from explicit short/long exact-sequence inputs
    for each pair `(E, p)`. -/
theorem eulerChar_formula_cech_from_point_exact_data
    {CRS : CompactRiemannSurface}
    {O : StructureSheaf CRS.toRiemannSurface}
    (L : LineBundleSheafAssignment CRS.toRiemannSurface O)
    (gc : ∀ D : Divisor CRS.toRiemannSurface, FiniteGoodCover (L.sheafOf D))
    (h0 :
      h_i (cechToSheafCohomologyGroup (L.sheafOf 0) (gc 0) 0) = 1)
    (h1 :
      h_i (cechToSheafCohomologyGroup (L.sheafOf 0) (gc 0) 1) = CRS.genus)
    (ses : ∀ E : Divisor CRS.toRiemannSurface,
      ∀ p : CRS.toRiemannSurface.carrier,
      ShortExactSeq CRS.toRiemannSurface O
        (DivisorSheaf O L (E - Divisor.point p))
        (DivisorSheaf O L E)
        (skyscraperSheaf O p))
    (les : ∀ E : Divisor CRS.toRiemannSurface,
      ∀ p : CRS.toRiemannSurface.carrier,
      LongExactSequence CRS.toRiemannSurface
        (DivisorSheaf O L (E - Divisor.point p))
        (DivisorSheaf O L E)
        (skyscraperSheaf O p)
        (ses E p))
    (h''0_dim : ∀ E : Divisor CRS.toRiemannSurface,
      ∀ p : CRS.toRiemannSurface.carrier,
      (les E p).H''0.dimension = 1)
    (h''1_dim : ∀ E : Divisor CRS.toRiemannSurface,
      ∀ p : CRS.toRiemannSurface.carrier,
      (les E p).H''1.dimension = 0)
    (h0_Dp_eq : ∀ E : Divisor CRS.toRiemannSurface,
      ∀ p : CRS.toRiemannSurface.carrier,
      (les E p).H'0.dimension = (gc (E - Divisor.point p)).dim 0)
    (h1_Dp_eq : ∀ E : Divisor CRS.toRiemannSurface,
      ∀ p : CRS.toRiemannSurface.carrier,
      (les E p).H'1.dimension = (gc (E - Divisor.point p)).dim 1)
    (h0_D_eq : ∀ E : Divisor CRS.toRiemannSurface,
      ∀ p : CRS.toRiemannSurface.carrier,
      (les E p).H0.dimension = (gc E).dim 0)
    (h1_D_eq : ∀ E : Divisor CRS.toRiemannSurface,
      ∀ p : CRS.toRiemannSurface.carrier,
      (les E p).H1.dimension = (gc E).dim 1)
    (D : Divisor CRS.toRiemannSurface) :
    cech_chi L gc D = D.degree + 1 - CRS.genus := by
  apply eulerChar_formula_cech_of L gc h0 h1
  intro E p
  exact cech_point_exact_of_data L gc E p (ses E p) (les E p)
    (h''0_dim E p) (h''1_dim E p)
    (h0_Dp_eq E p) (h1_Dp_eq E p)
    (h0_D_eq E p) (h1_D_eq E p)

end RiemannSurfaces.Algebraic.Cohomology.PointExactProof
