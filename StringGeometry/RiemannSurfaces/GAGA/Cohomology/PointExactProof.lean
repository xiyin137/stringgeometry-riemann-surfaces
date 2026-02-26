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
    CoherentSheaf.{0} CRS.toRiemannSurface O :=
  coherentSheafOfDivisor CRS.toRiemannSurface O L D

/-- Skyscraper sheaf at `p` with universe pinned to `0` for signature helpers. -/
noncomputable abbrev SkyscraperSheaf0
    {CRS : CompactRiemannSurface}
    (O : StructureSheaf CRS.toRiemannSurface)
    (p : CRS.toRiemannSurface.carrier) :
    CoherentSheaf.{0} CRS.toRiemannSurface O :=
  skyscraperSheaf O p

/-- Family of short exact sequences
`0 → O(E-p) → O(E) → C_p → 0` for all divisor/point pairs `(E,p)`. -/
abbrev PointExactSESFamily
    {CRS : CompactRiemannSurface}
    (O : StructureSheaf CRS.toRiemannSurface)
    (L : LineBundleSheafAssignment CRS.toRiemannSurface O) :=
  ∀ E : Divisor CRS.toRiemannSurface,
    ∀ p : CRS.toRiemannSurface.carrier,
    ShortExactSeq CRS.toRiemannSurface O
      (DivisorSheaf O L (E - Divisor.point p))
      (DivisorSheaf O L E)
      (SkyscraperSheaf0 O p)

/-- Family of long exact sequences induced by `PointExactSESFamily`. -/
abbrev PointExactLESFamily
    {CRS : CompactRiemannSurface}
    (O : StructureSheaf CRS.toRiemannSurface)
    (L : LineBundleSheafAssignment CRS.toRiemannSurface O)
    (ses : PointExactSESFamily O L) :=
  ∀ E : Divisor CRS.toRiemannSurface,
    ∀ p : CRS.toRiemannSurface.carrier,
    LongExactSequence CRS.toRiemannSurface
      (DivisorSheaf O L (E - Divisor.point p))
      (DivisorSheaf O L E)
      (SkyscraperSheaf0 O p)
      (ses E p)

/-- Pointwise short exact sequence `0 → O(D-p) → O(D) → C_p → 0`
for a fixed divisor/point pair `(D,p)`. -/
abbrev PointExactSESAt
    {CRS : CompactRiemannSurface}
    (O : StructureSheaf CRS.toRiemannSurface)
    (L : LineBundleSheafAssignment CRS.toRiemannSurface O)
    (D : Divisor CRS.toRiemannSurface)
    (p : CRS.toRiemannSurface.carrier) :=
  ShortExactSeq CRS.toRiemannSurface O
    (DivisorSheaf O L (D - Divisor.point p))
    (DivisorSheaf O L D)
    (SkyscraperSheaf0 O p)

/-- Pointwise long exact sequence induced by `PointExactSESAt`. -/
abbrev PointExactLESAt
    {CRS : CompactRiemannSurface}
    (O : StructureSheaf CRS.toRiemannSurface)
    (L : LineBundleSheafAssignment CRS.toRiemannSurface O)
    (D : Divisor CRS.toRiemannSurface)
    (p : CRS.toRiemannSurface.carrier)
    (ses : PointExactSESAt O L D p) :=
  LongExactSequence CRS.toRiemannSurface
    (DivisorSheaf O L (D - Divisor.point p))
    (DivisorSheaf O L D)
    (SkyscraperSheaf0 O p)
    ses

/-- Pointwise dimension input: `H''0` has dimension 1. -/
abbrev PointExactHpp0At
    {CRS : CompactRiemannSurface}
    {O : StructureSheaf CRS.toRiemannSurface}
    {L : LineBundleSheafAssignment CRS.toRiemannSurface O}
    (D : Divisor CRS.toRiemannSurface)
    (p : CRS.toRiemannSurface.carrier)
    {ses : PointExactSESAt O L D p}
    (les : PointExactLESAt O L D p ses) :=
  les.H''0.dimension = 1

/-- Pointwise dimension input: `H''1` has dimension 0. -/
abbrev PointExactHpp1At
    {CRS : CompactRiemannSurface}
    {O : StructureSheaf CRS.toRiemannSurface}
    {L : LineBundleSheafAssignment CRS.toRiemannSurface O}
    (D : Divisor CRS.toRiemannSurface)
    (p : CRS.toRiemannSurface.carrier)
    {ses : PointExactSESAt O L D p}
    (les : PointExactLESAt O L D p ses) :=
  les.H''1.dimension = 0

/-- Pointwise dimension-identification input for `H'0` (the `O(D-p)` side). -/
abbrev PointExactH0DpAt
    {CRS : CompactRiemannSurface}
    {O : StructureSheaf CRS.toRiemannSurface}
    {L : LineBundleSheafAssignment CRS.toRiemannSurface O}
    (gc : ∀ D : Divisor CRS.toRiemannSurface, FiniteGoodCover (L.sheafOf D))
    (D : Divisor CRS.toRiemannSurface)
    (p : CRS.toRiemannSurface.carrier)
    {ses : PointExactSESAt O L D p}
    (les : PointExactLESAt O L D p ses) :=
  les.H'0.dimension = (gc (D - Divisor.point p)).dim 0

/-- Pointwise dimension-identification input for `H'1` (the `O(D-p)` side). -/
abbrev PointExactH1DpAt
    {CRS : CompactRiemannSurface}
    {O : StructureSheaf CRS.toRiemannSurface}
    {L : LineBundleSheafAssignment CRS.toRiemannSurface O}
    (gc : ∀ D : Divisor CRS.toRiemannSurface, FiniteGoodCover (L.sheafOf D))
    (D : Divisor CRS.toRiemannSurface)
    (p : CRS.toRiemannSurface.carrier)
    {ses : PointExactSESAt O L D p}
    (les : PointExactLESAt O L D p ses) :=
  les.H'1.dimension = (gc (D - Divisor.point p)).dim 1

/-- Pointwise dimension-identification input for `H0` (the `O(D)` side). -/
abbrev PointExactH0DAt
    {CRS : CompactRiemannSurface}
    {O : StructureSheaf CRS.toRiemannSurface}
    {L : LineBundleSheafAssignment CRS.toRiemannSurface O}
    (gc : ∀ D : Divisor CRS.toRiemannSurface, FiniteGoodCover (L.sheafOf D))
    (D : Divisor CRS.toRiemannSurface)
    (p : CRS.toRiemannSurface.carrier)
    {ses : PointExactSESAt O L D p}
    (les : PointExactLESAt O L D p ses) :=
  les.H0.dimension = (gc D).dim 0

/-- Pointwise dimension-identification input for `H1` (the `O(D)` side). -/
abbrev PointExactH1DAt
    {CRS : CompactRiemannSurface}
    {O : StructureSheaf CRS.toRiemannSurface}
    {L : LineBundleSheafAssignment CRS.toRiemannSurface O}
    (gc : ∀ D : Divisor CRS.toRiemannSurface, FiniteGoodCover (L.sheafOf D))
    (D : Divisor CRS.toRiemannSurface)
    (p : CRS.toRiemannSurface.carrier)
    {ses : PointExactSESAt O L D p}
    (les : PointExactLESAt O L D p ses) :=
  les.H1.dimension = (gc D).dim 1

/-- Dimension input: `H''0` has dimension 1 for each `(E,p)`. -/
abbrev PointExactHpp0
    {CRS : CompactRiemannSurface}
    {O : StructureSheaf CRS.toRiemannSurface}
    {L : LineBundleSheafAssignment CRS.toRiemannSurface O}
    {ses : PointExactSESFamily O L}
    (les : PointExactLESFamily O L ses) :=
  ∀ E : Divisor CRS.toRiemannSurface,
    ∀ p : CRS.toRiemannSurface.carrier,
    (les E p).H''0.dimension = 1

/-- Dimension input: `H''1` has dimension 0 for each `(E,p)`. -/
abbrev PointExactHpp1
    {CRS : CompactRiemannSurface}
    {O : StructureSheaf CRS.toRiemannSurface}
    {L : LineBundleSheafAssignment CRS.toRiemannSurface O}
    {ses : PointExactSESFamily O L}
    (les : PointExactLESFamily O L ses) :=
  ∀ E : Divisor CRS.toRiemannSurface,
    ∀ p : CRS.toRiemannSurface.carrier,
    (les E p).H''1.dimension = 0

/-- Dimension-identification input for `H'0` (the `O(E-p)` side). -/
abbrev PointExactH0Dp
    {CRS : CompactRiemannSurface}
    {O : StructureSheaf CRS.toRiemannSurface}
    {L : LineBundleSheafAssignment CRS.toRiemannSurface O}
    (gc : ∀ D : Divisor CRS.toRiemannSurface, FiniteGoodCover (L.sheafOf D))
    {ses : PointExactSESFamily O L}
    (les : PointExactLESFamily O L ses) :=
  ∀ E : Divisor CRS.toRiemannSurface,
    ∀ p : CRS.toRiemannSurface.carrier,
    (les E p).H'0.dimension = (gc (E - Divisor.point p)).dim 0

/-- Dimension-identification input for `H'1` (the `O(E-p)` side). -/
abbrev PointExactH1Dp
    {CRS : CompactRiemannSurface}
    {O : StructureSheaf CRS.toRiemannSurface}
    {L : LineBundleSheafAssignment CRS.toRiemannSurface O}
    (gc : ∀ D : Divisor CRS.toRiemannSurface, FiniteGoodCover (L.sheafOf D))
    {ses : PointExactSESFamily O L}
    (les : PointExactLESFamily O L ses) :=
  ∀ E : Divisor CRS.toRiemannSurface,
    ∀ p : CRS.toRiemannSurface.carrier,
    (les E p).H'1.dimension = (gc (E - Divisor.point p)).dim 1

/-- Dimension-identification input for `H0` (the `O(E)` side). -/
abbrev PointExactH0D
    {CRS : CompactRiemannSurface}
    {O : StructureSheaf CRS.toRiemannSurface}
    {L : LineBundleSheafAssignment CRS.toRiemannSurface O}
    (gc : ∀ D : Divisor CRS.toRiemannSurface, FiniteGoodCover (L.sheafOf D))
    {ses : PointExactSESFamily O L}
    (les : PointExactLESFamily O L ses) :=
  ∀ E : Divisor CRS.toRiemannSurface,
    ∀ p : CRS.toRiemannSurface.carrier,
    (les E p).H0.dimension = (gc E).dim 0

/-- Dimension-identification input for `H1` (the `O(E)` side). -/
abbrev PointExactH1D
    {CRS : CompactRiemannSurface}
    {O : StructureSheaf CRS.toRiemannSurface}
    {L : LineBundleSheafAssignment CRS.toRiemannSurface O}
    (gc : ∀ D : Divisor CRS.toRiemannSurface, FiniteGoodCover (L.sheafOf D))
    {ses : PointExactSESFamily O L}
    (les : PointExactLESFamily O L ses) :=
  ∀ E : Divisor CRS.toRiemannSurface,
    ∀ p : CRS.toRiemannSurface.carrier,
    (les E p).H1.dimension = (gc E).dim 1

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
    (ses : PointExactSESAt O L D p)
    (les : PointExactLESAt O L D p ses)
    (h''0_dim : PointExactHpp0At D p les)
    (h''1_dim : PointExactHpp1At D p les)
    (h0_Dp_eq : PointExactH0DpAt gc D p les)
    (h1_Dp_eq : PointExactH1DpAt gc D p les)
    (h0_D_eq : PointExactH0DAt gc D p les)
    (h1_D_eq : PointExactH1DAt gc D p les) :
    cech_chi L gc D - cech_chi L gc (D - Divisor.point p) = 1 := by
  simpa [cech_chi] using
    point_recursion_cech_of_data L D p (gc D) (gc (D - Divisor.point p))
      ses les h''0_dim h''1_dim h0_Dp_eq h1_Dp_eq h0_D_eq h1_D_eq

/-- Same statement as `cech_point_exact_of_data`, kept as the public entry point. -/
theorem point_exact_cech_proof
    {CRS : CompactRiemannSurface}
    {O : StructureSheaf CRS.toRiemannSurface}
    (L : LineBundleSheafAssignment CRS.toRiemannSurface O)
    (gc : ∀ D : Divisor CRS.toRiemannSurface, FiniteGoodCover (L.sheafOf D))
    (D : Divisor CRS.toRiemannSurface)
    (p : CRS.toRiemannSurface.carrier)
    (ses : PointExactSESAt O L D p)
    (les : PointExactLESAt O L D p ses)
    (h''0_dim : PointExactHpp0At D p les)
    (h''1_dim : PointExactHpp1At D p les)
    (h0_Dp_eq : PointExactH0DpAt gc D p les)
    (h1_Dp_eq : PointExactH1DpAt gc D p les)
    (h0_D_eq : PointExactH0DAt gc D p les)
    (h1_D_eq : PointExactH1DAt gc D p les) :
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
    (ses : PointExactSESFamily O L)
    (les : PointExactLESFamily O L ses)
    (h''0_dim : PointExactHpp0 les)
    (h''1_dim : PointExactHpp1 les)
    (h0_Dp_eq : PointExactH0Dp gc les)
    (h1_Dp_eq : PointExactH1Dp gc les)
    (h0_D_eq : PointExactH0D gc les)
    (h1_D_eq : PointExactH1D gc les)
    (D : Divisor CRS.toRiemannSurface) :
    cech_chi L gc D = D.degree + 1 - CRS.genus := by
  apply eulerChar_formula_cech_of L gc h0 h1
  intro E p
  exact cech_point_exact_of_data L gc E p (ses E p) (les E p)
    (h''0_dim E p) (h''1_dim E p)
    (h0_Dp_eq E p) (h1_Dp_eq E p)
    (h0_D_eq E p) (h1_D_eq E p)

end RiemannSurfaces.Algebraic.Cohomology.PointExactProof
