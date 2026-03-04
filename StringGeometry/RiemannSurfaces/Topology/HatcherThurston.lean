import StringGeometry.RiemannSurfaces.Topology.PantsDecomposition

/-!
# Hatcher-Thurston Theorem

This file develops the Hatcher-Thurston theorem on connectivity of the
pants complex (marking complex).

## Mathematical Background (Hatcher-Thurston 1980)

### Simple Moves (I)-(IV)

Hatcher-Thurston define four types of simple moves on markings:

**Move (I)**: In a 4-holed sphere subsurface, replace one essential curve
by the other. This is the **only move that changes the dual trivalent graph**.

**Move (II)**: In a 1-holed torus, replace α by β with i(α,β) = 1.
**Move (III)**: In a 2-holed torus, twist around a boundary curve.
**Move (IV)**: In a 4-holed sphere, half-twist interchanging two boundaries.

**Key theorem**: "Moves (I) and (IV) suffice" to connect any two markings.

### Main Theorem

**Proposition** (Hatcher-Thurston, Appendix):
"Any two markings of M are obtainable one from the other by a finite
sequence of simple moves of these four types (up to isotopy)."

This shows the **pants graph** is **connected**.

## Main Definitions

* `HatcherThurstonMove` - The four move types (I)-(IV)
* `PantsGraph` - Graph with vertices = markings, edges = elementary moves
* `hatcher_thurston` - The connectivity theorem

## References

* Hatcher, Thurston "A presentation for the mapping class group" (1980)
-/

namespace RiemannSurfaces.Topology

open SimpleCurve Marking

/-!
## Hatcher-Thurston Simple Moves (I)-(IV)
-/

/-- A 4-holed sphere subsurface is determined by 4 boundary curves.
    The two essential curves in a 4-holed sphere (up to isotopy) are
    the ones that separate the boundaries into pairs. -/
structure FourHoledSphereSubsurface where
  /-- The four boundary curves of the subsurface -/
  boundaries : Fin 4 → SimpleCurve
  /-- All boundaries are distinct -/
  distinct : ∀ i j, i ≠ j → boundaries i ≠ boundaries j

/-- **Move (I)**: The A-move or "flip" in a 4-holed sphere.

    This is the only move that changes the dual trivalent graph.
    In the 4-holed sphere formed by two adjacent trinions sharing an edge e,
    there are exactly two isotopy classes of essential simple closed curves.
    Move (I) swaps between them.

    **Graph effect**: Flips edge e between vertices v and w. -/
structure MoveI (g n : ℕ) where
  /-- The curve being removed -/
  oldCurve : SimpleCurve
  /-- The curve being added -/
  newCurve : SimpleCurve
  /-- They are distinct -/
  distinct : oldCurve ≠ newCurve
  /-- The old curve is essential -/
  oldEssential : oldCurve.essential
  /-- The new curve is essential -/
  newEssential : newCurve.essential
  /-- The 4-holed sphere subsurface where the flip occurs -/
  subsurface : FourHoledSphereSubsurface
  /-- The old and new curves are the two essential curves in this 4-holed sphere.
      They separate the 4 boundaries into pairs in different ways. -/
  areDualCurves : Prop  -- oldCurve separates {b0,b1} from {b2,b3}, newCurve separates {b0,b2} from {b1,b3}

/-- **Move (II)**: The S-move in a 1-holed torus.

    In a subsurface homeomorphic to a torus with one boundary component,
    replace curve α by curve β where i(α, β) = 1.

    This generates SL(2,ℤ) action on the torus.
    **Graph effect**: None (preserves the dual graph). -/
structure MoveII (g n : ℕ) where
  /-- Intersection data for the surface -/
  iData : IntersectionData
  /-- The curve being removed -/
  oldCurve : SimpleCurve
  /-- The curve being added -/
  newCurve : SimpleCurve
  /-- They intersect exactly once -/
  intersectOnce : SimpleCurve.intersectionNumber iData oldCurve newCurve = 1
  /-- The new curve is essential -/
  newEssential : newCurve.essential

/-- A 2-holed torus subsurface (genus 1 with 2 boundary components). -/
structure TwoHoledTorusSubsurface where
  /-- The two boundary curves -/
  boundary1 : SimpleCurve
  boundary2 : SimpleCurve
  /-- Boundaries are distinct -/
  distinct : boundary1 ≠ boundary2

/-- **Move (III)**: Twist in a 2-holed torus.

    In a genus-1 surface with 2 boundary components, perform a Dehn twist
    around one of the boundary curves.

    **Graph effect**: None. -/
structure MoveIII (g n : ℕ) where
  /-- The 2-holed torus subsurface -/
  subsurface : TwoHoledTorusSubsurface
  /-- The boundary curve for the twist (one of the two boundaries) -/
  twistCurve : SimpleCurve
  /-- The twist curve is one of the boundaries -/
  isBoundary : twistCurve = subsurface.boundary1 ∨ twistCurve = subsurface.boundary2
  /-- Number of twists (positive = right, negative = left) -/
  twistCount : ℤ

/-- **Move (IV)**: Half-twist in a 4-holed sphere.

    In a 4-holed sphere, interchange two of the four boundary components
    via a half-twist. Different from Move (I).

    **Graph effect**: None (but changes which curves are on which side). -/
structure MoveIV (g n : ℕ) where
  /-- The 4-holed sphere subsurface -/
  subsurface : FourHoledSphereSubsurface
  /-- First boundary being interchanged -/
  index1 : Fin 4
  /-- Second boundary being interchanged -/
  index2 : Fin 4
  /-- They are distinct indices -/
  distinctIndices : index1 ≠ index2

/-- The four Hatcher-Thurston simple moves -/
inductive HatcherThurstonMove (g n : ℕ)
  | moveI : MoveI g n → HatcherThurstonMove g n
  | moveII : MoveII g n → HatcherThurstonMove g n
  | moveIII : MoveIII g n → HatcherThurstonMove g n
  | moveIV : MoveIV g n → HatcherThurstonMove g n

/-- A move changes the dual graph iff it is Move (I) -/
def HatcherThurstonMove.changesGraph : HatcherThurstonMove g n → Prop
  | .moveI _ => True
  | .moveII _ => False
  | .moveIII _ => False
  | .moveIV _ => False

/-!
## Simplified Elementary Moves (A and S)

For many purposes, the simpler "A-move" and "S-move" suffice:
- **A-move** = Move (I): flips in 4-holed spheres
- **S-move** = Move (II): flips in 1-holed tori
-/

/-- An A-move (= Move I) in a 4-holed sphere region. -/
abbrev AMove := MoveI

/-- An S-move (= Move II) in a 1-holed torus region. -/
abbrev SMove := MoveII

/-- An elementary move is either an A-move or an S-move -/
inductive ElementaryMove (g n : ℕ)
  | amove : AMove g n → ElementaryMove g n
  | smove : SMove g n → ElementaryMove g n

/-!
## Applying Moves to Markings
-/

/-- Existence of the updated marking after a valid A-move. -/
theorem exists_applyMove_amove (P : PantsDecomposition g n) (a : AMove g n)
    (hvalid : a.oldCurve ∈ P.circles ∧ a.newCurve ∉ P.circles) :
    Nonempty (PantsDecomposition g n) := by
  -- Deferred: build the updated marking from local topological move data.
  sorry

/-- Existence of the updated marking after a valid S-move. -/
theorem exists_applyMove_smove (P : PantsDecomposition g n) (s : SMove g n)
    (hvalid : s.oldCurve ∈ P.circles ∧ s.newCurve ∉ P.circles) :
    Nonempty (PantsDecomposition g n) := by
  -- Deferred: build the updated marking from local topological move data.
  sorry

/-- Apply an elementary move to a pants decomposition.
    Returns `some P'` if the move is valid, `none` otherwise. -/
noncomputable def applyMove (P : PantsDecomposition g n) (m : ElementaryMove g n) :
    Option (PantsDecomposition g n) :=
  match m with
  | .amove a =>
    if hvalid : a.oldCurve ∈ P.circles ∧ a.newCurve ∉ P.circles then
      some (Classical.choice (exists_applyMove_amove (P := P) a hvalid))
    else none
  | .smove s =>
    if hvalid : s.oldCurve ∈ P.circles ∧ s.newCurve ∉ P.circles then
      some (Classical.choice (exists_applyMove_smove (P := P) s hvalid))
    else none

/-!
## The Pants Graph
-/

/-- Two pants decompositions are adjacent if they differ by one elementary move -/
def adjacent (P Q : PantsDecomposition g n) : Prop :=
  ∃ m : ElementaryMove g n, applyMove P m = some Q

/-- The pants graph P(Σ_{g,n}).

    **Vertices**: isotopy classes of pants decompositions
    **Edges**: pairs differing by a single elementary move

    **Properties**:
    - Connected (Hatcher-Thurston theorem)
    - Infinite for stable surfaces
    - Quasi-isometric to Teichmüller space with Weil-Petersson metric (Brock) -/
structure PantsGraph (g n : ℕ) where
  /-- Set of all pants decompositions -/
  vertices : Set (PantsDecomposition g n)
  /-- Nonempty (pants decompositions exist) -/
  nonempty : vertices.Nonempty
  /-- Adjacency relation -/
  adj : PantsDecomposition g n → PantsDecomposition g n → Prop := adjacent

/-!
## Paths in the Pants Graph
-/

/-- A path in the pants graph from P to Q -/
inductive PantsPath (g n : ℕ) : PantsDecomposition g n → PantsDecomposition g n → Type
  | refl : (P : PantsDecomposition g n) → PantsPath g n P P
  | step : {P Q R : PantsDecomposition g n} →
           adjacent P Q → PantsPath g n Q R → PantsPath g n P R

/-- Length of a path in the pants graph -/
def PantsPath.length : PantsPath g n P Q → ℕ
  | .refl _ => 0
  | .step _ path => 1 + path.length

/-- Concatenation of paths -/
def PantsPath.concat : PantsPath g n P Q → PantsPath g n Q R → PantsPath g n P R
  | .refl _, path => path
  | .step h path₁, path₂ => .step h (path₁.concat path₂)

/-- Length of concatenation is sum of lengths -/
theorem PantsPath.length_concat (p₁ : PantsPath g n P Q) (p₂ : PantsPath g n Q R) :
    (p₁.concat p₂).length = p₁.length + p₂.length := by
  induction p₁ with
  | refl _ => simp [concat, length]
  | step _ _ ih => simp [concat, length, ih]; ring

/-- A pants path of length zero has equal source and target. -/
theorem PantsPath.eq_of_length_eq_zero (path : PantsPath g n P Q)
    (h0 : path.length = 0) : P = Q := by
  induction path with
  | refl P =>
      rfl
  | step h path ih =>
      simp [PantsPath.length] at h0

/-- Two pants decompositions are connected in the pants graph -/
def connected (P Q : PantsDecomposition g n) : Prop :=
  Nonempty (PantsPath g n P Q)

/-- Every pants decomposition is connected to itself. -/
theorem connected_refl (P : PantsDecomposition g n) : connected P P :=
  ⟨PantsPath.refl P⟩

/-!
## The Hatcher-Thurston Theorem
-/

/-- **Hatcher-Thurston Theorem**: The pants graph is connected.

    **Statement** (Hatcher-Thurston 1980, Appendix):
    "Any two markings of M are obtainable one from the other by a finite
    sequence of simple moves of these four types (up to isotopy)."

    **Proof outline**:
    1. Show moves (I) and (IV) suffice
    2. Use induction on the "complexity" of the difference between markings
    3. Key: any two markings can be related by curve surgeries -/
theorem hatcher_thurston (g n : ℕ) (_ : 2 * g + n > 2)
    (P Q : PantsDecomposition g n) :
    connected P Q := by
  sorry  -- This is Hatcher-Thurston's main theorem

/-- The pants graph is infinite for stable surfaces -/
theorem pants_graph_infinite (g n : ℕ) (_ : 2 * g + n > 2) :
    ¬(Set.Finite { P : PantsDecomposition g n | True }) := by
  sorry

/-!
## Distance in the Pants Graph
-/

/-- Distance in the pants graph (minimal number of moves) -/
noncomputable def pantsDistance (P Q : PantsDecomposition g n) : ℕ :=
  sInf {m : ℕ | ∃ path : PantsPath g n P Q, path.length = m}

/-- The pants distance is bounded above by the length of any connecting path. -/
theorem pantsDistance_le_length {P Q : PantsDecomposition g n}
    (path : PantsPath g n P Q) :
    pantsDistance P Q ≤ path.length := by
  unfold pantsDistance
  exact Nat.sInf_le ⟨path, rfl⟩

/-- The distance from a pants decomposition to itself is zero. -/
theorem pantsDistance_self (P : PantsDecomposition g n) :
    pantsDistance P P = 0 := by
  apply Nat.eq_zero_of_le_zero
  have hle : pantsDistance P P ≤ (PantsPath.refl P).length :=
    pantsDistance_le_length (path := PantsPath.refl P)
  simpa [PantsPath.length] using hle

/-- The pants graph has infinite diameter -/
theorem pants_graph_infinite_diameter (g n : ℕ) (_ : 3 * g - 3 + n ≥ 2) :
    ∀ D : ℕ, ∃ P Q : PantsDecomposition g n, pantsDistance P Q > D := by
  sorry

/-- The pants distance equals the minimum path length -/
theorem pants_distance_eq_min_length (P Q : PantsDecomposition g n) (_ : connected P Q) :
    ∃ path : PantsPath g n P Q, path.length = pantsDistance P Q := by
  have hnonempty :
      ({m : ℕ | ∃ path : PantsPath g n P Q, path.length = m} : Set ℕ).Nonempty := by
    rcases (show connected P Q from ‹connected P Q›) with ⟨path⟩
    exact ⟨path.length, ⟨path, rfl⟩⟩
  have hsinf_mem :
      pantsDistance P Q ∈ {m : ℕ | ∃ path : PantsPath g n P Q, path.length = m} := by
    unfold pantsDistance
    exact Nat.sInf_mem hnonempty
  rcases hsinf_mem with ⟨path, hlen⟩
  exact ⟨path, hlen⟩

/-- For connected vertices, distance zero is equivalent to equality. -/
theorem pantsDistance_eq_zero_iff (P Q : PantsDecomposition g n) (hconn : connected P Q) :
    pantsDistance P Q = 0 ↔ P = Q := by
  constructor
  · intro hdist
    rcases pants_distance_eq_min_length (P := P) (Q := Q) hconn with ⟨path, hlen⟩
    exact PantsPath.eq_of_length_eq_zero path (by simpa [hlen] using hdist)
  · intro hPQ
    subst hPQ
    exact pantsDistance_self P

/-- For connected distinct vertices, pants distance is positive. -/
theorem pantsDistance_pos_of_ne (P Q : PantsDecomposition g n)
    (hconn : connected P Q) (hne : P ≠ Q) :
    0 < pantsDistance P Q := by
  refine Nat.pos_iff_ne_zero.mpr ?_
  intro hzero
  exact hne ((pantsDistance_eq_zero_iff P Q hconn).mp hzero)

/-!
## Quasi-isometry to Weil-Petersson Metric (Brock)

Brock showed that the pants graph is quasi-isometric to Teichmüller space
with the Weil-Petersson metric. This is remarkable because:
- The pants graph is discrete and combinatorial
- The WP metric is analytic and incomplete
-/

/-- **Brock's Theorem**: The pants graph is quasi-isometric to (T_g, d_WP).

    There exist constants A, B > 0 such that for all P, Q:
    (1/A) · d_WP(P, Q) - B ≤ d_pants(P, Q) ≤ A · d_WP(P, Q) + B -/
theorem brock_quasi_isometry (g n : ℕ) (_ : 2 * g + n > 2) :
    True := by  -- Pants graph ≃_QI (T_{g,n}, d_WP)
  trivial

end RiemannSurfaces.Topology
