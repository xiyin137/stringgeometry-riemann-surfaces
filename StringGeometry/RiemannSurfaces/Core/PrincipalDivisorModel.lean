import StringGeometry.RiemannSurfaces.Core.DivisorModel
import Mathlib.Algebra.Group.Defs

/-!
# Core Principal Divisor and Linear Equivalence Interfaces

This file extends `DivisorModel` with model-agnostic contracts for:
- principal divisors
- linear equivalence (difference by a principal divisor)

The intent is to centralize these concepts for analytic/algebraic/scheme adapters.
-/

namespace RiemannSurfaces.Core

/-- A divisor model equipped with a distinguished subgroup of principal divisors. -/
class PrincipalDivisorModel (Point Divisor : Type*) [AddGroup Divisor]
    [DivisorModel Point Divisor] where
  IsPrincipal : Divisor → Prop
  zero_isPrincipal : IsPrincipal 0
  add_isPrincipal : ∀ {D₁ D₂ : Divisor}, IsPrincipal D₁ → IsPrincipal D₂ → IsPrincipal (D₁ + D₂)
  neg_isPrincipal : ∀ {D : Divisor}, IsPrincipal D → IsPrincipal (-D)

namespace PrincipalDivisorModel

variable {Point Divisor : Type*}
variable [AddGroup Divisor] [DivisorModel Point Divisor]
variable [PrincipalDivisorModel Point Divisor]

/-- Core linear equivalence relation: `D₁ ~ D₂` iff `D₁ - D₂` is principal.
We use `D₁ + (-D₂)` to avoid additional `Sub` assumptions. -/
def LinearlyEquivalent (D₁ D₂ : Divisor) : Prop :=
  PrincipalDivisorModel.IsPrincipal (Point := Point) (Divisor := Divisor) (D₁ + -D₂)

@[refl] theorem linearlyEquivalent_refl (D : Divisor) :
    LinearlyEquivalent (Point := Point) (Divisor := Divisor) D D := by
  unfold LinearlyEquivalent
  simpa using
    (PrincipalDivisorModel.zero_isPrincipal (Point := Point) (Divisor := Divisor))

@[symm] theorem linearlyEquivalent_symm {D₁ D₂ : Divisor}
    (h : LinearlyEquivalent (Point := Point) (Divisor := Divisor) D₁ D₂) :
    LinearlyEquivalent (Point := Point) (Divisor := Divisor) D₂ D₁ := by
  unfold LinearlyEquivalent at h ⊢
  have hneg := PrincipalDivisorModel.neg_isPrincipal (Point := Point) (Divisor := Divisor) h
  simpa [add_assoc, add_comm] using hneg

@[trans] theorem linearlyEquivalent_trans {D₁ D₂ D₃ : Divisor}
    (h₁₂ : LinearlyEquivalent (Point := Point) (Divisor := Divisor) D₁ D₂)
    (h₂₃ : LinearlyEquivalent (Point := Point) (Divisor := Divisor) D₂ D₃) :
    LinearlyEquivalent (Point := Point) (Divisor := Divisor) D₁ D₃ := by
  unfold LinearlyEquivalent at h₁₂ h₂₃ ⊢
  have hsum := PrincipalDivisorModel.add_isPrincipal (Point := Point) (Divisor := Divisor) h₁₂ h₂₃
  simpa [add_assoc, add_comm] using hsum

/-- Core setoid for divisor linear equivalence. -/
def linearlyEquivalentSetoid : Setoid Divisor where
  r := LinearlyEquivalent (Point := Point) (Divisor := Divisor)
  iseqv :=
    ⟨linearlyEquivalent_refl (Point := Point) (Divisor := Divisor),
      linearlyEquivalent_symm (Point := Point) (Divisor := Divisor),
      linearlyEquivalent_trans (Point := Point) (Divisor := Divisor)⟩

end PrincipalDivisorModel

/-- Transport contract for principal divisors on top of a divisor transport. -/
structure PrincipalDivisorTransport
    (Point D₁ D₂ : Type*)
    [AddGroup D₁] [DivisorModel Point D₁] [PrincipalDivisorModel Point D₁]
    [AddGroup D₂] [DivisorModel Point D₂] [PrincipalDivisorModel Point D₂]
    (T : DivisorTransport Point D₁ D₂) where
  map_isPrincipal : ∀ {D : D₁},
    PrincipalDivisorModel.IsPrincipal (Point := Point) (Divisor := D₁) D →
      PrincipalDivisorModel.IsPrincipal (Point := Point) (Divisor := D₂) (T.toFun D)
  inv_isPrincipal : ∀ {D : D₂},
    PrincipalDivisorModel.IsPrincipal (Point := Point) (Divisor := D₂) D →
      PrincipalDivisorModel.IsPrincipal (Point := Point) (Divisor := D₁) (T.invFun D)

namespace PrincipalDivisorTransport

variable {Point D₁ D₂ : Type*}
variable [AddGroup D₁] [DivisorModel Point D₁] [PrincipalDivisorModel Point D₁]
variable [AddGroup D₂] [DivisorModel Point D₂] [PrincipalDivisorModel Point D₂]
variable {T : DivisorTransport Point D₁ D₂}

/-- Principal transport preserves linear equivalence in the forward direction. -/
theorem map_linearlyEquivalent
    (P : PrincipalDivisorTransport Point D₁ D₂ T)
    {A B : D₁}
    (hAB : PrincipalDivisorModel.LinearlyEquivalent (Point := Point) (Divisor := D₁) A B) :
    PrincipalDivisorModel.LinearlyEquivalent (Point := Point) (Divisor := D₂) (T.toFun A) (T.toFun B) := by
  unfold PrincipalDivisorModel.LinearlyEquivalent at hAB ⊢
  have hmap := P.map_isPrincipal hAB
  simpa [T.map_add, T.map_neg] using hmap

end PrincipalDivisorTransport

end RiemannSurfaces.Core
