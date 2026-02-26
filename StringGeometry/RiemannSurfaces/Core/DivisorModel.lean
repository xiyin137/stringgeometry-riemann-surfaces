import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Core Divisor Model Interfaces

This file provides shared interfaces for divisor-like objects used across
analytic, algebraic, and scheme-theoretic developments.

The goal is to separate:
- model-independent algebraic contracts (here)
- model-specific implementations (adapter files)
- inter-model transport data (bridge structures)
-/

namespace RiemannSurfaces.Core

/-- A model of divisors indexed by a point type.

This class captures the core API expected by GAGA bridges and common proofs,
without forcing a particular implementation choice for divisors. -/
class DivisorModel (Point Divisor : Type*) [Zero Divisor] [Add Divisor] [Neg Divisor] where
  coeff : Divisor → Point → ℤ
  finiteSupport : ∀ D : Divisor, Set.Finite { p : Point | coeff D p ≠ 0 }
  degree : Divisor → ℤ
  point : Point → Divisor
  coeff_zero : ∀ p : Point, coeff (0 : Divisor) p = 0
  coeff_add : ∀ D₁ D₂ : Divisor, ∀ p : Point, coeff (D₁ + D₂) p = coeff D₁ p + coeff D₂ p
  coeff_neg : ∀ D : Divisor, ∀ p : Point, coeff (-D) p = -coeff D p
  degree_zero : degree (0 : Divisor) = 0
  degree_add : ∀ D₁ D₂ : Divisor, degree (D₁ + D₂) = degree D₁ + degree D₂
  degree_neg : ∀ D : Divisor, degree (-D) = -degree D
  degree_point : ∀ p : Point, degree (point p) = 1

namespace DivisorModel

variable {Point Divisor : Type*} [Zero Divisor] [Add Divisor] [Neg Divisor]
variable [DivisorModel Point Divisor]

/-- Core-level support set of a divisor. -/
def support (D : Divisor) : Set Point :=
  { p : Point | DivisorModel.coeff (Point := Point) (Divisor := Divisor) D p ≠ 0 }

/-- Support is finite in every model implementing `DivisorModel`. -/
theorem support_finite (D : Divisor) :
    Set.Finite (support (Point := Point) (Divisor := Divisor) D) :=
  DivisorModel.finiteSupport (Point := Point) (Divisor := Divisor) D

@[simp] theorem coeff_zero_eq (p : Point) :
    DivisorModel.coeff (Point := Point) (Divisor := Divisor) (0 : Divisor) p = 0 :=
  DivisorModel.coeff_zero (Point := Point) (Divisor := Divisor) p

@[simp] theorem coeff_add_eq (D₁ D₂ : Divisor) (p : Point) :
    DivisorModel.coeff (Point := Point) (Divisor := Divisor) (D₁ + D₂) p =
      DivisorModel.coeff (Point := Point) (Divisor := Divisor) D₁ p +
      DivisorModel.coeff (Point := Point) (Divisor := Divisor) D₂ p :=
  DivisorModel.coeff_add (Point := Point) (Divisor := Divisor) D₁ D₂ p

@[simp] theorem coeff_neg_eq (D : Divisor) (p : Point) :
    DivisorModel.coeff (Point := Point) (Divisor := Divisor) (-D) p =
      -DivisorModel.coeff (Point := Point) (Divisor := Divisor) D p :=
  DivisorModel.coeff_neg (Point := Point) (Divisor := Divisor) D p

@[simp] theorem degree_zero_eq :
    DivisorModel.degree (Point := Point) (Divisor := Divisor) (0 : Divisor) = 0 :=
  DivisorModel.degree_zero (Point := Point) (Divisor := Divisor)

@[simp] theorem degree_add_eq (D₁ D₂ : Divisor) :
    DivisorModel.degree (Point := Point) (Divisor := Divisor) (D₁ + D₂) =
      DivisorModel.degree (Point := Point) (Divisor := Divisor) D₁ +
      DivisorModel.degree (Point := Point) (Divisor := Divisor) D₂ :=
  DivisorModel.degree_add (Point := Point) (Divisor := Divisor) D₁ D₂

@[simp] theorem degree_neg_eq (D : Divisor) :
    DivisorModel.degree (Point := Point) (Divisor := Divisor) (-D) =
      -DivisorModel.degree (Point := Point) (Divisor := Divisor) D :=
  DivisorModel.degree_neg (Point := Point) (Divisor := Divisor) D

@[simp] theorem degree_point_eq (p : Point) :
    DivisorModel.degree (Point := Point) (Divisor := Divisor)
      (DivisorModel.point (Point := Point) (Divisor := Divisor) p : Divisor) = 1 :=
  DivisorModel.degree_point (Point := Point) (Divisor := Divisor) p

end DivisorModel

/-- Explicit transport contract between two divisor implementations over the
same point type.

The structure is intentionally concrete: instead of postulating abstract
category-level equivalence, we require executable maps and preservation facts
needed downstream (coefficients and degree). -/
structure DivisorTransport
    (Point D₁ D₂ : Type*)
    [Zero D₁] [Add D₁] [Neg D₁] [DivisorModel Point D₁]
    [Zero D₂] [Add D₂] [Neg D₂] [DivisorModel Point D₂] where
  toFun : D₁ → D₂
  invFun : D₂ → D₁
  left_inv : Function.LeftInverse invFun toFun
  right_inv : Function.RightInverse invFun toFun
  map_zero : toFun 0 = 0
  map_add : ∀ a b : D₁, toFun (a + b) = toFun a + toFun b
  map_neg : ∀ a : D₁, toFun (-a) = -toFun a
  map_point : ∀ p : Point, toFun (DivisorModel.point p : D₁) = (DivisorModel.point p : D₂)
  map_coeff : ∀ a : D₁, ∀ p : Point,
    DivisorModel.coeff (Point := Point) (Divisor := D₂) (toFun a) p =
      DivisorModel.coeff (Point := Point) (Divisor := D₁) a p
  map_degree : ∀ a : D₁,
    DivisorModel.degree (Point := Point) (Divisor := D₂) (toFun a) =
      DivisorModel.degree (Point := Point) (Divisor := D₁) a

namespace DivisorTransport

variable {Point D₁ D₂ : Type*}
variable [Zero D₁] [Add D₁] [Neg D₁] [DivisorModel Point D₁]
variable [Zero D₂] [Add D₂] [Neg D₂] [DivisorModel Point D₂]

/-- The transport viewed as an equivalence of underlying types. -/
def toEquiv (T : DivisorTransport Point D₁ D₂) : D₁ ≃ D₂ where
  toFun := T.toFun
  invFun := T.invFun
  left_inv := T.left_inv
  right_inv := T.right_inv

@[simp] theorem map_sub (T : DivisorTransport Point D₁ D₂) [Sub D₁] [Sub D₂]
    (hsub₁ : ∀ a b : D₁, a - b = a + -b)
    (hsub₂ : ∀ a b : D₂, a - b = a + -b)
    (a b : D₁) :
    T.toFun (a - b) = T.toFun a - T.toFun b := by
  rw [hsub₁, hsub₂, T.map_add, T.map_neg]

end DivisorTransport

end RiemannSurfaces.Core
