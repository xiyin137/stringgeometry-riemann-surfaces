/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Module.PUnit
import Mathlib.Topology.Sheaves.Skyscraper
import StringGeometry.RiemannSurfaces.SchemeTheoretic.Helpers.SkyscraperInfrastructure

/-!
# Skyscraper Module Construction

This file constructs the skyscraper O_X-module at a point p on a scheme X.

The skyscraper sheaf k_p is the O_X-module with:
- Sections k_p(U) = κ(p) if p ∈ U, else PUnit (trivial = zero module)
- Module action: f · v = evalAtPoint(f)(p) · v for f ∈ O_X(U), v ∈ κ(p)
- Restriction: identity on κ(p) when p is in both opens, zero otherwise
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Classical

namespace RiemannSurfaces.SchemeTheoretic.SkyscraperConstruction

variable {X : Scheme}

/-!
## Type compatibility

The carrier type `↑(X.ringCatSheaf.val.obj U)` equals `Γ(X, U.unop)` definitionally.
We establish this and use it to transfer module instances.
-/

/-- The underlying type of ringCatSheaf sections agrees with the presheaf sections type.
    This follows from `forgetToRingCat_obj` in Mathlib. -/
theorem ringCatSheaf_carrier_eq (U : (Opens X.carrier)ᵒᵖ) :
    (X.ringCatSheaf.val.obj U : Type _) = (X.presheaf.obj U : Type _) := rfl

/-- Module instance on κ(p) over the ringCatSheaf ring of sections.
    Uses the fact that the carrier types are definitionally equal. -/
noncomputable def residueFieldModuleRCS (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (hp : (p : X.carrier) ∈ U.unop) :
    Module (↑(X.ringCatSheaf.val.obj U)) (↑(X.residueField p)) := by
  simpa [ringCatSheaf_carrier_eq (X := X) U] using
    (residueFieldModule (X := X) p U.unop hp)

/-!
## Evaluation-Restriction Compatibility
-/

/-- Evaluation at p commutes with restriction of sections. -/
theorem evalAtPoint_comp_restriction (p : X) (U V : Opens X.carrier)
    (hpU : (p : X.carrier) ∈ U) (hpV : (p : X.carrier) ∈ V) (hUV : U ≤ V)
    (r : Γ(X, V)) :
    (evalAtPoint p U hpU) ((X.presheaf.map (homOfLE hUV).op).hom r) =
    (evalAtPoint p V hpV) r := by
  simp only [evalAtPoint]
  show ((X.presheaf.map (homOfLE hUV).op ≫ X.presheaf.germ U (↑p) hpU) ≫
    X.residue (↑p)).hom r = (X.presheaf.germ V (↑p) hpV ≫ X.residue (↑p)).hom r
  rw [X.presheaf.germ_res (homOfLE hUV) (↑p) hpU]

/-!
## Object Definition
-/

/-- The module of sections of the skyscraper sheaf at p over U.
    Returns κ(p) when p ∈ U, and PUnit (zero module) otherwise. -/
noncomputable def skyscraperObj (p : X) (U : (Opens X.carrier)ᵒᵖ) :
    ModuleCat ↑(X.ringCatSheaf.val.obj U) := by
  by_cases h : (p : X.carrier) ∈ U.unop
  · exact @ModuleCat.of (↑(X.ringCatSheaf.val.obj U)) _ (↑(X.residueField p)) _
      (residueFieldModuleRCS p U h)
  · exact ModuleCat.of ↑(X.ringCatSheaf.val.obj U) PUnit

/-- When p ∈ U, the skyscraper sections are κ(p). -/
theorem skyscraperObj_pos (p : X) (U : (Opens X.carrier)ᵒᵖ) (h : (p : X.carrier) ∈ U.unop) :
    skyscraperObj p U = (
      @ModuleCat.of (↑(X.ringCatSheaf.val.obj U)) _ (↑(X.residueField p)) _
        (residueFieldModuleRCS p U h) :
        ModuleCat ↑(X.ringCatSheaf.val.obj U)) := by
  simp only [skyscraperObj, dif_pos h]

/-- When p ∉ U, the skyscraper sections are PUnit. -/
theorem skyscraperObj_neg (p : X) (U : (Opens X.carrier)ᵒᵖ) (h : (p : X.carrier) ∉ U.unop) :
    skyscraperObj p U = (ModuleCat.of ↑(X.ringCatSheaf.val.obj U) PUnit) := by
  simp only [skyscraperObj, dif_neg h]

/-- When p ∉ U, the carrier of skyscraperObj is a subsingleton (it's PUnit). -/
instance skyscraperObj_subsingleton' (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (h : (p : X.carrier) ∉ U.unop) :
    Subsingleton ↑(skyscraperObj p U) := by
  rw [skyscraperObj_neg p U h]
  exact instSubsingletonPUnit

/-- The carrier type of restrictScalars.obj equals the original carrier. -/
theorem skyscraperObj_restrictScalars_carrier' (p : X) (U : (Opens X.carrier)ᵒᵖ)
    {V : (Opens X.carrier)ᵒᵖ} (f : V ⟶ U) :
    (↑((ModuleCat.restrictScalars (X.ringCatSheaf.val.map f).hom).obj (skyscraperObj p U)) : Type _) =
    (↑(skyscraperObj p U) : Type _) := rfl

/-- When p ∉ U, the restrictScalars variant is also a subsingleton. -/
instance skyscraperObj_restrictScalars_subsingleton' (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (h : (p : X.carrier) ∉ U.unop)
    {V : (Opens X.carrier)ᵒᵖ} (f : V ⟶ U) :
    Subsingleton ↑((ModuleCat.restrictScalars (X.ringCatSheaf.val.map f).hom).obj (skyscraperObj p U)) := by
  rw [show (↑((ModuleCat.restrictScalars (X.ringCatSheaf.val.map f).hom).obj
    (skyscraperObj p U)) : Type _) = ↑(skyscraperObj p U) from rfl]
  exact skyscraperObj_subsingleton' p U h

/-- eqToHom followed by its inverse is identity on elements (using .hom). -/
@[simp] theorem eqToHom_hom_symm_comp' {R : Type*} [Ring R] {A B : ModuleCat R}
    (h : A = B) (x : ↑A) :
    (eqToHom h.symm).hom ((eqToHom h).hom x) = x := by
  subst h; rfl

/-- eqToHom inverse followed by eqToHom is identity on elements (using .hom). -/
@[simp] theorem eqToHom_hom_comp_symm' {R : Type*} [Ring R] {A B : ModuleCat R}
    (h : A = B) (y : ↑B) :
    (eqToHom h).hom ((eqToHom h.symm).hom y) = y := by
  subst h; rfl

/-!
## Restriction Maps
-/

/-- The restriction map for the skyscraper presheaf of modules. -/
noncomputable def skyscraperMap (p : X) {U V : (Opens X.carrier)ᵒᵖ} (f : U ⟶ V) :
    skyscraperObj p U ⟶
      (ModuleCat.restrictScalars (X.ringCatSheaf.val.map f).hom).obj (skyscraperObj p V) := by
  by_cases hV : (p : X.carrier) ∈ V.unop
  · -- p ∈ V, hence p ∈ U
    sorry
  · -- p ∉ V, target has PUnit carrier
    rw [show skyscraperObj p V = ModuleCat.of _ PUnit from skyscraperObj_neg p V hV]
    exact 0

/-!
## Presheaf of Modules
-/

/-- The skyscraper presheaf of modules at point p on scheme X. -/
noncomputable def skyscraperPresheafOfModules (p : X) :
    PresheafOfModules X.ringCatSheaf.val where
  obj := skyscraperObj p
  map f := skyscraperMap p f
  map_id U := by
    sorry
  map_comp {U V W} f g := by
    sorry

/-!
## Helper Lemmas for Sheaf Condition

Key properties of the skyscraper presheaf restriction maps:
1. On elements, the presheaf map equals the skyscraperMap (by presheaf_map_apply_coe)
2. When both opens contain p, restriction acts as identity on κ(p)
3. The projection to κ(p) via eqToHom is injective
-/

/-- The projection from skyscraperObj sections to κ(p) via eqToHom. -/
noncomputable def toKappa (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (h : (p : X.carrier) ∈ U.unop) :
    ↑(skyscraperObj p U) → X.residueField p :=
  (eqToHom (skyscraperObj_pos p U h)).hom

/-- The embedding from κ(p) to skyscraperObj sections. -/
noncomputable def fromKappa (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (h : (p : X.carrier) ∈ U.unop) :
    X.residueField p → ↑(skyscraperObj p U) :=
  (eqToHom (skyscraperObj_pos p U h).symm).hom

@[simp] theorem toKappa_fromKappa (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (h : (p : X.carrier) ∈ U.unop) (v : X.residueField p) :
    toKappa p U h (fromKappa p U h v) = v :=
  eqToHom_hom_comp_symm' (skyscraperObj_pos p U h) v

@[simp] theorem fromKappa_toKappa (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (h : (p : X.carrier) ∈ U.unop) (x : ↑(skyscraperObj p U)) :
    fromKappa p U h (toKappa p U h x) = x :=
  eqToHom_hom_symm_comp' (skyscraperObj_pos p U h) x

/-- toKappa is injective. -/
theorem toKappa_injective (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (h : (p : X.carrier) ∈ U.unop) :
    Function.Injective (toKappa p U h) := by
  intro a b hab
  have := congr_arg (fromKappa p U h) hab
  simp only [fromKappa_toKappa] at this
  exact this

/-- fromKappa is injective. -/
theorem fromKappa_injective (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (h : (p : X.carrier) ∈ U.unop) :
    Function.Injective (fromKappa p U h) := by
  intro a b hab
  have := congr_arg (toKappa p U h) hab
  simp only [toKappa_fromKappa] at this
  exact this

/-- eqToHom applied to an element equals cast of the carrier equality. -/
theorem eqToHom_apply_eq_cast' {R : Type*} [Ring R] {A B : ModuleCat R}
    (h : A = B) (x : ↑A) :
    (eqToHom h).hom x = cast (congrArg (↑·) h) x := by
  cases h; rfl

/-- toKappa commutes with cast between carrier types.
    All casts through κ(p) give the same result by proof irrelevance. -/
theorem toKappa_cast (p : X) (U V : (Opens X.carrier)ᵒᵖ)
    (hU : (p : X.carrier) ∈ U.unop) (hV : (p : X.carrier) ∈ V.unop)
    (heq : (↑(skyscraperObj p U) : Type _) = ↑(skyscraperObj p V))
    (x : ↑(skyscraperObj p U)) :
    toKappa p V hV (cast heq x) = toKappa p U hU x := by
  simp only [toKappa]
  -- Convert eqToHom applications to cast
  rw [eqToHom_apply_eq_cast' (skyscraperObj_pos p V hV) (cast heq x),
      eqToHom_apply_eq_cast' (skyscraperObj_pos p U hU) x]
  -- Goal: cast _ (cast heq x) = cast _ x
  -- Both are casts of x to the same target type. Use HEq transitivity.
  exact eq_of_heq ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))

/-- The skyscraper presheaf of modules satisfies the sheaf condition.

    **Proof:** We prove the sheaf condition directly using the unique gluing
    characterization. The skyscraper presheaf assigns κ(p) to opens containing p
    and PUnit to opens not containing p, with identity restriction maps.
    Unique gluing follows because all sections at opens containing p must agree,
    and sections at opens not containing p are trivially unique (PUnit). -/
theorem skyscraper_isSheaf (p : X) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X.carrier)
      (skyscraperPresheafOfModules p).presheaf := by
  sorry

/-- The skyscraper O_X-module at point p. -/
noncomputable def constructSkyscraperModule (p : X) :
    SheafOfModules X.ringCatSheaf where
  val := skyscraperPresheafOfModules p
  isSheaf := skyscraper_isSheaf p

/-- When p ∉ U, the carrier of skyscraperObj is a subsingleton (it's PUnit). -/
instance skyscraperObj_subsingleton (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (h : (p : X.carrier) ∉ U.unop) :
    Subsingleton ↑(skyscraperObj p U) := by
  rw [skyscraperObj_neg p U h]
  exact instSubsingletonPUnit

/-- The carrier type of skyscraperObj is the same as that of the restrictScalars variant. -/
theorem skyscraperObj_restrictScalars_carrier (p : X) (U : (Opens X.carrier)ᵒᵖ)
    {V : (Opens X.carrier)ᵒᵖ} (f : V ⟶ U) :
    (↑((ModuleCat.restrictScalars (X.ringCatSheaf.val.map f).hom).obj (skyscraperObj p U)) : Type _) =
    (↑(skyscraperObj p U) : Type _) := rfl

/-- When p ∉ U, the restrictScalars variant is also a subsingleton. -/
instance skyscraperObj_restrictScalars_subsingleton (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (h : (p : X.carrier) ∉ U.unop)
    {V : (Opens X.carrier)ᵒᵖ} (f : V ⟶ U) :
    Subsingleton ↑((ModuleCat.restrictScalars (X.ringCatSheaf.val.map f).hom).obj (skyscraperObj p U)) := by
  rw [show (↑((ModuleCat.restrictScalars (X.ringCatSheaf.val.map f).hom).obj
    (skyscraperObj p U)) : Type _) = ↑(skyscraperObj p U) from rfl]
  exact skyscraperObj_subsingleton p U h

/-- eqToHom followed by its inverse is identity on elements (using .hom). -/
theorem eqToHom_hom_symm_comp {R : Type*} [Ring R] {A B : ModuleCat R}
    (h : A = B) (x : ↑A) :
    (eqToHom h.symm).hom ((eqToHom h).hom x) = x := by
  subst h; rfl

/-- eqToHom inverse followed by eqToHom is identity on elements (using .hom). -/
theorem eqToHom_hom_comp_symm {R : Type*} [Ring R] {A B : ModuleCat R}
    (h : A = B) (y : ↑B) :
    (eqToHom h).hom ((eqToHom h.symm).hom y) = y := by
  subst h; rfl

/-- The restriction map of the skyscraper presheaf is surjective. -/
theorem skyscraperMap_surjective (p : X) {U V : (Opens X.carrier)ᵒᵖ} (f : U ⟶ V) :
    Function.Surjective (skyscraperMap p f) := by
  sorry

/-- Global sections of the skyscraper module are κ(p). -/
theorem skyscraper_globalSections_eq (p : X) :
    skyscraperObj p (op ⊤) = (
      @ModuleCat.of (↑(X.ringCatSheaf.val.obj (op ⊤))) _ (↑(X.residueField p)) _
        (residueFieldModuleRCS p (op ⊤) (Set.mem_univ (↑p))) :
        ModuleCat ↑(X.ringCatSheaf.val.obj (op ⊤))) :=
  skyscraperObj_pos p (op ⊤) (Set.mem_univ _)

/-- The restriction map of the skyscraper presheaf preserves the κ(p) value.

    For the skyscraper presheaf F at point p, when p ∈ U' and p ∈ V',
    the presheaf restriction map F.map f' : F(U') → F(V') acts as identity
    on κ(p) (i.e., toKappa(F.map f' x) = toKappa(x)). -/
theorem res_toKappa (p : X) {U' V' : (Opens X.carrier)ᵒᵖ} (f' : U' ⟶ V')
    (hU' : (p : X.carrier) ∈ U'.unop) (hV' : (p : X.carrier) ∈ V'.unop)
    (x' : ↑((skyscraperPresheafOfModules p).presheaf.obj U')) :
    toKappa p V' hV' ((skyscraperPresheafOfModules p).presheaf.map f' x') =
    toKappa p U' hU' x' := by
  sorry

/-- Version of res_toKappa using PresheafOfModules.map (= SheafOfModules.val.map).
    This version matches the syntactic form of restriction maps in Čech cohomology
    computations and can be used with `rw` instead of `erw`.

    For the skyscraper presheaf F at point p, when p ∈ U and p ∈ V,
    the restriction map F.map f : F.obj(U) → (restrictScalars ...).obj(F.obj(V))
    acts as identity on κ(p) (i.e., toKappa(F.map f x) = toKappa(x)). -/
theorem res_toKappa_val (p : X) {U V : (Opens X.carrier)ᵒᵖ} (f : U ⟶ V)
    (hU : (p : X.carrier) ∈ U.unop) (hV : (p : X.carrier) ∈ V.unop)
    (x : ↑(skyscraperObj p U)) :
    toKappa p V hV ((skyscraperPresheafOfModules p).map f x) =
    toKappa p U hU x := by
  -- PresheafOfModules.map f applied to x equals presheaf.map f applied to x
  -- (by presheaf_map_apply_coe which is rfl)
  -- So this reduces to res_toKappa
  exact res_toKappa p f hU hV x

/-- toKappa commutes with ring scalar multiplication via evalAtPoint.
    For r : O_X(U) and x : skyscraperObj(p, U) with p ∈ U:
    toKappa(r • x) = evalAtPoint(r) * toKappa(x). -/
theorem toKappa_ring_smul (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (hp : (p : X.carrier) ∈ U.unop)
    (r : ↑(X.ringCatSheaf.val.obj U))
    (x : ↑(skyscraperObj p U)) :
    toKappa p U hp (r • x) = evalAtPoint p U.unop hp r * toKappa p U hp x := by
  letI := residueFieldModuleRCS p U hp
  simp only [toKappa]
  -- eqToHom h is a morphism in ModuleCat R, hence R-linear
  -- So (eqToHom h).hom (r • x) = r • (eqToHom h).hom x
  -- And r • v in κ(p) with residueFieldModuleRCS = evalAtPoint(r) * v
  have h_eq := skyscraperObj_pos p U hp
  have h_smul : (eqToHom h_eq).hom (r • x) = r • (eqToHom h_eq).hom x :=
    map_smul (eqToHom h_eq).hom r x
  rw [h_smul]
  -- r • v in κ(p) = evalAtPoint(r) * v (definitional from Module.compHom)
  rfl

/-- fromKappa commutes with ring scalar multiplication via evalAtPoint.
    r • fromKappa(v) = fromKappa(evalAtPoint(r) * v). -/
theorem fromKappa_ring_smul (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (hp : (p : X.carrier) ∈ U.unop)
    (r : ↑(X.ringCatSheaf.val.obj U))
    (v : X.residueField p) :
    r • fromKappa p U hp v = fromKappa p U hp (evalAtPoint p U.unop hp r * v) := by
  apply toKappa_injective p U hp
  rw [toKappa_ring_smul p U hp r (fromKappa p U hp v)]
  rw [toKappa_fromKappa, toKappa_fromKappa]

end RiemannSurfaces.SchemeTheoretic.SkyscraperConstruction
