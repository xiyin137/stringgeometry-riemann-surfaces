/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringGeometry.RiemannSurfaces.SchemeTheoretic.Helpers.SkyscraperModuleConstruction
import StringGeometry.RiemannSurfaces.SchemeTheoretic.Helpers.CohomologyModuleStructure
import StringGeometry.RiemannSurfaces.SchemeTheoretic.Helpers.SkyscraperInfrastructure

/-!
# Skyscraper Sheaf H⁰ Infrastructure

This file proves that h⁰(k_p) = 1 for the skyscraper sheaf at a closed point p.

The proof uses `finrank_eq_one_iff_of_nonzero'` with the "constant 1" cocycle:
1. Construct a nonzero cocycle v with toKappa(v(σ)) = 1 for all σ with p ∈ U_σ
2. Show every cocycle w is a ℂ-scalar multiple of v
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Classical

namespace RiemannSurfaces.SchemeTheoretic.SkyscraperH0

variable (C : AlgebraicCurve) (p : C.PointType)

/-- The underlying presheaf of the skyscraper module at p. -/
noncomputable def skyPresheaf : OModule C.toScheme :=
  SkyscraperConstruction.constructSkyscraperModule (X := C.toScheme) p

/-- Construction of the "constant v" 0-cochain for the skyscraper.
    Assigns fromKappa(v) at each σ with p ∈ 𝒰.intersection σ, and 0 otherwise. -/
noncomputable def constantCochain (𝒰 : OpenCover C.toScheme) (v : C.toScheme.residueField p) :
    CechCochain (skyPresheaf C p) 𝒰 0 := fun σ =>
  if h : (p : C.toScheme.carrier) ∈ 𝒰.intersection σ then
    SkyscraperConstruction.fromKappa p (op (𝒰.intersection σ)) h v
  else
    0

/-- p ∈ 𝒰.intersection (fun _ => i) when p ∈ U i. -/
theorem p_mem_intersection_single (𝒰 : OpenCover C.toScheme) (i : 𝒰.I)
    (hi : (p : C.toScheme.carrier) ∈ 𝒰.U i) :
    (p : C.toScheme.carrier) ∈ 𝒰.intersection (fun (_ : Fin 1) => i) := by
  unfold OpenCover.intersection
  simp only [show (0 + 1 : ℕ) ≠ 0 from by omega, ↓reduceDIte, iInf_unique]
  exact hi

/-- The constant cochain is a 0-cocycle (d⁰ = 0). -/
theorem constantCochain_is_cocycle (𝒰 : OpenCover C.toScheme) (v : C.toScheme.residueField p) :
    cechDifferential (skyPresheaf C p) 𝒰 0 (constantCochain C p 𝒰 v) = 0 := by
  funext τ
  show cechDifferential (skyPresheaf C p) 𝒰 0 (constantCochain C p 𝒰 v) τ = 0
  simp only [cechDifferential]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_one_smul,
    restrictionToFace]
  -- Goal: res(c(face 0 τ)) + (-res(c(face 1 τ))) = 0
  rw [add_neg_eq_zero]
  by_cases hp_tau : (p : C.toScheme.carrier) ∈ 𝒰.intersection τ
  · -- p ∈ 𝒰.intersection τ, so p is in both face intersections
    have hp0 := intersection_face_le 𝒰 τ 0 hp_tau
    have hp1 := intersection_face_le 𝒰 τ 1 hp_tau
    -- Use toKappa_injective: reduce to equality in κ(p)
    apply SkyscraperConstruction.toKappa_injective p (op (𝒰.intersection τ)) hp_tau
    -- erw [res_toKappa] removes the restriction maps (erw needed for presheaf.map vs val.map)
    erw [SkyscraperConstruction.res_toKappa p (homOfLE (intersection_face_le 𝒰 τ 0)).op hp0 hp_tau,
         SkyscraperConstruction.res_toKappa p (homOfLE (intersection_face_le 𝒰 τ 1)).op hp1 hp_tau]
    -- Unfold constantCochain to expose the dif, then split
    simp only [constantCochain]
    split_ifs with h0 h1
    · simp only [SkyscraperConstruction.toKappa_fromKappa]
    · exact absurd hp1 h1
    · exact absurd hp0 h0
    · exact absurd hp0 h0
  · -- p ∉ 𝒰.intersection τ: target module is subsingleton (it's PUnit)
    exact @Subsingleton.elim _
      (SkyscraperConstruction.skyscraperObj_subsingleton (X := C.toScheme) p _ hp_tau) _ _

/-- The constant cocycle: the constant cochain bundled as a cocycle. -/
noncomputable def constantCocycle (𝒰 : OpenCover C.toScheme) (v : C.toScheme.residueField p) :
    CechCocycles (skyPresheaf C p) 𝒰 0 :=
  ⟨constantCochain C p 𝒰 v, by
    simp only [CechCocycles, AddMonoidHom.mem_ker, cechDifferentialHom,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    exact constantCochain_is_cocycle C p 𝒰 v⟩

/-- The "constant 1" cocycle is nonzero. -/
theorem constantCocycle_one_ne_zero (𝒰 : OpenCover C.toScheme) :
    constantCocycle C p 𝒰 1 ≠ 0 := by
  sorry

/-- Local version of res_toKappa matching the syntactic form (skyPresheaf C p).val.map.
    This enables `rw` without `erw`, avoiding unwanted unfolding of `intersection`. -/
private theorem res_toKappa_sky {U V : (Opens C.toScheme.carrier)ᵒᵖ}
    (f : U ⟶ V) (hU : (p : C.toScheme.carrier) ∈ U.unop) (hV : (p : C.toScheme.carrier) ∈ V.unop)
    (x : ↑((skyPresheaf C p).val.obj U)) :
    SkyscraperConstruction.toKappa p V hV ((skyPresheaf C p).val.map f x) =
    SkyscraperConstruction.toKappa p U hU x :=
  SkyscraperConstruction.res_toKappa p f hU hV x

/-- For a 0-cocycle of the skyscraper, toKappa values at (fun _ => i) and (fun _ => j) agree.

    This follows from d⁰(w) = 0: for τ = [i, j], the differential gives
    res(w(fun _ => j)) = res(w(fun _ => i)), and res_toKappa shows
    toKappa commutes with restriction. -/
private theorem cocycle_toKappa_eq
    (𝒰 : OpenCover C.toScheme)
    (w : CechCocycles (skyPresheaf C p) 𝒰 0)
    (i j : 𝒰.I) (hi : (p : C.toScheme.carrier) ∈ 𝒰.U i)
    (hj : (p : C.toScheme.carrier) ∈ 𝒰.U j) :
    SkyscraperConstruction.toKappa p (op (𝒰.intersection (fun _ => i)))
      (p_mem_intersection_single C p 𝒰 i hi) (w.val (fun _ => i)) =
    SkyscraperConstruction.toKappa p (op (𝒰.intersection (fun _ => j)))
      (p_mem_intersection_single C p 𝒰 j hj) (w.val (fun _ => j)) := by
  -- w is a cocycle: d⁰(w) = 0
  have hw : cechDifferential (skyPresheaf C p) 𝒰 0 w.val = 0 :=
    AddMonoidHom.mem_ker.mp w.prop
  -- Evaluate d⁰(w) at τ = [i, j] : Fin 2 → 𝒰.I
  let τ : Fin 2 → 𝒰.I := fun k => if k.val = 0 then i else j
  have hw_τ : cechDifferential (skyPresheaf C p) 𝒰 0 w.val τ = 0 :=
    congrFun hw τ
  -- p ∈ intersection τ = U(i) ⊓ U(j)
  have hp_τ : (p : C.toScheme.carrier) ∈ 𝒰.intersection τ := by
    unfold OpenCover.intersection
    simp only [show (1 + 1 : ℕ) ≠ 0 from by omega, ↓reduceDIte]
    -- Convert ⨅ over Fin 2 to binary ⊓ using le_antisymm
    rw [show ⨅ k : Fin 2, 𝒰.U (τ k) = 𝒰.U i ⊓ 𝒰.U j from
      le_antisymm
        (le_inf ((iInf_le _ 0).trans (by show 𝒰.U (τ 0) ≤ 𝒰.U i; simp [τ]))
                ((iInf_le _ 1).trans (by show 𝒰.U (τ 1) ≤ 𝒰.U j; simp [τ])))
        (le_iInf fun k => by fin_cases k <;> simp_all [τ, inf_le_left, inf_le_right])]
    exact ⟨hi, hj⟩
  -- Extract the equality from d⁰(w)(τ) = 0
  have hres_eq : (skyPresheaf C p).val.map
      (homOfLE (intersection_face_le 𝒰 τ 0)).op (w.val (faceMap 0 τ)) =
    (skyPresheaf C p).val.map
      (homOfLE (intersection_face_le 𝒰 τ 1)).op (w.val (faceMap 1 τ)) := by
    have h := hw_τ
    simp only [cechDifferential] at h
    rw [Fin.sum_univ_two] at h
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_one_smul,
      restrictionToFace] at h
    exact sub_eq_zero.mp (by rwa [sub_eq_add_neg])
  -- p is in both face intersections
  have hp0 : (p : C.toScheme.carrier) ∈ 𝒰.intersection (faceMap 0 τ) :=
    intersection_face_le 𝒰 τ 0 hp_τ
  have hp1 : (p : C.toScheme.carrier) ∈ 𝒰.intersection (faceMap 1 τ) :=
    intersection_face_le 𝒰 τ 1 hp_τ
  -- Compute face maps: faceMap 0 [i,j] = [j], faceMap 1 [i,j] = [i]
  have hface0 : faceMap 0 τ = (fun _ : Fin 1 => j) := by
    ext ⟨k, hk⟩
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  have hface1 : faceMap 1 τ = (fun _ : Fin 1 => i) := by
    ext ⟨k, hk⟩
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  -- Transport lemma: toKappa is invariant under equal σ (subst trick for dependent types)
  have transport : ∀ (σ₁ σ₂ : Fin 1 → 𝒰.I) (hσ : σ₁ = σ₂)
      (hp₁ : (p : C.toScheme.carrier) ∈ 𝒰.intersection σ₁)
      (hp₂ : (p : C.toScheme.carrier) ∈ 𝒰.intersection σ₂),
      SkyscraperConstruction.toKappa p (op (𝒰.intersection σ₁)) hp₁ (w.val σ₁) =
      SkyscraperConstruction.toKappa p (op (𝒰.intersection σ₂)) hp₂ (w.val σ₂) := by
    intro σ₁ σ₂ hσ hp₁ hp₂; subst hσ; rfl
  -- Build the equality chain in term mode to avoid rw unfolding intersection:
  -- toKappa_i(w(i)) = toKappa_{face1}(w(face1))     by transport (hface1)
  --                  = toKappa_τ(res(w(face1)))       by res_toKappa_sky
  --                  = toKappa_τ(res(w(face0)))       by congr_arg hres_eq
  --                  = toKappa_{face0}(w(face0))      by res_toKappa_sky
  --                  = toKappa_j(w(j))                by transport (hface0)
  exact
    (transport _ _ hface1.symm (p_mem_intersection_single C p 𝒰 i hi) hp1).trans
      ((res_toKappa_sky C p ((homOfLE (intersection_face_le 𝒰 τ 1)).op) hp1 hp_τ
        (w.val (faceMap 1 τ))).symm.trans
      ((congr_arg (SkyscraperConstruction.toKappa p (op (𝒰.intersection τ)) hp_τ)
        hres_eq.symm).trans
      ((res_toKappa_sky C p ((homOfLE (intersection_face_le 𝒰 τ 0)).op) hp0 hp_τ
        (w.val (faceMap 0 τ))).trans
      (transport _ _ hface0 hp0 (p_mem_intersection_single C p 𝒰 j hj)))))

/-- toKappa of the ℂ-smul of constantCocycle: computes
    toKappa((c • constantCocycle v).val σ) = canonicalResidueMap(c) * v
    when p ∈ intersection σ. -/
private theorem toKappa_smul_constantCocycle
    (𝒰 : OpenCover C.toScheme) (v : C.toScheme.residueField p)
    (c_val : ℂ) (σ : Fin 1 → 𝒰.I)
    (hp_σ : (p : C.toScheme.carrier) ∈ 𝒰.intersection σ) :
    letI : Module ℂ (CechCocycles (skyPresheaf C p) 𝒰 0) :=
      CechCohomology0.module C (skyPresheaf C p) 𝒰
    SkyscraperConstruction.toKappa p (op (𝒰.intersection σ)) hp_σ
      ((c_val • constantCocycle C p 𝒰 v).val σ) =
    canonicalResidueMap C p c_val * v := by
  sorry

/-- Every cocycle of the skyscraper is a ℂ-scalar multiple of the constant 1 cocycle.

    Key proof steps:
    1. Choose i₀ with p ∈ U_{i₀}
    2. Let α = toKappa(w(fun _ => i₀)) ∈ κ(p)
    3. Take c = canonicalResidueEquiv⁻¹(α)
    4. Show (c • v)(σ) = w(σ) for all σ using:
       - toKappa(c • v(σ)) = canonicalResidueMap(c) * 1 = α (by smul_toKappa)
       - toKappa(w(σ)) = α (by cocycle condition: toKappa values are constant)
       - Conclude by toKappa_injective -/
theorem skyscraper_cocycle_scalar_multiple
    (𝒰 : OpenCover C.toScheme)
    (w : CechCocycles (skyPresheaf C p) 𝒰 0) :
    letI : Module ℂ (CechCocycles (skyPresheaf C p) 𝒰 0) :=
      CechCohomology0.module C (skyPresheaf C p) 𝒰
    ∃ c : ℂ, c • constantCocycle C p 𝒰 1 = w := by
  sorry

end RiemannSurfaces.SchemeTheoretic.SkyscraperH0
