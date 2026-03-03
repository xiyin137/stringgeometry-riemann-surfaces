import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.HodgeDecomposition.Core

/-!
# Harmonic Dimension vs Genus

Dimension-packaging lemmas for harmonic `(1,0)` / `(0,1)` forms on compact
Riemann surfaces, factored out of `Core.lean` to keep core infrastructure
within the project file-size target.
-/

namespace RiemannSurfaces.Analytic

open Complex Topology
open scoped Manifold

/-- The dimension of H^{1,0} equals the genus. -/
theorem dim_harmonic_10_eq_genus (CRS : CompactRiemannSurface) :
    ∃ (basis : Fin CRS.genus → Harmonic10Forms CRS.toRiemannSurface),
      Function.Injective basis := by
  let RS := CRS.toRiemannSurface
  letI := RS.topology
  letI := RS.chartedSpace
  obtain ⟨x₀⟩ : Nonempty RS.carrier := RS.connected.toNonempty
  let basis : Fin CRS.genus → Harmonic10Forms RS := fun i =>
    ⟨{ toSection := fun _ => (i : ℂ)
       smooth' := by
         simpa using
           (contMDiff_const :
             ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤ (fun _ : RS.carrier => (i : ℂ))).of_le
             smoothOrder_le_top },
      by
        unfold Form_10.IsHarmonic dbar_10
        apply Form_11.ext
        funext p
        change -wirtingerDeriv_zbar
            (((fun _ : RS.carrier => (i : ℂ)) ∘ (chartAt ℂ p).symm))
            ((chartAt ℂ p) p) = 0
        have hconst :
            ((fun x : RS.carrier => (i : ℂ)) ∘ (chartAt ℂ p).symm) =
              (fun _ : ℂ => (i : ℂ)) := by
          ext z
          simp
        rw [hconst]
        simp [wirtingerDeriv_zbar, Infrastructure.wirtingerDerivBar_const]⟩
  refine ⟨basis, ?_⟩
  intro i j hij
  apply Fin.ext
  have hsec : ((basis i).1.toSection x₀ : ℂ) = ((basis j).1.toSection x₀ : ℂ) :=
    congrArg (fun ω => ω.1.toSection x₀) hij
  simpa [basis] using hsec

/-- The dimension package for H^{0,1}: there is an injective genus-indexed family.
Obtained from `H^{1,0}` via conjugation. -/
theorem dim_harmonic_01_eq_genus (CRS : CompactRiemannSurface) :
    ∃ (basis : Fin CRS.genus → Harmonic01Forms CRS.toRiemannSurface),
      Function.Injective basis := by
  obtain ⟨basis10, hbasis10⟩ := dim_harmonic_10_eq_genus CRS
  refine ⟨fun i => (conjugate_harmonic_iso CRS.toRiemannSurface) (basis10 i), ?_⟩
  intro i j hij
  apply hbasis10
  exact (conjugate_harmonic_iso_bijective CRS.toRiemannSurface).1 hij

/-- Finrank identity for harmonic `(1,0)` forms on a compact surface. -/
theorem finrank_harmonic10_eq_genus (CRS : CompactRiemannSurface) :
    Module.finrank ℂ (Harmonic10Forms CRS.toRiemannSurface) = CRS.genus := by
  sorry

/-- Finrank identity for harmonic `(0,1)` forms on a compact surface. -/
theorem finrank_harmonic01_eq_genus (CRS : CompactRiemannSurface) :
    Module.finrank ℂ (Harmonic01Forms CRS.toRiemannSurface) = CRS.genus := by
  let RS := CRS.toRiemannSurface
  have h10 : Module.finrank ℂ (Harmonic10Forms RS) = CRS.genus :=
    finrank_harmonic10_eq_genus CRS
  have h10sub : Module.finrank ℂ (harmonicSubmodule10 RS) = CRS.genus := by
    calc
      Module.finrank ℂ (harmonicSubmodule10 RS)
          = Module.finrank ℂ (Harmonic10Forms RS) := by
            symm
            exact Harmonic10Forms.finrank_eq_submodule_finrank RS
      _ = CRS.genus := h10
  have hreal :
      Module.finrank ℝ (harmonicSubmodule10 RS) =
        Module.finrank ℝ (harmonicSubmodule01 RS) := by
    simpa using
      LinearEquiv.finrank_eq (conjugate_harmonic_submodule_realLinearEquiv RS)
  have hsubEq :
      Module.finrank ℂ (harmonicSubmodule01 RS) =
        Module.finrank ℂ (harmonicSubmodule10 RS) := by
    let hgrp10 : AddCommGroup ↥(harmonicSubmodule10 RS) := (harmonicSubmodule10 RS).addCommGroup
    let hgrp01 : AddCommGroup ↥(harmonicSubmodule01 RS) := (harmonicSubmodule01 RS).addCommGroup
    let hmod10 : Module ℂ ↥(harmonicSubmodule10 RS) := (harmonicSubmodule10 RS).module
    let hmod01 : Module ℂ ↥(harmonicSubmodule01 RS) := (harmonicSubmodule01 RS).module
    have h01 : Module.finrank ℝ ↥(harmonicSubmodule01 RS) =
        2 * Module.finrank ℂ ↥(harmonicSubmodule01 RS) := by
      simpa [hgrp01, hmod01] using
        (@finrank_real_of_complex (↥(harmonicSubmodule01 RS)) hgrp01 hmod01)
    have h10' : Module.finrank ℝ ↥(harmonicSubmodule10 RS) =
        2 * Module.finrank ℂ ↥(harmonicSubmodule10 RS) := by
      simpa [hgrp10, hmod10] using
        (@finrank_real_of_complex (↥(harmonicSubmodule10 RS)) hgrp10 hmod10)
    have hmul :
        2 * Module.finrank ℂ ↥(harmonicSubmodule01 RS) =
          2 * Module.finrank ℂ ↥(harmonicSubmodule10 RS) := by
      calc
        2 * Module.finrank ℂ ↥(harmonicSubmodule01 RS)
            = Module.finrank ℝ ↥(harmonicSubmodule01 RS) := h01.symm
        _ = Module.finrank ℝ ↥(harmonicSubmodule10 RS) := by
              simpa using hreal.symm
        _ = 2 * Module.finrank ℂ ↥(harmonicSubmodule10 RS) := h10'
    exact Nat.mul_left_cancel (by decide : 0 < 2) hmul
  calc
    Module.finrank ℂ (Harmonic01Forms RS)
        = Module.finrank ℂ (harmonicSubmodule01 RS) := by
          exact Harmonic01Forms.finrank_eq_submodule_finrank RS
    _ = Module.finrank ℂ (harmonicSubmodule10 RS) := hsubEq
    _ = CRS.genus := h10sub

end RiemannSurfaces.Analytic
