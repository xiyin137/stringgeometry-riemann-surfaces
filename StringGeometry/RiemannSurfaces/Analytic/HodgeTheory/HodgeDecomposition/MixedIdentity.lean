import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.HodgeDecomposition.Core
import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.Infrastructure.ChartSelection

/-!
# Mixed `∂̄∂ + ∂∂̄` Identity Helpers

Selector-sensitive local versions of the mixed identity for `del_real` / `dbar_real_hd`.
-/

namespace RiemannSurfaces.Analytic

open Complex Topology
open scoped Manifold
open OnePoint

variable {RS : RiemannSurface}

/-- Pointwise mixed identity under local chart-selection stabilization at the point. -/
theorem dbar_10_del_real_add_del_01_dbar_real_hd_toSection_eq_zero_of_chartAt_eventuallyEq
    (f : RealSmoothFunction RS) (p : RS.carrier)
    (hchartp :
      letI := RS.topology
      letI := RS.chartedSpace
      (fun q : RS.carrier => @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace q)
        =ᶠ[nhds p]
      (fun _ : RS.carrier => @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p)) :
    (dbar_10 (del_real f) + del_01 (dbar_real_hd f)).toSection p = 0 := by
  letI := RS.topology
  letI := RS.chartedSpace
  let e := @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p
  have he_source : p ∈ e.source := by
    simpa [e] using (mem_chart_source ℂ p)
  have he_target : e p ∈ e.target := by
    simpa [e] using (mem_chart_target ℂ p)
  have hchartz :
      (fun z : ℂ => @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace (e.symm z))
        =ᶠ[nhds (e p)]
      (fun _ : ℂ => e) := by
    have hcont_symm : ContinuousAt e.symm (e p) := by
      simpa [e] using (e.continuousAt_symm he_target)
    have hsymm_eq : e.symm (e p) = p := by
      simpa [e] using (e.left_inv he_source)
    have hto_p : Filter.Tendsto e.symm (nhds (e p)) (nhds p) := by
      simpa [hsymm_eq] using hcont_symm.tendsto
    exact hchartp.comp_tendsto hto_p
  have hcdiffOn :
      ContDiffOn ℝ ((2 : ℕ∞) : WithTop ℕ∞) (f.toFun ∘ e.symm) e.target := by
    simpa [e] using
      (RealSmoothFunction.contDiffOn_comp_chart_symm (f := f) (p0 := p) (n := (2 : ℕ∞)))
  have hsec_fixed :
      ((dbar_real_hd f).toSection ∘ e.symm) =ᶠ[nhds (e p)]
        (fun z => wirtingerDeriv_zbar (f.toFun ∘ e.symm) z) := by
    filter_upwards [hchartz, e.open_target.mem_nhds he_target] with z hzchart hzt
    have hzid : e (e.symm z) = z := e.right_inv hzt
    simp [dbar_real_hd, hzchart, hzid]
  have hdel01_eq :
      Infrastructure.wirtingerDeriv (((dbar_real_hd f).toSection) ∘ e.symm) (e p) =
        Infrastructure.wirtingerDeriv (fun z => wirtingerDeriv_zbar (f.toFun ∘ e.symm) z) (e p) :=
    Infrastructure.wirtingerDeriv_congr_of_eventuallyEq hsec_fixed
  have hdel_fixed :
      ((del_real f).toSection ∘ e.symm) =ᶠ[nhds (e p)]
        (fun z => wirtingerDeriv_z (f.toFun ∘ e.symm) z) := by
    filter_upwards [hchartz, e.open_target.mem_nhds he_target] with z hzchart hzt
    have hzid : e (e.symm z) = z := e.right_inv hzt
    have hdiffAt : DifferentiableAt ℝ (f.toFun ∘ e.symm) z := by
      have hcdiffAt : ContDiffAt ℝ ((2 : ℕ∞) : WithTop ℕ∞) (f.toFun ∘ e.symm) z :=
        hcdiffOn.contDiffAt (e.open_target.mem_nhds hzt)
      exact hcdiffAt.differentiableAt (by simp)
    have hconj_bar :
        Infrastructure.wirtingerDerivBar (starRingEnd ℂ ∘ (f.toFun ∘ e.symm)) z =
          starRingEnd ℂ (Infrastructure.wirtingerDeriv (f.toFun ∘ e.symm) z) :=
      Infrastructure.wirtingerDerivBar_comp_conj_real hdiffAt
    have hcomp : f.conj.toFun ∘ e.symm = starRingEnd ℂ ∘ (f.toFun ∘ e.symm) := by
      ext w
      simp [RealSmoothFunction.conj_toFun]
    have hbar_conj :
        Infrastructure.wirtingerDerivBar (f.conj.toFun ∘ e.symm) z =
          starRingEnd ℂ (Infrastructure.wirtingerDeriv (f.toFun ∘ e.symm) z) := by
      rw [hcomp]
      exact hconj_bar
    have hstar_hbar :
        (starRingEnd ℂ) (wirtingerDeriv_zbar (f.conj.toFun ∘ e.symm) z) =
          wirtingerDeriv_z (f.toFun ∘ e.symm) z := by
      have hstar := congrArg (starRingEnd ℂ) hbar_conj
      simpa [wirtingerDeriv_zbar, wirtingerDeriv_z] using hstar
    simpa [del_real, dbar_real_hd, hzchart, hzid] using hstar_hbar
  have hdbar_eq :
      Infrastructure.wirtingerDerivBar (((del_real f).toSection) ∘ e.symm) (e p) =
        Infrastructure.wirtingerDerivBar (fun z => wirtingerDeriv_z (f.toFun ∘ e.symm) z) (e p) :=
    Infrastructure.wirtingerDerivBar_congr_of_eventuallyEq hdel_fixed
  have hcdiffAt :
      ContDiffAt ℝ ((2 : ℕ∞) : WithTop ℕ∞) (f.toFun ∘ e.symm) (e p) :=
    hcdiffOn.contDiffAt (e.open_target.mem_nhds he_target)
  have hmixed :
      Infrastructure.wirtingerDeriv (Infrastructure.wirtingerDerivBar (f.toFun ∘ e.symm)) (e p) =
      Infrastructure.wirtingerDerivBar (Infrastructure.wirtingerDeriv (f.toFun ∘ e.symm)) (e p) :=
    Infrastructure.laplacian_eq_four_wirtinger_mixed_at (f := f.toFun ∘ e.symm) (z := e p) hcdiffAt
  change -(Infrastructure.wirtingerDerivBar ((del_real f).toSection ∘ e.symm) (e p)) +
      Infrastructure.wirtingerDeriv ((dbar_real_hd f).toSection ∘ e.symm) (e p) = 0
  rw [hdbar_eq, hdel01_eq]
  simpa [wirtingerDeriv_zbar, wirtingerDeriv_z, hmixed] using sub_eq_zero.mpr hmixed

/-- Nonzero-point specialization on `RiemannSphere`:
the mixed identity holds at finite points `a ≠ 0`. -/
theorem dbar_10_del_real_add_del_01_dbar_real_hd_toSection_eq_zero_riemannSphere_coe_of_ne_zero
    (f : RealSmoothFunction RiemannSphere) (a : ℂ) (ha : a ≠ 0) :
    (dbar_10 (del_real f) + del_01 (dbar_real_hd f)).toSection ((a : ℂ) : OnePoint ℂ) = 0 := by
  exact dbar_10_del_real_add_del_01_dbar_real_hd_toSection_eq_zero_of_chartAt_eventuallyEq
    (RS := RiemannSphere) f ((a : ℂ) : OnePoint ℂ)
    (Infrastructure.chartAt_eventuallyEq_center_riemannSphere_coe_of_ne_zero a ha)

end RiemannSurfaces.Analytic

