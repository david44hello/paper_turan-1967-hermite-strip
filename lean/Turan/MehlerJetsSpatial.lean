-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.MehlerJetsContinuation
import Turan.GeneratingKernel

noncomputable section
namespace Turan.MehlerJets

/-- The only use of the parameter-series kernel in the continuation is its
restriction to pairs of real spatial coordinates. -/
private theorem kernel_on_real_plane (x y : ℝ) :
    spatialSeries ((x:ℂ),(y:ℂ)) = spatialKernel ((x:ℂ),(y:ℂ)) := by
  have h := mehler_kernel (1/5) (by norm_num) (by norm_num) (x:ℂ) (y:ℂ)
  unfold spatialSeries spatialKernel
  convert h.tsum_eq using 1 <;> push_cast
  · rfl
  · congr 2
    ring

theorem mehler_spatial_identity : spatialSeries = spatialKernel :=
  mehler_continuation_from_real kernel_on_real_plane

theorem mehler_spatial_entire (p : ℂ × ℂ) :
    AnalyticAt ℂ spatialSeries p ∧ AnalyticAt ℂ spatialKernel p := by
  have h₁ : AnalyticAt ℂ (fun q : ℂ × ℂ => q.1) p := (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _
  have h₂ : AnalyticAt ℂ (fun q : ℂ × ℂ => q.2) p := (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _
  have ha : AnalyticAt ℂ spatialKernel p := by unfold spatialKernel; fun_prop
  exact ⟨mehler_spatial_identity ▸ ha, ha⟩

end Turan.MehlerJets
