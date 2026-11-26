module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Circles
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.Harmonic.MeanValue
public import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

@[expose] public section

open Metric Filter
open scoped Topology
namespace Turan

theorem harnack_disk (f : ℂ → ℝ) (c z : ℂ) (R : ℝ)
    (hf : InnerProductSpace.HarmonicContOnCl f (ball c R))
    (hn : ∀ w ∈ sphere c R, 0 ≤ f w) (hz : z ∈ ball c R) :
    (R-‖z-c‖)/(R+‖z-c‖)*f c ≤ f z ∧ f z ≤ (R+‖z-c‖)/(R-‖z-c‖)*f c := by
  have hR := pos_of_mem_ball hz
  let K := Complex.re ∘ herglotzRieszKernel c z
  let lo := (R-‖z-c‖)/(R+‖z-c‖)
  let hi := (R+‖z-c‖)/(R-‖z-c‖)
  have hfc : ContinuousOn f (sphere c |R|) := by
    rw [abs_of_pos hR]
    exact hf.continuousOn_ball.mono sphere_subset_closedBall
  have hzoff : z ∉ sphere c |R| := by
    rw [abs_of_pos hR, mem_sphere]
    exact (mem_ball.mp hz).ne
  have hK : ContinuousOn K (sphere c |R|) :=
    Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hzoff)
  have hweighted : CircleIntegrable (K • f) c R := (hK.smul hfc).circleIntegrable'
  have hscalar (a : ℝ) : CircleIntegrable (a • f) c R :=
    (continuousOn_const.smul hfc).circleIntegrable'
  have hmean : Real.circleAverage f c R = f c :=
    InnerProductSpace.HarmonicContOnCl.circleAverage_eq (by simpa [abs_of_pos hR] using hf)
  have hpoisson : Real.circleAverage (K • f) c R = f z :=
    hf.circleAverage_re_herglotzRieszKernel_smul hz
  have lower : Real.circleAverage (lo • f) c R ≤ Real.circleAverage (K • f) c R := by
    apply Real.circleAverage_mono (hscalar lo) hweighted
    rw [abs_of_pos hR]
    intro w hw
    have hkernel : lo ≤ K w := by
      simpa only [K, Function.comp_apply, lo, herglotzRieszKernel_def] using le_re_herglotzRieszKernel hw hz
    exact mul_le_mul_of_nonneg_right hkernel (hn w hw)
  have upper : Real.circleAverage (K • f) c R ≤ Real.circleAverage (hi • f) c R := by
    apply Real.circleAverage_mono hweighted (hscalar hi)
    rw [abs_of_pos hR]
    intro w hw
    have hkernel : K w ≤ hi := by
      simpa only [K, Function.comp_apply, hi, herglotzRieszKernel_def] using re_herglotzRieszKernel_le hw hz
    exact mul_le_mul_of_nonneg_right hkernel (hn w hw)
  rw [hpoisson] at lower upper
  simpa only [Real.circleAverage_smul, hmean, smul_eq_mul] using And.intro lower upper

theorem zeros_persist_locally (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hF : ∀ j, Differentiable ℂ (F j)) (hf : Differentiable ℂ f)
    (hconv : TendstoLocallyUniformly F f atTop) (hn : f ≠ 0) (c : ℂ) (hc : f c = 0)
    (r : ℝ) (hr : 0 < r) :
    ∀ᶠ j in atTop, ∃ z ∈ ball c r, F j z = 0 := by
  have han : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hisolated := (hf.analyticAt c).eventually_eq_zero_or_eventually_ne_zero.resolve_left
    (fun he => hn (han.eq_of_eventuallyEq analyticOnNhd_const he))
  obtain ⟨δ, hδ, hlocal⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hisolated)
  let ρ := min r δ / 2
  have hρ : 0 < ρ := half_pos (lt_min hr hδ)
  have hρδ : ρ < δ := (half_lt_self (lt_min hr hδ)).trans_le (min_le_right ..)
  have hρr : ρ ≤ r := (half_lt_self (lt_min hr hδ)).le.trans (min_le_left ..)
  have hboundary (w : ℂ) (hw : w ∈ sphere c ρ) : f w ≠ 0 :=
    hlocal ((mem_sphere.mp hw).trans_lt hρδ) (ne_of_mem_sphere hw hρ.ne')
  obtain ⟨w, hw, hmin⟩ := (isCompact_sphere c ρ).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hρ.le) hf.continuous.norm.continuousOn
  have huniform := tendstoLocallyUniformly_iff_forall_isCompact.mp hconv _ (isCompact_sphere c ρ)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp huniform _ (norm_pos_iff.mpr (hboundary w hw))]
    with j hj
  obtain ⟨z, hz, he⟩ := circle_comparison hρ (hF j).differentiableOn hf.differentiableOn
    ⟨c, mem_ball_self hρ, hc⟩ (fun v hv => by
      have h := (hj v hv).trans_le (hmin hv)
      simpa only [dist_comm (f v), dist_eq_norm] using h)
  exact ⟨z, ball_subset_ball hρr hz, he⟩

end Turan
