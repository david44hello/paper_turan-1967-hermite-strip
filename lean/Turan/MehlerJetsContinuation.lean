-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.GeneratingBounds
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros

noncomputable section
open Polynomial Metric Filter
open scoped Topology
namespace Turan.MehlerJets

def spatialSeries (p : ℂ × ℂ) : ℂ :=
  ∑' k : ℕ, (1/5 : ℂ)^k * psi k p.1 * psi k p.2

def spatialKernel (p : ℂ × ℂ) : ℂ :=
  (Real.sqrt (1-(1/5:ℝ)^2) : ℂ)⁻¹ * Complex.exp
    ((2*p.1*p.2/5-(p.1^2+p.2^2)/25)/(1-(1/5:ℂ)^2))

private def term (k : ℕ) (p : ℂ × ℂ) : ℂ := ((1:ℂ)/5)^k * psi k p.1 * psi k p.2

/-- The M-test on a bounded ball has the defining series as its limit. -/
private theorem series_uniform (R : ℝ) :
    TendstoUniformlyOn (fun N p => ∑ k ∈ Finset.range N, term k p)
      spatialSeries atTop (closedBall 0 R) := by
  let q := Real.exp 1 ^ 2/10
  let δ := Real.log (5/4)
  have hδ : 0 < δ := Real.log_pos (by norm_num)
  let M := Real.exp (4*R^2/δ)
  apply tendstoUniformlyOn_tsum_nat (u := fun n => M*(q*(5/4))^n)
    ((summable_geometric_of_lt_one (by dsimp [q]; positivity)
      (by dsimp [q]; linarith only [mehler_growth_ratio])).mul_left M)
  intro n p hp
  have hp' : ‖p‖ ≤ R := mem_closedBall_zero_iff.mp hp
  have h₁ := (norm_fst_le p).trans hp'
  have h₂ := (norm_snd_le p).trans hp'
  have hlin : 2*Real.sqrt n*(‖p.1‖+‖p.2‖) ≤ δ*(n:ℝ) + 4*R^2/δ := by
    have hb := mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by positivity : 0 ≤ 2*Real.sqrt n)
    apply hb.trans
    rw [add_comm (δ*(n:ℝ)), ← sub_le_iff_le_add, le_div_iff₀ hδ]
    have hs := Real.sq_sqrt (by positivity : 0 ≤ (n:ℝ))
    nlinarith only [sq_nonneg (δ*Real.sqrt n-2*R),
      congrArg (fun y : ℝ => δ^2*y) hs]
  apply (mehler_term_majorant n p.1 p.2).trans
  calc
    _ ≤ q^n * Real.exp (δ*(n:ℝ)+4*R^2/δ) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlin) (by dsimp [q]; positivity)
    _ = _ := by
      rw [Real.exp_add, mul_comm δ, Real.exp_nat_mul, show Real.exp δ = 5/4 from Real.exp_log (by norm_num),
        mul_pow]
      dsimp only [M]
      ring

/-- On a coordinate slice the partial sums are holomorphic polynomials.
The locally uniform limit is therefore holomorphic on the slice. -/
private theorem series_slice (g : ℂ → ℂ × ℂ) (z : ℂ) (R : ℝ)
    (hz : ‖z‖ < R) (hmap : Set.MapsTo g (ball 0 R) (closedBall 0 R))
    (hd : ∀ k, Differentiable ℂ (term k ∘ g)) :
    AnalyticAt ℂ (spatialSeries ∘ g) z := by
  have hu := ((series_uniform R).comp g).mono hmap
  have hlim := hu.tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall (fun N => DifferentiableOn.fun_sum (fun k _ => (hd k).differentiableOn)))
    isOpen_ball
  exact hlim.analyticAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz))

private theorem series_left (z w : ℂ) :
    AnalyticAt ℂ (fun t => spatialSeries (t,w)) z := by
  let R := max ‖z‖ ‖w‖ + 1
  apply series_slice (fun t => (t,w)) z R (by dsimp [R]; linarith [le_max_left ‖z‖ ‖w‖])
  · intro t ht
    exact mem_closedBall_zero_iff.mpr (max_le (mem_ball_zero_iff.mp ht).le
      (show ‖w‖ ≤ R by dsimp [R]; linarith [le_max_right ‖z‖ ‖w‖]))
  · intro k; unfold Function.comp term psi; fun_prop

private theorem series_right (z w : ℂ) :
    AnalyticAt ℂ (fun t => spatialSeries (z,t)) w := by
  let R := max ‖z‖ ‖w‖ + 1
  apply series_slice (fun t => (z,t)) w R (by dsimp [R]; linarith [le_max_right ‖z‖ ‖w‖])
  · intro t ht
    exact mem_closedBall_zero_iff.mpr (max_le
      (show ‖z‖ ≤ R by dsimp [R]; linarith [le_max_left ‖z‖ ‖w‖]) (mem_ball_zero_iff.mp ht).le)
  · intro k; unfold Function.comp term psi; fun_prop

private theorem eq_of_real_axis (u v : ℂ → ℂ) (hu : ∀ t, AnalyticAt ℂ u t)
    (hv : ∀ t, AnalyticAt ℂ v t) (h : ∀ t : ℝ, u t = v t) : u = v := by
  have hacc : (0:ℂ) ∈ closure ({z | u z = v z} \ {0}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨((ε/2:ℝ):ℂ), ⟨h _, ?_⟩, ?_⟩
    · simpa using (show ε/2 ≠ 0 by positivity)
    · simp [abs_of_pos hε]; linarith
  exact funext (fun z => AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure
    (fun t _ => hu t) (fun t _ => hv t) isPreconnected_univ (Set.mem_univ _) hacc (Set.mem_univ z))

/-- First extend along the first variable with a real second variable, then
extend along the second variable with an arbitrary complex first variable. -/
private theorem eq_of_slices (f g : ℂ × ℂ → ℂ)
    (hfl : ∀ (z : ℂ) (y : ℝ), AnalyticAt ℂ (fun t : ℂ => f (t,y)) z)
    (hgl : ∀ (z : ℂ) (y : ℝ), AnalyticAt ℂ (fun t : ℂ => g (t,y)) z)
    (hfr : ∀ z w : ℂ, AnalyticAt ℂ (fun t : ℂ => f (z,t)) w)
    (hgr : ∀ z w : ℂ, AnalyticAt ℂ (fun t : ℂ => g (z,t)) w)
    (hreal : ∀ x y : ℝ, f ((x:ℂ),(y:ℂ)) = g ((x:ℂ),(y:ℂ))) : f = g := by
  have first (y : ℝ) := eq_of_real_axis _ _ (fun z => hfl z y) (fun z => hgl z y) (fun x => hreal x y)
  funext ⟨z,w⟩
  exact congrFun (eq_of_real_axis _ _ (hfr z) (hgr z) (fun t => congrFun (first t) z)) w

theorem spatial_eq_of_real_plane (f g : ℂ × ℂ → ℂ)
    (hf : ∀ p, AnalyticAt ℂ f p) (hg : ∀ p, AnalyticAt ℂ g p)
    (hreal : ∀ x y : ℝ, f ((x:ℂ),(y:ℂ)) = g ((x:ℂ),(y:ℂ))) :
    f = g := by
  exact eq_of_slices f g
    (fun z y => (hf (z,y)).comp (f := fun t : ℂ => (t,(y:ℂ))) (by fun_prop))
    (fun z y => (hg (z,y)).comp (f := fun t : ℂ => (t,(y:ℂ))) (by fun_prop))
    (fun z w => (hf (z,w)).comp (f := fun t : ℂ => (z,t)) (by fun_prop))
    (fun z w => (hg (z,w)).comp (f := fun t : ℂ => (z,t)) (by fun_prop)) hreal

theorem mehler_continuation_from_real
    (hr : ∀ x y : ℝ, spatialSeries ((x:ℂ),(y:ℂ)) = spatialKernel ((x:ℂ),(y:ℂ))) :
    spatialSeries = spatialKernel := by
  apply eq_of_slices spatialSeries spatialKernel (fun z y => series_left z y) _ series_right _ hr
  · intro z y; unfold spatialKernel; fun_prop
  · intro z w; unfold spatialKernel; fun_prop

end Turan.MehlerJets
