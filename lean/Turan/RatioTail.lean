-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.RatioSeries
import Turan.CircleWeightedExpansion

noncomputable section
open Polynomial
namespace Turan.Ratio

def modeScale (j : ℕ) : ℝ := (ratioScale j : ℝ)⁻¹ * 128^j

theorem scale_ne (j : ℕ) : modeScale j ≠ 0 := by
  have h : 0 < ratioScale j := by unfold ratioScale; positivity
  unfold modeScale
  positivity

theorem ratioMode_eq (j : ℕ) : ratioMode j = C (modeScale j : ℂ) * hermite j := by
  simp [ratioMode, scaledMode, modeScale, mul_assoc]

private theorem initial_jets (j : ℕ) (x r : ℝ) :
    gaugedJet j x r 0 = (ratioMode j).eval (x:ℂ) ∧
    gaugedJet j x r 1 = (r:ℂ)*((ratioMode j).derivative.eval (x:ℂ) - x*(ratioMode j).eval (x:ℂ)) := by
  let p := diskExpansion (ratioMode j) x r
  have h0 : p.coeff 0 = (ratioMode j).eval (x:ℂ) := by
    simp [p, diskExpansion, coeff_zero_eq_eval_zero, eval_comp, eval_mul]
  have h1 : p.coeff 1 = (r:ℂ)*(ratioMode j).derivative.eval (x:ℂ) := by
    have h := p.coeff_derivative 0
    simp only [zero_add, Nat.cast_zero, mul_one] at h
    rw [← h, coeff_zero_eq_eval_zero]
    simp [p, diskExpansion, derivative_comp, eval_comp, eval_mul]
  dsimp only [p] at h0 h1
  norm_num [gaugedJet, Finset.sum_range_succ, gaugeCoeff, h0, h1]
  ring

theorem weight_eq (x r : ℝ) (v : ℂ) :
    weight x r v = normalizedCircleWeight x (point x r v) := by
  unfold weight normalizedCircleWeight point
  congr 1
  push_cast
  ring

/-- Restore the linear pivot in Lemma 13 on the doubled disk, then sum the
Cauchy tail starting with degree eleven. -/
theorem mode_tail (j : ℕ) (x r : ℝ) (hr : 0 < r) (hQ : circleQ j x (2*r) ≤ 36)
    (v : ℂ) (hv : ‖v‖ = 1) :
    ‖mode j x r v - ∑ n ∈ Finset.range 11, gaugedJet j x r n * v^n‖ ≤ omittedTail j x r := by
  apply cauchy_tail (by unfold mode weight point; fun_prop) (mode_series j x r) _ v hv
  intro w hw
  let u := w / 2
  have hu : ‖u‖ = 1 := by simp [u, hw]
  have hpoint : point x r w = (x:ℂ) + ((2*r:ℝ):ℂ)*u := by
    unfold point u; push_cast; ring
  let d := (r:ℂ)*((ratioMode j).derivative.eval (x:ℂ) - x*(ratioMode j).eval (x:ℂ))
  have hh := weighted_normalized_expansion j (modeScale j) x (2*r) (by positivity) hQ u hu.le
  dsimp only at hh
  rw [← ratioMode_eq] at hh
  have hd : ((2*r:ℝ):ℂ)*((ratioMode j).derivative.eval (x:ℂ)-x*(ratioMode j).eval (x:ℂ)) =
      2*d := by dsimp [d]; push_cast; ring
  rw [hd, ← hpoint, ← weight_eq] at hh
  change ‖mode j x r w - 2*d*u‖ ≤ _ at hh
  have hn := norm_add_le (mode j x r w - 2*d*u) (2*d*u)
  rw [sub_add_cancel] at hn
  simp only [norm_mul, Complex.norm_ofNat, hu, mul_one] at hh hn
  rw [(initial_jets j x r).1, (initial_jets j x r).2]
  change ‖mode j x r w‖ ≤ ‖(ratioMode j).eval (x:ℂ)‖ * _ + 2*‖d‖*_
  linarith only [hh, hn]

/-- The affine term, including its Gaussian multiplier on the parameter circle. -/
theorem affine_bound (x r : ℝ) (hr : 0 < r) (v : ℂ) (hv : ‖v‖ = 1) :
    ‖weight x r v * (1+2*point x r v)‖ ≤
      (|1+2*x|+2*r) * (2:ℝ)^(⌈3*(|x| *r+r^2/2)/2⌉ : ℤ) := by
  have ha : ‖1+2*point x r v‖ ≤ |1+2*x|+2*r := by
    rw [show 1+2*point x r v = ((1+2*x:ℝ):ℂ) + 2*(r:ℂ)*v by unfold point; push_cast; ring]
    apply (norm_add_le _ _).trans
    rw [Complex.norm_real, Real.norm_eq_abs]
    simp [abs_of_pos hr, hv]
  have hw : ‖weight x r v‖ ≤ Real.exp (|x| *r+r^2/2) := by
    rw [weight, Complex.norm_exp, Real.exp_le_exp]
    apply (Complex.re_le_norm _).trans ((norm_add_le _ _).trans _)
    simp [norm_pow, hv, abs_of_pos hr]
  rw [norm_mul, mul_comm ‖weight x r v‖]
  exact mul_le_mul ha (hw.trans (exp_le_two_zpow_ceil _ (by positivity))) (norm_nonneg _) (by positivity)

end Turan.Ratio
