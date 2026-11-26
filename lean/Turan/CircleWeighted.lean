module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.CircleWeightedExpansion
public import Turan.ScaledFamily
public import Turan.Circles

@[expose] public section

open Metric
namespace Turan

/-- Bound the weighted affine term on the unit parameter circle. -/
private theorem weighted_affine_bound (x r : ℝ) (hr : 0 < r) (v : ℂ) (hv : ‖v‖ = 1) :
    let z := (x:ℂ) + r*v
    ‖normalizedCircleWeight x z * (1 + 2*z)‖ ≤
      (|1+2*x| + 2*r) * (2 : ℝ)^(⌈3*(|x| * r+r^2/2)/2⌉ : ℤ) := by
  let u := (r : ℂ)*v
  have hu : ‖u‖ = r := by simp [u, hv, abs_of_pos hr]
  have ha : ‖1 + 2*((x:ℂ)+u)‖ ≤ |1+2*x|+2*r := by
    rw [show 1+2*((x:ℂ)+u) = ((1+2*x:ℝ):ℂ) + 2*u by push_cast; ring]
    simpa only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_ofNat, hu] using
      norm_add_le ((1+2*x:ℝ):ℂ) (2*u)
  have hw : ‖normalizedCircleWeight x ((x:ℂ)+u)‖ ≤ Real.exp (|x| * r + r^2/2) := by
    rw [normalizedCircleWeight, Complex.norm_exp, Real.exp_le_exp,
      show ((x:ℂ)^2 - ((x:ℂ)+u)^2)/2 = -(x:ℂ)*u - u^2/2 by ring]
    apply (Complex.re_le_norm _).trans ((norm_sub_le _ _).trans _)
    simp [norm_pow, hu]
  dsimp only
  rw [norm_mul, mul_comm (|1+2*x|+2*r)]
  exact mul_le_mul (hw.trans (exp_le_two_zpow_ceil _ (by positivity))) ha (norm_nonneg _)
    (by positivity)

theorem circle_weighted_cut (w : CircleRow) (n m : ℕ) (a b : ℂ) (sign : ℝ)
    (hs : emptyStrip (scaledFamily n m a b) (87/100))
    (hphase : 0 ≤ sign*(a*star b).re) (hsign : sign = -1 ∨ sign = 1)
    (hv : w.valid n m sign) (hk : w.test = .weighted) : w.cut n m ‖a‖ ‖b‖ := by
  let x := w.x
  let r := w.r
  let d := weightedPivot n x r
  let e := weightedPivot m x r
  let D := a*(d:ℂ) + b*(e:ℂ)
  simp only [CircleRow.valid, hk, reduceCtorEq, false_or] at hv
  obtain ⟨hr, hstrip, hQn, hQm, hst, hde⟩ := hv
  change 0 < r at hr
  have hor : 0 ≤ (a*star b).re*d*e := by
    rcases hsign with rfl | rfl
    · change 0 ≤ -1*d*e at hde
      nlinarith only [mul_nonneg hphase hde]
    · change 0 ≤ 1*d*e at hde
      nlinarith only [mul_nonneg hphase hde]
  have hst' : (w.s:ℝ)^2 + (w.t:ℝ)^2 ≤ 100 := by exact_mod_cast hst
  have hproj := circle_coefficient_bound a b d e ((w.s:ℝ)/10) ((w.t:ℝ)/10) hor
    (by positivity) (by positivity) (by nlinarith only [hst'])
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs] at hproj
  let z (v : ℂ) := (x:ℂ) + r*v
  let F (v : ℂ) := normalizedCircleWeight x (z v) * scaledFamily n m a b (z v)
  let P (v : ℂ) := D*v
  have witness : ∃ v : ℂ, ‖v‖ = 1 ∧ ‖P v‖ ≤ ‖F v - P v‖ := by
    by_contra! h
    have hF : Differentiable ℂ F := by unfold F z normalizedCircleWeight scaledFamily; fun_prop
    have hP : Differentiable ℂ P := by unfold P; fun_prop
    obtain ⟨v, hin, hzero⟩ := circle_comparison (c := (0:ℂ)) zero_lt_one hF.differentiableOn hP.differentiableOn
      ⟨0, by simp, by simp [P]⟩ (fun v hv => h v (by simpa using mem_sphere.mp hv))
    have hball : z v ∈ closedBall (x:ℂ) r := by
      rw [mem_closedBall, dist_eq_norm]
      simp only [z, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr]
      exact mul_le_of_le_one_right hr.le (by simpa using (mem_ball.mp hin).le)
    exact hs _ (disk_in_strip _ _ _ _ (by simpa [r] using hstrip) hball)
      ((mul_eq_zero.mp hzero).resolve_left (Complex.exp_ne_zero _))
  obtain ⟨v, hv1, hbd⟩ := witness
  let rem (j : ℕ) := normalizedCircleWeight x (z v) * (scaledMode j).eval (z v) -
    (weightedPivot j x r : ℂ)*v
  let aff := normalizedCircleWeight x (z v) * (1+2*z v)
  have hid : F v - P v = aff + a*rem n + b*rem m := by
    dsimp [F, P, aff, rem, D, d, e, scaledFamily]
    ring
  rw [hid] at hbd
  have hlin : ‖D‖ ≤ ‖aff‖ + ‖a‖*‖rem n‖ + ‖b‖*‖rem m‖ := by
    calc
      ‖D‖ = ‖P v‖ := by simp [P, hv1]
      _ ≤ _ := hbd
      _ ≤ ‖aff + a*rem n‖ + ‖b*rem m‖ := norm_add_le _ _
      _ ≤ _ := by grw [norm_add_le]; simp only [norm_mul, le_refl]
  have hest : ‖D‖ ≤ (|1+2*x| + 2*r) * (2:ℝ)^(⌈3*(|x| * r+r^2/2)/2⌉ : ℤ) +
      ‖a‖*weightedError n x r + ‖b‖*weightedError m x r :=
    hlin.trans (add_le_add (add_le_add (weighted_affine_bound x r hr v hv1)
      (mul_le_mul_of_nonneg_left (weighted_mode_remainder n x r hr hQn v hv1.le) (norm_nonneg _)))
      (mul_le_mul_of_nonneg_left (weighted_mode_remainder m x r hr hQm v hv1.le) (norm_nonneg _)))
  simp only [CircleRow.cut, hk]
  change ‖a‖*((w.s:ℝ)/10*|d| - weightedError n x r) +
    ‖b‖*((w.t:ℝ)/10*|e| - weightedError m x r) ≤ _
  change _ ≤ ‖D‖ at hproj
  linarith only [hproj, hest]

end Turan
