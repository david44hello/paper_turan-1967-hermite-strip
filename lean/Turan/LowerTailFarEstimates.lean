module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.LowerComparison
public import Turan.LargeCircleEnergy

@[expose] public section

noncomputable section
open Filter Metric Set Polynomial
open scoped ComplexConjugate Topology
namespace Turan.LowerTailSteps

def farInterval (m : ℕ) : Set ℝ :=
  Icc (Real.sqrt (9 * (m : ℝ) / 5))
    (Real.sqrt (9 * (m : ℝ) / 5) + 3 * Real.pi / Real.sqrt m)

private theorem far_geometry (m : ℕ) (hm : 450 ≤ m) (x : ℝ) (hx : x ∈ farInterval m) :
    0 ≤ x ∧ x ≤ 1.363 * Real.sqrt m := by
  let s := Real.sqrt (m:ℝ)
  have h : (450:ℝ) ≤ m := by exact_mod_cast hm
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hsq : s^2 = (m:ℝ) := Real.sq_sqrt (by positivity)
  have ha : Real.sqrt (9*(m:ℝ)/5) ≤ 1.342*s :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp (by rw [Real.sq_sqrt (by positivity)]; nlinarith only [hsq,h])
  have hb : 3*Real.pi/s ≤ 0.021*s := (div_le_iff₀ hs).mpr (by nlinarith only [hsq,h,Real.pi_lt_d2])
  exact ⟨(Real.sqrt_nonneg _).trans hx.1, by linarith only [hx.2, ha, hb]⟩

theorem far_potential (m : ℕ) (hm : 450 ≤ m) (t : ℝ) (ht : t ∈ farInterval m) :
    (14 / 100 : ℝ) * m < 2 * (m : ℝ) + 1 - t ^ 2 := by
  obtain ⟨ht0, ht1⟩ := far_geometry m hm t ht
  have h := (sq_le_sq₀ ht0 (by positivity)).mpr ht1
  nlinarith only [h, Real.sq_sqrt (Nat.cast_nonneg m : (0:ℝ) ≤ m), Nat.cast_nonneg (α := ℝ) m]

theorem far_zero_slope (m : ℕ) (hm : 450 ≤ m) (x : ℝ) (hx : x ∈ farInterval m)
    (hz : psi m (x : ℂ) = 0) :
    (26 / 100 : ℝ) < ‖deriv (phi m) (x : ℂ)‖ := by
  apply lt_of_lt_of_le _ (Complex.abs_re_le_norm _)
  apply largeCircle_slope_sharp m hm x (far_geometry m hm x hx).1 _ hz
  linarith only [far_potential m hm x hx, Nat.cast_nonneg (α := ℝ) m]

theorem far_affine (m : ℕ) (hm : 450 ≤ m) (x : ℝ) (hx : x ∈ farInterval m)
    (z : ℂ) (hz : ‖z - (x : ℂ)‖ = 1 / Real.sqrt m) :
    ‖1 + 2*z‖ < (278 / 100 : ℝ) * Real.sqrt m := by
  obtain ⟨hx0, hx1⟩ := far_geometry m hm x hx
  let s := Real.sqrt (m:ℝ)
  have h : (450:ℝ) ≤ m := by exact_mod_cast hm
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hsq : s^2 = (m:ℝ) := Real.sq_sqrt (by positivity)
  have h21 : 21 ≤ s := by nlinarith
  have hr : 1/s ≤ s/450 := (div_le_iff₀ hs).mpr (by nlinarith only [h,hsq])
  have hzn := norm_add_le (z-(x:ℂ)) (x:ℂ)
  rw [sub_add_cancel,hz,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx0] at hzn
  have ha := norm_add_le (1:ℂ) (2*z)
  norm_num [norm_mul] at ha
  change x ≤ 1.363*s at hx1
  change ‖z‖ ≤ 1/s+x at hzn
  change _ < 278/100*s
  linarith only [hx1, hzn, ha, hr, h21]

theorem far_affine_ratio (m : ℕ) (hm : 450 ≤ m) (x : ℝ) (hx : x ∈ farInterval m)
    (z : ℂ) (hz : ‖z - (x : ℂ)‖ = 1 / Real.sqrt m)
    (hφ : 1 / (5 * Real.sqrt m) < ‖phi m z‖) :
    ‖1 + 2*z‖ < 55 * (m : ℝ) * Real.exp (-(9/10 : ℝ) * m) * ‖psi m z‖ := by
  have h : (450:ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨hxy,_,_⟩ := circle_geometry m x h hx.1 hx.2 z hz
  let A := (z.re^2-z.im^2)/2
  have hA : 0.9*(m:ℝ)-A ≤ 1.35 := by dsimp [A]; linarith only [hxy]
  have hφeq : ‖phi m z‖ = Real.exp (-A) * ‖psi m z‖ := by
    rw [phi, norm_mul, Complex.norm_exp]
    congr 2
    norm_num [A, Complex.div_ofNat_re, Complex.neg_re, sq, Complex.mul_re]
    ring
  have hs : 0 < Real.sqrt (m:ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hroot := (div_lt_iff₀ (show 0 < 5*Real.sqrt (m:ℝ) by positivity)).mp hφ
  rw [hφeq] at hroot
  have hnum : Real.exp 1.35 < 3.95 := by
    rw [show (1.35:ℝ)=1+0.35 by norm_num, Real.exp_add]
    have he := Real.exp_bound' (x := 0.35) (by norm_num) (by norm_num) (n := 4) (by decide)
    norm_num [Finset.sum_range_succ, Nat.factorial_succ] at he
    nlinarith only [mul_le_mul Real.exp_one_lt_d9.le he (Real.exp_nonneg _) (by norm_num : 0 ≤ (2.7182818286:ℝ))]
  have hex : Real.exp (-A) ≤ 3.95 * Real.exp (-(9/10:ℝ)*m) := by
    rw [show -A = (0.9*(m:ℝ)-A) + (-(9/10:ℝ)*m) by ring, Real.exp_add]
    gcongr
    exact (Real.exp_le_exp.mpr hA).trans hnum.le
  have hscaled := mul_lt_mul_of_pos_left hroot (show 0 < 2.78 * Real.sqrt (m:ℝ) by positivity)
  have hbound := mul_le_mul_of_nonneg_right hex (show 0 ≤ 2.78*5*(m:ℝ)*‖psi m z‖ by positivity)
  have heq := Real.sq_sqrt (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  apply (far_affine m hm x hx z hz).trans_le
  nlinarith only [hscaled, hbound, mul_nonneg (Real.exp_nonneg (-(9/10:ℝ)*m)) (mul_nonneg (Nat.cast_nonneg m) (norm_nonneg (psi m z))), congrArg (fun t : ℝ => 2.78*5*t*(Real.exp (-A)*‖psi m z‖)) heq]

end Turan.LowerTailSteps
