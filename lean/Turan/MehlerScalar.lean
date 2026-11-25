-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs

namespace Turan

private theorem mehler_prefactor_sq :
    ((1 - (1 : ℝ)/25) ^ (-(1 : ℝ)/4)) ^ 2 = 5/4 * Real.sqrt (2/3) := by
  apply (sq_eq_sq₀ (sq_nonneg _) (by positivity)).mp
  rw [← pow_mul, ← Real.rpow_mul_natCast (by norm_num : 0 ≤ 1 - (1 : ℝ)/25),
    mul_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- The scalar Gaussian bound after taking the nonnegative square root. -/
theorem mehler_scalar (n : ℕ) (x y U : ℝ) (hU : 0 ≤ U)
    (hc : U^2 * (1/5 : ℝ)^n * (4*Real.pi/5) * Real.exp ((x^2-y^2)/2) ≤
      Real.pi * Real.sqrt (2/3) * Real.exp (5*x^2/6)) :
    U * Real.exp (-x^2/2) ≤ (1-(1 : ℝ)/25) ^ (-(1 : ℝ)/4) *
      Real.exp (-x^2/3+y^2/4+((n : ℝ)/2)*Real.log 5) := by
  let a := (x^2-y^2)/2 - (n : ℝ) * Real.log 5
  have ha : Real.exp a = Real.exp ((x^2-y^2)/2) * (1/5 : ℝ)^n := by
    rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
    simp [div_eq_mul_inv]
  have hsq : U^2 * Real.exp a ≤ (5/4 * Real.sqrt (2/3)) * Real.exp (5*x^2/6) := by
    apply (mul_le_mul_iff_left₀ (by positivity : 0 < 4*Real.pi/5)).mp
    rw [ha]
    convert hc using 1 <;> ring
  -- Both squared sides have the same remaining exponential factor.
  let b := -x^2 - a
  have hl : Real.exp (-x^2/2)^2 = Real.exp a * Real.exp b := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp only [b]
    ring
  have hr : Real.exp (-x^2/3+y^2/4+((n : ℝ)/2)*Real.log 5)^2 =
      Real.exp (5*x^2/6) * Real.exp b := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp only [b, a]
    ring
  have hbase : 0 < 1 - (1 : ℝ)/25 := by norm_num
  apply (sq_le_sq₀ (mul_nonneg hU (Real.exp_pos _).le) (by positivity)).mp
  rw [mul_pow, mul_pow, mehler_prefactor_sq, hl, hr]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hsq (Real.exp_pos b).le

end Turan
