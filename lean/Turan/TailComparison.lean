-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

public section

namespace Turan

private theorem exp_integer_lower (k : ℕ) : (2.718 : ℝ)^k ≤ Real.exp (k : ℝ) := by
  calc
    _ ≤ (Real.exp 1)^k := pow_le_pow_left₀ (by norm_num1)
      (le_trans (by norm_num1) Real.exp_one_gt_d9.le) _
    _ = _ := by simpa only [mul_one] using (Real.exp_nat_mul 1 k).symm

private theorem exp_lower_small : 225000 < Real.exp (12 + 3/8) := by
  have h₁ : 160000 ≤ Real.exp 12 :=
    le_trans (by norm_num1) (exp_integer_lower 12)
  have h₂ := Real.quadratic_le_exp_of_nonneg (by norm_num1 : (0 : ℝ) ≤ 3/8)
  rw [Real.exp_add]
  exact lt_of_lt_of_le (by norm_num1)
    (mul_le_mul h₁ h₂ (by norm_num1) (Real.exp_nonneg _))

/-- Beyond the last split the numerator bound grows linearly in the index,
so it suffices to retain a quadratic in the square-root variable. -/
private theorem exp_lower_large (s : ℝ) (hs : 29 ≤ s) :
    24000000 * (s/29)^2 ≤ Real.exp ((608/1000)*s - 315/1000) := by
  have h₁ : 24000000 ≤ Real.exp 17 :=
    le_trans (by norm_num1) (exp_integer_lower 17)
  have h₂ : s/29 ≤ Real.exp (s/29 - 1) := by
    linarith only [Real.add_one_le_exp (s/29 - 1)]
  calc
    _ ≤ Real.exp 17 * (Real.exp (s/29 - 1))^2 :=
      mul_le_mul h₁ (pow_le_pow_left₀ (by linarith) h₂ 2) (sq_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (17 + ((s/29 - 1) + (s/29 - 1))) := by rw [Real.exp_add, Real.exp_add, pow_two]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hs])

theorem tail_numeric_compare (n m j : ℕ) (hm : 450 ≤ m) (hhalf : m ≤ 2*n)
    (hnm : n < m) (hj : j=n ∨ j=m) :
    Real.log (50000*(m:ℝ)^2 / ((j:ℝ)*((m:ℝ)-(n:ℝ)))) <
      (608/1000)*Real.sqrt (2*(j:ℝ)-1125/100) - 315/1000 := by
  have hm' : (450 : ℝ) ≤ m := by exact_mod_cast hm
  have hhalf' : (m : ℝ) ≤ 2*n := by exact_mod_cast hhalf
  have hgap : (n : ℝ) + 1 ≤ m := by exact_mod_cast (show n + 1 ≤ m by omega)
  have hnj : (n : ℝ) ≤ j := by exact_mod_cast (show n ≤ j by rcases hj with rfl | rfl <;> omega)
  have hjpos : 0 < (j : ℝ) := by linarith
  have hgap_pos : 0 < (m : ℝ) - n := by linarith
  have hmpos : 0 < (m : ℝ) := by linarith
  have hden := mul_le_mul_of_nonneg_right hnj hgap_pos.le
  let s := Real.sqrt (2*(j : ℝ) - 1125/100)
  change Real.log _ < (608/1000)*s - 315/1000
  apply (Real.log_lt_iff_lt_exp (by positivity)).mpr
  by_cases hlo : (n : ℝ) ≤ 2*m/3
  · -- On this interval n(m-n) ≥ 2m²/9.
    have hp := mul_nonneg (show 0 ≤ (n : ℝ) - m/3 by linarith)
      (sub_nonneg.mpr hlo)
    have hs : 20.9 ≤ s := Real.le_sqrt_of_sq_le (by linarith only [hm', hhalf', hnj])
    calc
      _ ≤ 225000 := (div_le_iff₀ (mul_pos hjpos hgap_pos)).mpr (by nlinarith only [hp, hden])
      _ < _ := exp_lower_small
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hs])
  by_cases hmid : (n : ℝ) ≤ 19*m/20
  · -- On this interval n(m-n) ≥ 19m²/400.
    have hp := mul_nonneg (show 0 ≤ (n : ℝ) - m/20 by linarith)
      (sub_nonneg.mpr hmid)
    have hs : 24 ≤ s := Real.le_sqrt_of_sq_le (by linarith only [hlo, hm', hnj])
    calc
      _ ≤ 1100000 := (div_le_iff₀ (mul_pos hjpos hgap_pos)).mpr (by
        nlinarith only [hp, hden, sq_nonneg (m : ℝ)])
      _ < Real.exp 14 := lt_of_lt_of_le (by norm_num1) (exp_integer_lower 14)
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hs])
  -- For near neighbors the integer gap gives j(m-n) ≥ 19m/20.
  have hd : 19*(m : ℝ)/20 ≤ j*((m : ℝ)-n) := by
    calc
      _ ≤ (j : ℝ) := by linarith only [hmid, hnj]
      _ ≤ _ := le_mul_of_one_le_right hjpos.le (by linarith only [hgap])
  have hs : 29 ≤ s := Real.le_sqrt_of_sq_le (by linarith only [hmid, hm', hnj])
  have hsq : s^2 = 2*(j : ℝ) - 1125/100 :=
    Real.sq_sqrt (by linarith only [hm', hhalf', hnj])
  calc
    _ ≤ 53000*(m : ℝ) := (div_le_iff₀ (mul_pos hjpos hgap_pos)).mpr (by
      nlinarith only [mul_le_mul_of_nonneg_left hd hmpos.le, sq_nonneg (m : ℝ)])
    _ < 24000000*(s/29)^2 := by nlinarith only [hsq, hmid, hm', hnj]
    _ ≤ _ := exp_lower_large s hs

end Turan
