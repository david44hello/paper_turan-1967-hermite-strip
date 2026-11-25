-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.LowerTailScalarDetails
import Mathlib.Analysis.Complex.ExponentialBounds
namespace Turan.LowerTailSteps

theorem rounded_logTail_at_450 :
    |Real.log 2200000 - 14.6040| < 0.00005 ∧
    |5*Real.log 450 - 30.5462| < 0.00005 ∧
    |logTail 450 - (-12.6998)| < 0.00005 ∧
    deriv logTail 450 = -289/1800 := by
  let q : ℝ := 5632/5625
  have hq : 0 < q := by norm_num [q]
  have qu : Real.log q ≤ q-1 := Real.log_le_sub_one_of_pos hq
  have ql := Real.log_le_sub_one_of_pos (inv_pos.mpr hq)
  rw [Real.log_inv] at ql
  have h₁ : Real.log 2200000 =
      2*Real.log 3+9*Real.log 5-3*Real.log 2+Real.log q := by
    rw [show (2200000:ℝ) = (3^2*5^9/2^3)*q by norm_num [q],
      Real.log_mul (by norm_num) hq.ne',Real.log_div (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow,Real.log_pow,Real.log_pow]
    norm_num
  have h₂ : Real.log 450 = Real.log 2+2*Real.log 3+2*Real.log 5 := by
    rw [show (450:ℝ) = 2*3^2*5^2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow,Real.log_pow]
    norm_num
  have lo₁ : 14.603966 < Real.log 2200000 := by
    dsimp [q] at ql; linarith only [ql,h₁,Real.log_two_lt_d9,Real.log_three_gt_d9,Real.log_five_gt_d9]
  have hi₁ : Real.log 2200000 < 14.603970 := by
    dsimp [q] at qu; linarith only [qu,h₁,Real.log_two_gt_d9,Real.log_three_lt_d9,Real.log_five_lt_d9]
  have lo₂ : 30.546237 < 5*Real.log 450 := by
    linarith only [h₂,Real.log_two_gt_d9,Real.log_three_gt_d9,Real.log_five_gt_d9]
  have hi₂ : 5*Real.log 450 < 30.546239 := by
    linarith only [h₂,Real.log_two_lt_d9,Real.log_three_lt_d9,Real.log_five_lt_d9]
  refine ⟨abs_lt.mpr ⟨by linarith,by linarith⟩,abs_lt.mpr ⟨by linarith,by linarith⟩,?_,?_⟩
  · unfold logTail
    rw [show Real.sqrt (2*450:ℝ)=30 by norm_num]
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  · rw [(logTail_rate.1 450 (by simp)).deriv]
    norm_num

end Turan.LowerTailSteps
