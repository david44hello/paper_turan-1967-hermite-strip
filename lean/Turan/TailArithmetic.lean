module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

namespace Turan

private theorem exp_nat_lower (k : ℕ) : (2.7 : ℝ)^k ≤ Real.exp (k : ℝ) := by
  calc
    _ ≤ (Real.exp 1)^k := pow_le_pow_left₀ (by norm_num)
      (le_trans (by norm_num) Real.exp_one_gt_d9.le) _
    _ = _ := by simpa only [mul_one] using (Real.exp_nat_mul 1 k).symm

theorem tail_decay (m : ℝ) (hm : 450 ≤ m) :
    2200000*m^5*Real.exp (8+76/100*Real.sqrt (2*m)-197/1000*m) < 1 := by
  have hmpos : 0 < m := by linarith
  have h450 : Real.log 450 < 7 := (Real.log_lt_iff_lt_exp (by norm_num)).mpr
    (lt_of_lt_of_le (by norm_num) (exp_nat_lower 7))
  have hc : Real.log 2200000 < 15 := (Real.log_lt_iff_lt_exp (by norm_num)).mpr
    (lt_of_lt_of_le (by norm_num) (exp_nat_lower 15))
  have hlog := Real.log_le_sub_one_of_pos (show 0 < m/450 by positivity)
  rw [Real.log_div hmpos.ne' (by norm_num)] at hlog
  have hs : Real.sqrt (2*m) ≤ 30 + (m-450)/30 := by
    nlinarith only [Real.sq_sqrt (show 0 ≤ 2*m by positivity),
      sq_nonneg (Real.sqrt (2*m) - 30)]
  apply (Real.log_lt_log_iff (by positivity) zero_lt_one).mp
  rw [Real.log_mul (by positivity : 2200000*m^5 ≠ 0) (Real.exp_ne_zero _),
    Real.log_mul (by norm_num : (2200000 : ℝ) ≠ 0) (pow_ne_zero 5 hmpos.ne'),
    Real.log_pow, Real.log_exp, Real.log_one]
  linarith only [hm, h450, hc, hlog, hs]

private theorem log_five_upper : Real.log 5 < 1.612 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 7)
  norm_num [Finset.sum_range_succ, Nat.factorial_succ]

theorem lower_mode_exponent (m n X Y : ℝ) (hm : 450 ≤ m) (hn : 0 ≤ n)
    (hh : 2*n ≤ m) (hXY : 9*m/5-27/10 ≤ X^2-Y^2) (hY : Y^2 ≤ 1/m) :
    5*(1-(1:ℝ)/25)^(-(1:ℝ)/4) * Real.exp (X^2/6+Y^2/4+n/2*Real.log 5) <
      20*Real.exp (-197/1000*m) * Real.exp ((X^2-Y^2)/2) := by
  have hK : (1-(1:ℝ)/25)^(-(1:ℝ)/4) < 1.1 := by
    calc
      _ ≤ (1-(1:ℝ)/25)^(-(1:ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
      _ < _ := by rw [Real.rpow_neg_one]; norm_num
  have hY' : Y^2 ≤ 1/450 := hY.trans (one_div_le_one_div_of_le (by norm_num) hm)
  let b := -197/1000*m + (X^2-Y^2)/2
  have hexp : X^2/6 + Y^2/4 + n/2*Real.log 5 ≤ 0.91 + b := by
    dsimp only [b]
    have hnlog := mul_le_mul_of_nonneg_left log_five_upper.le
      (div_nonneg hn (by norm_num : (0 : ℝ) ≤ 2))
    linarith only [hnlog, hh, hXY, hY']
  have he : Real.exp 0.91 < 3 :=
    (Real.exp_le_exp.mpr (by norm_num : (0.91 : ℝ) ≤ 1)).trans_lt Real.exp_one_lt_three
  rw [mul_assoc 20, ← Real.exp_add]
  change _ < 20 * Real.exp b
  calc
    _ ≤ (5*1.1) * Real.exp (0.91+b) :=
      mul_le_mul (by linarith only [hK]) (Real.exp_le_exp.mpr hexp)
        (Real.exp_nonneg _) (by norm_num)
    _ = (5*1.1*Real.exp 0.91) * Real.exp b := by rw [Real.exp_add, ← mul_assoc]
    _ < _ := mul_lt_mul_of_pos_right (by linarith only [he]) (Real.exp_pos _)

theorem affine_mode_exponent (m X Y : ℝ) (hm : 450 ≤ m)
    (hXY : 9*m/5-27/10 ≤ X^2-Y^2) :
    15*Real.sqrt m < 20*Real.exp (-197/1000*m)*Real.exp ((X^2-Y^2)/2) := by
  have hs : Real.sqrt m ≤ 1 + m/4 := by
    nlinarith only [Real.sq_sqrt (show 0 ≤ m by linarith), sq_nonneg (Real.sqrt m - 2)]
  rw [mul_assoc 20, ← Real.exp_add]
  linarith only [hs, hm, hXY, Real.add_one_le_exp (-197/1000*m+(X^2-Y^2)/2)]

end Turan
