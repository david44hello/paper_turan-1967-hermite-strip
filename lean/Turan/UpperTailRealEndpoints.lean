module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set
namespace Turan.UpperTailReal

def lhs (j : ℝ) := 0.608 * Real.sqrt (2*j - 11.25) - 0.315
def rhs (m n j : ℝ) := Real.log (50000*m^2 / (j*(m-n)))
def margin (m n : ℝ) := lhs n - rhs m n n
def rightMinorant (m : ℝ) := 0.608 * Real.sqrt (2*m - 13.25) - 0.315 - Real.log (50200*m)
def domain : Set (ℝ × ℝ) := {p | 450 ≤ p.1 ∧ p.1/2 ≤ p.2 ∧ p.2 ≤ p.1-1}

private theorem half_log (m : ℝ) (hm : m ≠ 0) :
    rhs m (m/2) (m/2) = Real.log 200000 := by
  unfold rhs
  congr 1
  field_simp [hm, show m-m/2 ≠ 0 by intro h; apply hm; linarith]
  ring

theorem margin_half_eq (m : ℝ) (hm : m ≠ 0) :
    margin m (m/2) = 0.608*Real.sqrt (m-11.25)-0.315-Real.log 200000 := by
  rw [margin, half_log m hm, lhs, show 2*(m/2) = m by ring]

private theorem log_left_bounds : 12.206 < Real.log 200000 ∧ Real.log 200000 < 12.2061 := by
  rw [show (200000:ℝ) = 2^6 * 5^5 by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
  constructor
  · linarith only [Real.log_two_gt_d9, Real.log_five_gt_d9]
  · linarith only [Real.log_two_lt_d9, Real.log_five_lt_d9]

private theorem lhs_left_bounds : 12.4203 < lhs 225 ∧ lhs 225 < 12.421 := by
  have h₁ : (20.9463:ℝ) < Real.sqrt (2*225-11.25) := Real.lt_sqrt_of_sq_lt (by norm_num)
  have h₂ : Real.sqrt (2*225-11.25) < 20.9464 := (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  unfold lhs
  constructor <;> linarith

theorem left_endpoint (m : ℝ) (hm : 450 ≤ m) :
    rhs m (m/2) (m/2) = Real.log 200000 ∧
    margin m (m/2) = 0.608*Real.sqrt (m-11.25)-0.315-Real.log 200000 ∧
    12.4203 < lhs 225 ∧ Real.log 200000 < 12.2061 ∧
    (0.214 : ℝ) < 12.4203-12.2061 ∧ margin 450 225 < 0.215 := by
  have hne : m ≠ 0 := by linarith
  refine ⟨half_log m hne, margin_half_eq m hne, lhs_left_bounds.1, log_left_bounds.2, by norm_num, ?_⟩
  have h := half_log 450 (by norm_num)
  norm_num1 at h
  rw [margin, h]
  linarith only [lhs_left_bounds.2, log_left_bounds.1]

/-- Factor out 22500000. The remaining logarithm is below 0.004. -/
private theorem log_right_upper : Real.log (50200*450) < 16.9331 := by
  rw [show (50200*450:ℝ) = (2^5*3^2)*(5^7)*1.004 by norm_num]
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow, Real.log_pow]
  linarith only [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9,
    Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 1.004)]

theorem right_endpoint (m : ℝ) (hm : 450 ≤ m) :
    50000*m/(m-1) ≤ 50000*450/449 ∧ (50000*450/449 : ℝ) < 50200 ∧
    rhs m (m-1) (m-1) ≤ Real.log (50200*m) ∧ rightMinorant m ≤ margin m (m-1) ∧
    17.7902 < lhs 449 ∧ Real.log (50200*450) < 16.9331 ∧
    (0.857 : ℝ) < 17.7902-16.9331 := by
  have hpos : 0 < m := by linarith
  have hden : 0 < m-1 := by linarith
  have hrat : 50000*m/(m-1) ≤ 50000*450/449 := (div_le_iff₀ hden).mpr (by linarith)
  have hlog : rhs m (m-1) (m-1) ≤ Real.log (50200*m) := by
    rw [rhs, show m-(m-1) = 1 by ring, mul_one]
    apply Real.log_le_log (by positivity)
    calc
      _ = (50000*m/(m-1))*m := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrat.trans (by norm_num)) hpos.le
  refine ⟨hrat, by norm_num, hlog, ?_, ?_, log_right_upper, by norm_num⟩
  · rw [rightMinorant, margin, lhs, show 2*(m-1)-11.25 = 2*m-13.25 by ring]
    linarith only [hlog]
  · have h : (29.7783:ℝ) < Real.sqrt (2*449-11.25) := Real.lt_sqrt_of_sq_lt (by norm_num)
    unfold lhs
    linarith

end Turan.UpperTailReal
