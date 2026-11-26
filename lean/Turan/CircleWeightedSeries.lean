module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.CircleDefs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic

@[expose] public section

namespace Turan

/-- Beyond index twelve every successive factorial ratio is bounded by the
ratio used by the certificate. Sum that geometric majorant. -/
private theorem series_le_upper (Q : ℝ) (o : ℕ) (hQ : 0 < Q) (h36 : Q ≤ 36) (L : ℝ)
    (hL : HasSum (fun k : ℕ => Q^k / ((2*k+o).factorial : ℝ)) L) :
    L ≤ seriesUpper Q o := by
  let t (k : ℕ) := Q^k / ((2*k+o).factorial : ℝ)
  let R := Q / ((26 + (o : ℝ)) * (25 + (o : ℝ)))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : R < 1 := by
    dsimp [R]
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith [(Nat.cast_nonneg o : (0:ℝ) ≤ o), sq_nonneg (o : ℝ)]
  have step (k : ℕ) (hk : 12 ≤ k) : t (k+1) ≤ t k * R := by
    let l := 2*k+o
    have hrec : t (k+1) = t k * (Q / (((l:ℝ)+2)*((l:ℝ)+1))) := by
      simp only [t, show 2*(k+1)+o = l+2 by dsimp [l]; omega, Nat.factorial_succ,
        Nat.cast_mul, Nat.cast_succ, pow_succ]
      rw [show 2*k+o = l by rfl]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hrec]
    apply mul_le_mul_of_nonneg_left _ (by dsimp [t]; positivity)
    apply div_le_div_of_nonneg_left hQ.le (by positivity : 0 < (26+(o:ℝ))*(25+(o:ℝ)))
    have hl : 24+(o:ℝ) ≤ (l:ℝ) := by exact_mod_cast (show 24+o ≤ l by dsimp [l]; omega)
    exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have tail (i : ℕ) : t (i+13) ≤ t 12 * R * R^i := by
    induction i with
    | zero => simpa using step 12 (by decide)
    | succ i ih =>
      rw [pow_succ, ← mul_assoc]
      exact (step (i+13) (by omega)).trans (mul_le_mul_of_nonneg_right ih hR)
  have ht : HasSum t L := hL
  have hst := (summable_nat_add_iff 13).2 ht.summable
  have hg := (hasSum_geometric_of_lt_one hR hR1).mul_left (t 12 * R)
  have hle := hst.tsum_le_tsum tail hg.summable
  rw [hg.tsum_eq] at hle
  rw [← ht.tsum_eq, ← ht.summable.sum_add_tsum_nat_add 13]
  unfold seriesUpper
  push_cast
  apply add_le_add le_rfl
  exact hle

theorem cosh_sqrt_le_seriesUpper (Q : ℝ) (hQ : 0 < Q) (h36 : Q ≤ 36) :
    Real.cosh (Real.sqrt Q) ≤ seriesUpper Q 0 := by
  apply series_le_upper Q 0 hQ h36
  simpa only [add_zero, pow_mul, Real.sq_sqrt hQ.le] using Real.hasSum_cosh (Real.sqrt Q)

theorem sinh_sqrt_div_le_seriesUpper (Q : ℝ) (hQ : 0 < Q) (h36 : Q ≤ 36) :
    Real.sinh (Real.sqrt Q) / Real.sqrt Q ≤ seriesUpper Q 1 := by
  apply series_le_upper Q 1 hQ h36
  convert (Real.hasSum_sinh (Real.sqrt Q)).div_const (Real.sqrt Q) using 1
  funext k
  rw [pow_succ, pow_mul, Real.sq_sqrt hQ.le]
  field_simp [(Real.sqrt_pos.mpr hQ).ne']

theorem exp_le_two_zpow_ceil (t : ℝ) (ht : 0 ≤ t) :
    Real.exp t ≤ (2 : ℝ) ^ (⌈3*t/2⌉ : ℤ) := by
  rw [← Real.log_le_log_iff (Real.exp_pos _) (by positivity), Real.log_exp, Real.log_zpow]
  have hlog : 2/3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  calc
    t = (3*t/2)*(2/3) := by ring
    _ ≤ _ := mul_le_mul (Int.le_ceil _) hlog (by norm_num)
      ((by positivity : 0 ≤ 3*t/2).trans (Int.le_ceil _))

end Turan
