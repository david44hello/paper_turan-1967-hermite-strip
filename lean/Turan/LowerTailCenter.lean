module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Hermite
public import Turan.Normalized
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Filter Metric Set Polynomial
open scoped ComplexConjugate Topology
namespace Turan.LowerTailSteps

private theorem center_square (k : ℕ) :
    ((hermite (2*k)).eval 0)^2 = ((2*k).factorial : ℂ) * (k.centralBinom : ℂ) := by
  induction k with
  | zero => norm_num [hermite, Nat.centralBinom]
  | succ k ih =>
    have hb : ((k:ℂ)+1) * ((k+1).centralBinom : ℂ) =
        2*(2*(k:ℂ)+1)*(k.centralBinom : ℂ) := by exact_mod_cast Nat.succ_mul_centralBinom_succ k
    rw [show 2*(k+1) = 2*k+2 by omega, hermite]
    simp only [eval_sub, eval_mul, eval_X, mul_zero, zero_mul, zero_sub, eval_smul,
      nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, neg_sq, mul_pow, ih,
      Nat.factorial_succ]
    push_cast
    simp only [eval_ofNat, eval_add, eval_mul, eval_natCast, eval_one]
    linear_combination -(2*(2*(k:ℂ)+1)*((2*k).factorial : ℂ))*hb

theorem even_center (k : ℕ) :
    (psi (2*k) 0)^2 = (((((2*k).choose k : ℕ) : ℝ) / 4^k : ℝ) : ℂ) ∧
    1 / (2*(k:ℝ)+1) ≤ ‖psi (2*k) 0‖^2 := by
  have hfac : ((2*k).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero (2*k))
  have hsq : (psi (2*k) 0)^2 = (((2*k).choose k : ℂ) / 4^k) := by
    rw [psi, div_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity), center_square]
    push_cast
    rw [← Nat.centralBinom_eq_two_mul_choose, pow_mul]
    norm_num
    field_simp
  refine ⟨by simpa using hsq, ?_⟩
  have hn := congrArg norm hsq
  simp only [norm_pow, norm_div, Complex.norm_natCast, Complex.norm_ofNat] at hn
  rw [hn, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [mul_comm (((2*k).choose k : ℝ))]
  simpa [Nat.centralBinom_eq_two_mul_choose] using
    (show (4:ℝ)^k ≤ (2*(k:ℝ)+1)*(k.centralBinom : ℝ) by
      exact_mod_cast Nat.four_pow_le_two_mul_add_one_mul_centralBinom k)

end Turan.LowerTailSteps
