-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.ScaledFamily
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace Turan.Giroux

private theorem scaled_weight (j : ℕ) :
    Real.sqrt (scaledNormSq j : ℝ) = 128^j * Real.sqrt (2^j*(j.factorial:ℝ)) := by
  rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 128^j by positivity), ← Real.sqrt_mul (by positivity)]
  congr 1
  simp only [scaledNormSq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← mul_assoc, ← pow_mul, Nat.mul_comm j 2, pow_mul, ← mul_pow]
  norm_num

theorem circle_cut_of_bound (w : CircleRow) (n m : ℕ) (a b : ℂ)
    (hs : emptyStrip (scaledFamily n m a b) (87/100)) (hk : w.test = .giroux)
    (H : ∀ A B : ℂ, emptyStrip (normalizedFamily n m A B) (87/100) →
      (87/100)*Real.sqrt (2*(m:ℝ))*‖B‖ ≤ Real.sqrt 3 + ‖A‖) :
    w.cut n m ‖a‖ ‖b‖ := by
  let weight (j : ℕ) := Real.sqrt (scaledNormSq j : ℝ)
  have hmode (j : ℕ) (z : ℂ) : (weight j : ℂ) * psi j z = (scaledMode j).eval z := by
    have hpos : 0 < Real.sqrt (2^j*(j.factorial:ℝ)) := by
      have := Nat.factorial_pos j; positivity
    simp only [weight, scaled_weight, psi, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_ofNat, scaledMode, eval_mul, eval_C]
    have hne : (Real.sqrt (2^j*(j.factorial:ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [mul_assoc, ← mul_div_assoc, mul_comm (Real.sqrt _ : ℂ), mul_div_cancel_right₀ _ hne]
  have h := H (a * weight n) (b * weight m) (by
    intro z hz
    simpa only [normalizedFamily, mul_assoc, hmode, scaledFamily] using hs z hz)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, weight,
    abs_of_nonneg (Real.sqrt_nonneg _)] at h
  simp only [CircleRow.cut, hk]
  have hleft := Real.nat_sqrt_le_real_sqrt (a := 2*m*scaledNormSq m)
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by positivity)] at hleft
  have hright := Real.real_sqrt_le_nat_sqrt_succ (a := scaledNormSq n)
  have hthree : Real.sqrt 3 ≤ 1733/1000 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  calc
    _ ≤ (87/100) * (Real.sqrt (2*(m:ℝ)) * Real.sqrt (scaledNormSq m : ℝ)) * ‖b‖ := by gcongr
    _ = _ := by ring
    _ ≤ _ := h
    _ ≤ 1733/1000 + ((scaledNormSq n).sqrt+1:ℝ)*‖a‖ := by
      rw [mul_comm ‖a‖]
      gcongr

end Turan.Giroux
