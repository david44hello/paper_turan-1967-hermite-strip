module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Hermite
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Polynomial
namespace Turan

private theorem raise_hermite (n : ℕ) :
    hermite (n+1) = 2 • (X * hermite n) - (hermite n).derivative := by
  cases n with
  | zero => simp [hermite, nsmul_eq_mul]
  | succ k =>
    change 2 * X * hermite (k+1) - _ = _
    rw [hermite_derivative]
    simp [nsmul_eq_mul, mul_assoc]

/-- Moving one derivative across the Gaussian inner product lowers the degree
on the opposite side. -/
theorem hermite_square_moment (L : Polynomial ℂ →ₗ[ℂ] ℂ)
    (parts : ∀ p, L p.derivative = 2 * L (X*p)) (n : ℕ) :
    L (hermite n ^ 2) = 2^n * (n.factorial : ℂ) * L 1 := by
  induction n with
  | zero => simp [hermite]
  | succ k ih =>
    let p := hermite k
    let q := hermite (k+1)
    have hprod := parts (p*q)
    rw [derivative_mul, map_add] at hprod
    have hstep : q^2 = 2 • (X*(p*q)) - p.derivative*q := by
      rw [pow_two, show q = 2 • (X*p) - p.derivative from raise_hermite k] at ⊢
      simp only [nsmul_eq_mul]
      ring
    change L (q^2) = _
    rw [hstep, map_sub, map_nsmul]
    have hqd : p * q.derivative = (2*(k+1)) • (p^2) := by
      dsimp only [q, p]
      rw [hermite_derivative, pow_two]
      simp only [nsmul_eq_mul]
      ring
    rw [hqd, map_nsmul] at hprod
    change L (p^2) = _ at ih
    rw [ih] at hprod
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
    simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at hprod ⊢
    linear_combination -hprod

/-- A shifted Gaussian reproduces the Hermite polynomial at the complex point z,
with one scale factor per degree. -/
theorem hermite_shifted_moment (L : Polynomial ℂ →ₗ[ℂ] ℂ) (s z : ℂ) (hs : 5*s^2=1)
    (parts : ∀ p, L p.derivative = (5/2)*L (X*p) - (5*s*z/2)*L p) (n : ℕ) :
    L (hermite n) = s^n * (hermite n).eval z * L 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [hermite]
  | one =>
    have hp := parts 1
    simp at hp
    rw [raise_hermite, hermite, derivative_one, sub_zero, mul_one, map_nsmul]
    norm_num [hermite, eval_mul, nsmul_eq_mul] at hp ⊢
    linear_combination -(4/5 : ℂ)*hp
  | more k ih₀ ih₁ =>
    have hp := parts (hermite (k+1))
    rw [hermite_derivative, map_nsmul, ih₀, ih₁] at hp
    rw [raise_hermite (k+1), map_sub, map_nsmul, hermite_derivative, map_nsmul, ih₀]
    simp only [eval_sub, eval_mul, eval_X, eval_ofNat, nsmul_eq_mul,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, pow_succ,
      eval_add, eval_natCast, eval_one] at hp ⊢
    linear_combination -(4/5 : ℂ)*hp +
      ((2/5 : ℂ)*(k+1)*s^k*(hermite k).eval z*L 1) * hs

end Turan
