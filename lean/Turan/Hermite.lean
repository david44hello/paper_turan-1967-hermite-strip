-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs

noncomputable section
open Polynomial
open scoped ComplexConjugate
namespace Turan

private theorem hermite_step (j : ℕ) :
    hermite (j + 2) = 2 * X * hermite (j + 1) - (2 * (j + 1)) • hermite j := rfl

theorem hermite_low : hermite 2 = 4 * X ^ 2 - 2 ∧ hermite 3 = 8 * X ^ 3 - 12 * X := by
  constructor <;> norm_num [hermite, nsmul_eq_mul] <;> ring

/-- The lowering and raising identities propagate together through the recurrence. -/
private theorem hermite_ladder (j : ℕ) :
    (hermite (j + 1)).derivative = (2 * (j + 1)) • hermite j ∧
    2 * X * hermite j - (hermite j).derivative = hermite (j + 1) := by
  induction j with
  | zero => norm_num [hermite, derivative_mul, nsmul_eq_mul]
  | succ j ih =>
    obtain ⟨lower, raise⟩ := ih
    constructor
    · rw [hermite_step j, derivative_sub, derivative_mul, derivative_smul, lower]
      simp only [derivative_mul, derivative_ofNat, derivative_X, zero_mul, mul_one,
        zero_add, nsmul_eq_mul, Nat.cast_mul, Nat.cast_succ]
      linear_combination (2 * ((j : Polynomial ℂ) + 1)) * raise
    · rw [hermite_step j, lower]

theorem hermite_derivative (j : ℕ) :
    (hermite (j + 1)).derivative = (2 * (j + 1)) • hermite j :=
  (hermite_ladder j).1

theorem hermite_equation (j : ℕ) :
    (hermite j).derivative.derivative - 2 * X * (hermite j).derivative =
      -((2 * j) • hermite j) := by
  have hdiff := congrArg (derivative (R := ℂ)) (hermite_ladder j).2
  simp only [derivative_sub, derivative_mul, derivative_ofNat, derivative_X,
    zero_mul, mul_one, zero_add, hermite_derivative] at hdiff
  simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_succ] at hdiff ⊢
  linear_combination -hdiff

theorem hermite_symmetry (j : ℕ) (z : ℂ) :
    (hermite j).eval (conj z) = conj ((hermite j).eval z) ∧
    (hermite j).eval (-z) = (-1 : ℂ)^j * (hermite j).eval z := by
  induction j using Nat.twoStepInduction with
  | zero => simp [hermite]
  | one => simp [hermite, eval_mul, map_ofNat]
  | more j ih₀ ih₁ =>
    rw [hermite_step j]
    simp only [eval_sub, eval_mul, eval_X, eval_ofNat, eval_smul]
    constructor
    · rw [ih₀.1, ih₁.1]
      simp [nsmul_eq_mul, map_ofNat]
    · rw [ih₀.2, ih₁.2]
      simp only [pow_succ, nsmul_eq_mul]
      ring

end Turan
