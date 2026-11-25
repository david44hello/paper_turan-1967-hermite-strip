-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs

noncomputable section
namespace Turan

theorem cubic_shift_expansion (a b w : ℂ) :
    (family 2 3 a b).eval (w - 1/2) =
      2*w + a*(4*w^2-4*w-1) + b*(8*w^3-12*w^2-6*w+5) := by
  norm_num [family, hermite, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_add, nsmul_eq_mul]
  ring

theorem cubic_normalization (a b : ℂ) (hb : b ≠ 0) :
    let A := (4*a - 12*b)/(8*b)
    let B := (2 - 4*a - 6*b)/(8*b)
    let C₀ := (5*b - a)/(8*b)
    A + 4*C₀ = 1 ∧ ∀ w : ℂ, (family 2 3 a b).eval (w - 1/2) / (8*b) =
      w^3 + A*w^2 + B*w + C₀ := by
  dsimp only
  constructor
  · field_simp
    <;> ring
  · intro w
    rw [cubic_shift_expansion]
    field_simp
    <;> ring

theorem cubic_linear (z : ℂ) : (family 2 3 0 0).eval z = 0 ↔ z = -1/2 := by
  simp only [family, Polynomial.C_0, zero_mul, add_zero, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  constructor
  · intro hz
    linear_combination hz / 2
  · rintro rfl
    norm_num

end Turan
