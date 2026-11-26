module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs

@[expose] public section

noncomputable section
open Polynomial
open scoped ComplexConjugate
namespace Turan

theorem hermite_low : hermite 2 = 4 * X ^ 2 - 2 ∧ hermite 3 = 8 * X ^ 3 - 12 * X := by sorry

theorem hermite_degree (j : ℕ) :
    (hermite j).natDegree = j ∧ (hermite j).leadingCoeff = 2 ^ j := by sorry

theorem hermite_derivative (j : ℕ) :
    (hermite (j + 1)).derivative = (2 * (j + 1)) • hermite j := by sorry

theorem hermite_equation (j : ℕ) :
    (hermite j).derivative.derivative - 2 * X * (hermite j).derivative =
      -((2 * j) • hermite j) := by sorry

theorem hermite_symmetry (j : ℕ) (z : ℂ) :
    (hermite j).eval (conj z) = conj ((hermite j).eval z) ∧
    (hermite j).eval (-z) = (-1 : ℂ)^j * (hermite j).eval z := by sorry

theorem family_degree (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m) (a b : ℂ) :
    (family n m a b).natDegree = if b ≠ 0 then m else if a ≠ 0 then n else 1 := by sorry

theorem family_has_lowest_zero (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m) (a b : ℂ) :
    ∃ z : ℂ, (family n m a b).eval z = 0 ∧
      ∀ w : ℂ, (family n m a b).eval w = 0 → |z.im| ≤ |w.im| := by sorry

theorem cubic_shift_expansion (a b w : ℂ) :
    (family 2 3 a b).eval (w - 1/2) =
      2*w + a*(4*w^2-4*w-1) + b*(8*w^3-12*w^2-6*w+5) := by sorry

theorem cubic_normalization (a b : ℂ) (hb : b ≠ 0) :
    let A := (4*a - 12*b)/(8*b)
    let B := (2 - 4*a - 6*b)/(8*b)
    let C₀ := (5*b - a)/(8*b)
    A + 4*C₀ = 1 ∧ ∀ w : ℂ, (family 2 3 a b).eval (w - 1/2) / (8*b) =
      w^3 + A*w^2 + B*w + C₀ := by sorry

theorem cubic_linear (z : ℂ) : (family 2 3 0 0).eval z = 0 ↔ z = -1/2 := by sorry

end Turan
