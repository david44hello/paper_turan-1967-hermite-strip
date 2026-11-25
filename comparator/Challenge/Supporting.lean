-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs

open Polynomial
namespace Turan

theorem polynomial_has_lowest_zero (p : Polynomial ℂ) (hp : 0 < p.natDegree) :
    ∃ z : ℂ, p.eval z = 0 ∧ ∀ w : ℂ, p.eval w = 0 → |z.im| ≤ |w.im| := by sorry

theorem cubic_shifted_factorization (a b : ℂ) (hb : b ≠ 0) :
    ∃ x y v : ℂ, rootRelation x y v ∧
      (family 2 3 a b).comp (X - C (1 / 2)) =
        C (8 * b) * (X - C x) * (X - C y) * (X - C v) := by sorry

theorem cubic_shifted_zero_iff (a b x y v : ℂ) (hb : b ≠ 0)
    (hfac : (family 2 3 a b).comp (X - C (1 / 2)) =
      C (8 * b) * (X - C x) * (X - C y) * (X - C v)) (z : ℂ) :
    (family 2 3 a b).eval z = 0 ↔
      z + 1 / 2 = x ∨ z + 1 / 2 = y ∨ z + 1 / 2 = v := by sorry

theorem cubic_triple_root_coefficients (a b w : ℂ)
    (hfac : (family 2 3 a b).comp (X - C (1 / 2)) = C (8 * b) * (X - C w) ^ 3) :
    b * (12 * w ^ 2 - 12 * w + 9) = 1 ∧ a = (3 - 6 * w) * b := by sorry

theorem quadratic_half_disk (a : ℂ) :
    ∃ z : ℂ, (family 2 3 a 0).eval z = 0 ∧ ‖z + 1/2‖ ≤ 1/2 := by sorry

theorem cubic_zero_b_half_strip (a : ℂ) :
    ∃ z : ℂ, (family 2 3 a 0).eval z = 0 ∧ |z.im| ≤ 1/2 := by sorry

end Turan
