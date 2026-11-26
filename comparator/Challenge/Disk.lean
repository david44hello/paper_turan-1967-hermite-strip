module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs

@[expose] public section
namespace Turan

theorem bounded_degree_disk (M : ℕ) :
    ∃ R : ℝ, 0 < R ∧ ∀ n m : ℕ, 2 ≤ n → n < m → m ≤ M → ∀ a b : ℂ,
      ∃ z : ℂ, (family n m a b).eval z = 0 ∧ ‖z‖ < R := by sorry

theorem high_mode_small_on_disk (K : ℝ) (hK : 0 ≤ K) :
    ∃ R : ℝ, K < R ∧ ∃ M : ℕ, ∀ n m : ℕ, 2 ≤ n → n < m → M ≤ m → ∀ a b : ℂ,
      (∀ w : ℂ, ‖w‖ ≤ R → (family n m a b).eval w ≠ 0) →
      ∀ z : ℂ, ‖z‖ ≤ K → ‖b*(hermite m).eval z / (family n m a b).eval z‖ < 1 := by sorry

theorem proposition_three :
    ∃ R : ℝ, 0 < R ∧ ∀ n m : ℕ, 2 ≤ n → n < m → ∀ a b : ℂ,
      (∃ z : ℂ, (family n m a b).eval z = 0 ∧ ‖z‖ < R) ∧
      (∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| < R) := by sorry

end Turan
