-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.MiddleDefs
import Turan.ProjectiveDefs
namespace Turan

theorem figure_one_width (G1 : TrinomialDiskCheck) (middle : MiddleChecks)
    (F1 : QuinticChartCheck) (E10 : SexticChartCheck) (C : ℝ) :
    (∀ n m : ℕ, 2 ≤ n → n < m → ∀ a b : ℂ, ∃ z : ℂ,
      (family n m a b).eval z = 0 ∧ |z.im| ≤ C) ↔ h ≤ C := by sorry

theorem trinomial_exists_strip :
    ∃ A : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ a : ℂ,
      ∃ z : ℂ, 1+2*z+a*(hermite n).eval z = 0 ∧ |z.im| ≤ A := by sorry

theorem quadratic_trinomial_least_width :
    IsLeast {r : ℝ | ∀ a : ℂ, ∃ z : ℂ, 1+2*z+a*(hermite 2).eval z = 0 ∧ |z.im| ≤ r}
      (1/2) := by sorry

end Turan
