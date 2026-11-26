module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TrinomialDefs
public import Turan.MiddleDefs
public import Turan.ProjectiveDefs

@[expose] public section
namespace Turan

theorem attained_height_maximum_given (G1 : TrinomialDiskCheck) (middle : MiddleChecks)
    (F1 : QuinticChartCheck) (E10 : SexticChartCheck) :
    IsGreatest {r : ℝ | ∃ (n m : ℕ), 2 ≤ n ∧ n < m ∧ ∃ a b : ℂ,
      IsLeast {t : ℝ | ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| = t} r} h := by sorry

end Turan
