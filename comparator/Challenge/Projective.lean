module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.ProjectiveDefs

@[expose] public section
namespace Turan

theorem quintic_chart_gap (check : QuinticChartCheck) (a b : ℂ) :
    ∃ z : ℂ, (family 3 5 a b).eval z = 0 ∧ |z.im| < 29491/32768 := by sorry

theorem sextic_chart_gap (check : SexticChartCheck) (n : ℕ) (hn : n = 2 ∨ n = 3 ∨ n = 4) (a b : ℂ) :
    ∃ z : ℂ, (family n 6 a b).eval z = 0 ∧ |z.im| < 57016/65536 := by sorry

end Turan
