module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.CircleDefs
public import Turan.TailDefs

@[expose] public section
namespace Turan

theorem giroux_family (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m) (a b : ℂ)
    (hs : emptyStrip (normalizedFamily n m a b) (87/100)) :
    (87/100)*Real.sqrt (2*(m:ℝ))*‖b‖ ≤ Real.sqrt 3 + ‖a‖ := by sorry

theorem circle_certificate_gap (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m)
    (check : CircleCertificate n m) (a b : ℂ) :
    ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| < 87/100 := by sorry

end Turan
