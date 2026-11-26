module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Normalized

@[expose] public section

namespace Turan

theorem lemma_twelve (m : ℕ) (hm : 1 ≤ m) (c : ℂ) (hx : |c.re| ≤ 2)
    (hy : |c.im| < 76/100) :
    ‖psi m c‖ ≤ Real.exp (8 + (76/100) * Real.sqrt (2 * (m : ℝ))) := by sorry

end Turan
