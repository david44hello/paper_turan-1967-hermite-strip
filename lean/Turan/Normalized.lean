-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs

noncomputable section
namespace Turan

/-- The real normalization of the physicists' Hermite polynomial used in the tail estimates. -/
def psi (j : ℕ) (z : ℂ) : ℂ :=
  (hermite j).eval z / (Real.sqrt (2 ^ j * (j.factorial : ℝ)) : ℂ)

end Turan
