-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.TailDefs
import Turan.Oscillator

noncomputable section
namespace Turan.LowerTailSteps

def realEnergy (m : ℕ) (t : ℝ) : ℝ :=
  ‖psi m (t : ℂ)‖ ^ 2 + ‖deriv (psi m) (t : ℂ)‖ ^ 2 / (2 * (m : ℝ))

end Turan.LowerTailSteps
