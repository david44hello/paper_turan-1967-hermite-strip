-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.TailDefs

noncomputable section
namespace Turan.LowerTailSteps

def logTail (M : ℝ) : ℝ :=
  Real.log 2200000 + 5 * Real.log M + 8 + (76/100 : ℝ) * Real.sqrt (2*M) - (197/1000 : ℝ) * M

def factorDistanceSq (x r s t : ℝ) : ℝ := (x-s)^2 + r^2 + 2*(x-s)*r*t

def gaussianLog (x r t : ℝ) : ℝ := -(x^2 + 2*x*r*t + r^2*(2*t^2-1))/2

end Turan.LowerTailSteps
