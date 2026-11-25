-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.TailDefs
import Turan.RouteDefs
import Turan.TailGrowthSystem
import Turan.TailStripFactors
noncomputable section
namespace Turan.TailStrip
open Complex
def weightBase (m : ℕ) (z : ℂ) : ℂ := (Real.sqrt (2*(m:ℝ)) : ℝ) - 4*I*z
end Turan.TailStrip
