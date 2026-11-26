module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Small34Angles

@[expose] public section

noncomputable section
namespace Turan

/-- Outer, inner, outer boxes for the coefficients 5, −4, 2. -/
def small34GUpper (z : ℂ) : ℝ :=
  5 * small34Angle (-1.311446) (-0.096251) z - 4 * small34Angle (-1.553002) 1.794300 z
    + 2 * small34Angle (-0.308319) 2.074718 z

/-- Inner, outer, inner boxes for the coefficients 5, −4, 2. -/
def small34GLower (z : ℂ) : ℝ :=
  5 * small34Angle (-1.311445) (-0.096252) z - 4 * small34Angle (-1.553003) 1.794301 z
    + 2 * small34Angle (-0.308318) 2.074717 z

end Turan
