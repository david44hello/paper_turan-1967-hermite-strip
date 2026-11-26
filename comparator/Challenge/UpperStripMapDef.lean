module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Challenge.UpperSourceDefs

@[expose] public section

noncomputable section
namespace Turan.UpperTailStrip

def stripTanh (s : ℝ) (z : ℂ) : ℂ :=
  Complex.tanh ((Real.pi : ℂ)*(z-(s:ℂ))/(4*(TailStrip.height : ℂ)))

end Turan.UpperTailStrip
