module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs

@[expose] public section
noncomputable section
namespace Turan

def quarticDen (z : ℂ) : ℂ := 4*z^2+4*z+2
def quarticRatio (z : ℂ) : ℂ := (4*z^4-4*z^2+3)/quarticDen z
def quarticDelta (H s : ℝ) : ℝ :=
  let z : ℂ := ⟨s-1/2,H⟩
  let v := H^2
  ‖quarticDen z‖^4/(4*v) * (16*v*((quarticRatio z).re+4*v)-(quarticRatio z).im^2)

end Turan
