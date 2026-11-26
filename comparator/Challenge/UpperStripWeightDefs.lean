module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Challenge.UpperSourceDefs

@[expose] public section

noncomputable section
namespace Turan.UpperTailStrip

def stripWeight (m : ℕ) (z : ℂ) : ℂ :=
  (1-4*Complex.I*z/(Real.sqrt (2*(m:ℝ)) : ℂ))^4

def selectedRoots (j : ℕ) := (hermite j).roots.toFinset.filter
  (fun s => s.im = 0 ∧ -(7:ℝ)/2 ≤ s.re ∧ s.re ≤ 5/2)

end Turan.UpperTailStrip
