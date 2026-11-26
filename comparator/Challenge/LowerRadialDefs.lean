module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TailDefs
public import Turan.Oscillator

@[expose] public section

noncomputable section
namespace Turan.LowerTailSteps

def radialMode (j : ℕ) (ξ ρ : ℝ) (v : ℂ) : ℂ := phi j ((ξ : ℂ) + ρ*v)

def radialSlope (j : ℕ) (ξ ρ : ℝ) : ℂ := (ρ : ℂ) * deriv (phi j) (ξ : ℂ)

def radialPotential (j : ℕ) (ξ ρ : ℝ) (v : ℂ) : ℂ :=
  (ρ : ℂ)^2 * (2*(j:ℂ)+1-((ξ:ℂ)+ρ*v)^2)

end Turan.LowerTailSteps
