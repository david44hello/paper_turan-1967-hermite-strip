module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Normalized

@[expose] public section

open scoped Turan.NumeralFacts

noncomputable section
namespace Turan

def phi (j : ℕ) (z : ℂ) : ℂ := Complex.exp (-z^2/2) * psi j z

def circleQ (j : ℕ) (ξ ρ : ℝ) : ℝ :=
  ρ^2 * (|2 * (j : ℝ) + 1 - ξ^2| + 2 * |ξ| * ρ + ρ^2)

end Turan
