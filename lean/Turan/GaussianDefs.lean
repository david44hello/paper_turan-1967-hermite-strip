module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

@[expose] public section

noncomputable section
namespace Turan

def gaussianMoment (A : ℝ) (B : ℂ) (p : Polynomial ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-(A : ℂ) * (t : ℂ)^2 + B*t) * p.eval (t : ℂ)

end Turan
