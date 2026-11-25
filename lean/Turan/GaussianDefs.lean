-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

noncomputable section
namespace Turan

def gaussianMoment (A : ℝ) (B : ℂ) (p : Polynomial ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-(A : ℂ) * (t : ℂ)^2 + B*t) * p.eval (t : ℂ)

end Turan
