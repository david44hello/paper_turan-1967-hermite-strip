-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Normalized

noncomputable section
open scoped ComplexConjugate
namespace Turan.MehlerJets

def diagonalExponent (z : ℂ) (r : ℝ) : ℂ :=
  (2*z*conj z*(r:ℂ) - (z^2+(conj z)^2)*(r:ℂ)^2) / (1-(r:ℂ)^2)

end Turan.MehlerJets
