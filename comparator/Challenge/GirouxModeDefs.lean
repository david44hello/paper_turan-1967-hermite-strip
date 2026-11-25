-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Normalized
noncomputable section
open Polynomial
namespace Turan.Giroux
def scale (j : ℕ) : ℝ := Real.sqrt (2^j * (j.factorial : ℝ))
def mode (j : ℕ) : Polynomial ℂ := C ((scale j : ℂ)⁻¹) * hermite j
end Turan.Giroux
