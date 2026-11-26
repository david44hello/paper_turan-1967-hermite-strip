module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TailDefs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Tactic

@[expose] public section
noncomputable section
open Set
namespace Turan.StripDetails

abbrev height : ℝ := 7/11
def weight (m : ℕ) (z : ℂ) : ℂ := (1-4*Complex.I*z/(Real.sqrt (2*(m:ℝ)):ℂ))^4
def coordinate (s : ℝ) (z : ℂ) : ℂ := (Real.pi:ℂ)*(z-s)/(4*(height:ℂ))
def factor (s : ℝ) (z : ℂ) : ℂ := Complex.tanh (coordinate s z)

end Turan.StripDetails
