module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

@[expose] public section

noncomputable section
namespace Turan
open scoped ComplexConjugate

def small34Z (l r x y : ℝ) : ℂ :=
  (((x-r : ℝ) : ℂ) + y*Complex.I) * (((x-l : ℝ) : ℂ) - y*Complex.I)

def small34ZUpper (x y : ℝ) : ℂ :=
  small34Z (-1.311446) (-0.096251) x y ^ 5 *
  conj (small34Z (-1.553002) 1.794300 x y) ^ 4 *
  small34Z (-0.308319) 2.074718 x y ^ 2

def small34ZLower (x y : ℝ) : ℂ :=
  small34Z (-1.311445) (-0.096252) x y ^ 5 *
  conj (small34Z (-1.553003) 1.794301 x y) ^ 4 *
  small34Z (-0.308318) 2.074717 x y ^ 2

open Real
def small34Angle (l r : ℝ) (z : ℂ) : ℝ :=
  arctan ((r-z.re)/z.im) - arctan ((l-z.re)/z.im)

end Turan
