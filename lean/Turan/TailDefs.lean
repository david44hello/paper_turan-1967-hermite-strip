module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Normalized
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

@[expose] public section

noncomputable section
namespace Turan

def normalizedFamily (n m : ℕ) (a b z : ℂ) : ℂ := 1 + 2*z + a*psi n z + b*psi m z

def emptyStrip (f : ℂ → ℂ) (r : ℝ) : Prop := ∀ z : ℂ, |z.im| < r → f z ≠ 0

def omega (m : ℕ) (z : ℂ) : ℝ := Real.sqrt (2*(m : ℝ) + 16*z.re^2)

def modeQuotient (n m j : ℕ) (a b z : ℂ) : ℂ :=
  (if j = n then a else b) * psi j z / normalizedFamily n m a b z

def nodeProduct (j : ℕ) : ℝ :=
  ∏ s ∈ (hermite j).roots.toFinset.filter
      (fun s => s.im = 0 ∧ -(7:ℝ)/2 ≤ s.re ∧ s.re ≤ 5/2),
    |Real.tanh (Real.pi * (-(1:ℝ)/2-s.re)/(4*(7/11)))|

end Turan
