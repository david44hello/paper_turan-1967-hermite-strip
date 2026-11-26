module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Oscillator

@[expose] public section
namespace Turan

theorem lemma_nine (n : ℕ) (z : ℂ) :
    ‖psi n z‖ * Real.exp (-z.re^2/2) ≤
      (1 - (1:ℝ)/25) ^ (-(1:ℝ)/4) *
      Real.exp (-z.re^2/3 + z.im^2/4 + ((n:ℝ)/2)*Real.log 5) := by sorry

theorem lemma_thirteen (j : ℕ) (ξ ρ : ℝ) (hρ : 0 < ρ) (v : ℂ) (hv : ‖v‖ ≤ 1) :
    let δ := (ρ : ℂ) * deriv (phi j) (ξ : ℂ)
    let q := Real.sqrt (circleQ j ξ ρ)
    ‖phi j ((ξ : ℂ) + ρ*v) - δ*v‖ ≤ Real.cosh q * ‖phi j (ξ : ℂ)‖ +
      (Real.sinh q / q - 1) * ‖δ‖ := by sorry

end Turan
