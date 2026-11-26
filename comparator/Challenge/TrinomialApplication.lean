module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Challenge.TrinomialAE

@[expose] public section

noncomputable section
open Metric Set
namespace Turan.TrinomialAE

/-- The phase integration in A.1 (E) at the actual consecutive Hermite zeros. -/
theorem pencil_integrated_obstruction (n : ℕ) (hn : 80 ≤ n) (a : ℂ) (ha : a.im ≠ 0)
    (hfree : ∀ z ∈ ball (w₀:ℂ) outerRadius, (G n a).eval z ≠ 0) :
    ∃ (s₁ s₂ : ℝ) (θ : ℝ → ℝ),
      IsGreatest {s : ℝ | s ∈ Icc (w₀-beta n) w₀ ∧ psi n (s:ℂ)=0} s₁ ∧
      IsLeast {s : ℝ | s ∈ Icc w₀ (w₀+beta n) ∧ psi n (s:ℂ)=0} s₂ ∧
      s₁ < w₀ ∧ w₀ < s₂ ∧ s₂-s₁ < beta n ∧ PhaseOn θ (G n a) diameter ∧
      |θ s₂-θ s₁| = Real.pi ∧
      Real.pi ≤ (2*logBound n/Real.pi)*(J (w₀-s₁)+J (s₂-w₀)) ∧
      (2*logBound n/Real.pi)*(J (w₀-s₁)+J (s₂-w₀)) ≤ (2*logBound n/Real.pi)*J (beta n) ∧
      Real.pi^2 ≤ 2*logBound n*J (beta n) := by sorry

end Turan.TrinomialAE
