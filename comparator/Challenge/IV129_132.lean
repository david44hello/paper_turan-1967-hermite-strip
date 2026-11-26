module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.DeltaDefs
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology
namespace Turan

def realContactQuartic (t : ℝ) : ℝ := 12*t^4 + 16*t^3 + 12*t^2 - 3

/-- The derivative argument counts the two real roots independently of the
already verified isolation of the upper complex root. -/
theorem quartic_real_sign_intervals :
    (∀ t : ℝ, HasDerivAt realContactQuartic (24*t*(2*t^2+2*t+1)) t) ∧
    StrictAntiOn realContactQuartic (Iic 0) ∧ StrictMonoOn realContactQuartic (Ici 0) ∧
    (∃! t : ℝ, t < 0 ∧ realContactQuartic t = 0) ∧
    (∃! t : ℝ, 0 < t ∧ realContactQuartic t = 0) := by sorry

theorem quartic_squared_height_vieta_comparison (w : ℂ)
    (hw : 0 < w.im ∧ 12*w^4+16*w^3+12*w^2-3=0) :
    25/27 - 64/225 = (433/675 : ℝ) ∧ (16/25 : ℝ) < 433/675 ∧
    (433/675 : ℝ) < w.im^2 ∧ w.im^2 < 1 - (1/4 : ℝ) := by sorry

/-- Exact pole characterization supplements the already proved exclusion
quartic_den_ne above height one half. -/
theorem quartic_denominator_zeros (z : ℂ) :
    quarticDen z = 0 ↔
      z = -1/2+Complex.I/2 ∨ z = -1/2-Complex.I/2 := by sorry

theorem quartic_ratio_analytic_and_pencil (w z : ℂ)
    (hw : 0<w.im ∧ 12*w^4+16*w^3+12*w^2-3=0) (hz : w.im ≤ z.im) :
    AnalyticAt ℂ quarticRatio z ∧
    ∀ d : ℝ, (2*z+(d:ℂ))^2*quarticDen z-(4*z^4-4*z^2+3)=0 ↔
      quarticRatio z=(2*z+(d:ℂ))^2 := by sorry

/-- The local analytic square root with the specified sign and the derivative
of its imaginary part along the paper’s horizontal parameter. -/
theorem quartic_square_root_branch_at_contact (w : ℂ)
    (hw : 0<w.im ∧ 12*w^4+16*w^3+12*w^2-3=0) :
    ∃ ρ : ℂ → ℂ, AnalyticAt ℂ ρ w ∧ (∀ᶠ z in 𝓝 w, (ρ z)^2 = quarticRatio z) ∧
      ρ w = 2*w ∧ HasDerivAt ρ (-1) w ∧
      HasDerivAt (fun s : ℝ => (ρ (⟨s-1/2,w.im⟩ : ℂ)).im) 0 (w.re+1/2) := by sorry

end Turan
