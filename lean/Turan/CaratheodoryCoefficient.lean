-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.CircleAverage

public section

namespace Turan

/-- The circle average extracts the Taylor coefficient of order `l` at the center. -/
theorem caratheodory_coefficient (g : ℂ → ℂ) (z : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) (hg : DifferentiableOn ℂ g (Metric.ball z R)) (l : ℕ) :
    Real.circleAverage (fun w => g w / (w - z) ^ l) z r =
      iteratedDeriv l g z / (l.factorial : ℂ) := by
  have hclosed := hg.mono (Metric.closedBall_subset_ball hrR)
  have hkernel : (fun w => (w - z)⁻¹ • (g w / (w - z) ^ l)) =
      (fun w => (1 / (w - z) ^ (l + 1)) • g w) := by
    funext w
    simp only [smul_eq_mul, div_eq_mul_inv, pow_succ, mul_inv_rev, one_mul]
    ring
  rw [Real.circleAverage_eq_circleIntegral hr.ne', hkernel,
    hclosed.circleIntegral_one_div_sub_center_pow_smul hr l, ← mul_smul,
    div_eq_mul_inv, inv_mul_cancel_left₀ Complex.two_pi_I_ne_zero, smul_eq_mul,
    div_eq_mul_inv, mul_comm]

end Turan
