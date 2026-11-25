-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs
import Mathlib.Analysis.Complex.AbsMax

namespace Turan

/-- Existence form of the circle comparison used for the certificates. -/
theorem circle_comparison {F P : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (Metric.closedBall c r))
    (hP : DifferentiableOn ℂ P (Metric.closedBall c r))
    (hzero : ∃ z ∈ Metric.ball c r, P z = 0)
    (hdom : ∀ z ∈ Metric.sphere c r, ‖F z - P z‖ < ‖P z‖) :
    ∃ z ∈ Metric.ball c r, F z = 0 := by sorry

/-- The third elementary fact for the circle certificates. -/
theorem circle_at_neg_half (r : ℝ) (z : ℂ) (hz : ‖z + 1/2‖ = r) :
    ‖1 + 2*z‖ = 2*r := by sorry

/-- A disk with the indicated center and radius lies in the strict strip. -/
theorem disk_in_strip (c z : ℂ) (r t : ℝ) (hr : |c.im| + r < t)
    (hz : z ∈ Metric.closedBall c r) : |z.im| < t := by sorry

/-- The two coefficient components make a nonnegative scalar product. -/
theorem circle_coefficient_bound (a b : ℂ) (d e s t : ℝ)
    (horient : (a * star b).re * d * e ≥ 0) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s^2 + t^2 ≤ 1) :
    s * ‖a * (d : ℂ)‖ + t * ‖b * (e : ℂ)‖ ≤ ‖a*(d : ℂ) + b*(e : ℂ)‖ := by sorry

/-- The decimal in Theorem 1 is a truncation of the exact constant. -/
theorem height_decimal :
    (903669747226 : ℝ)/10^12 < h ∧ h < (903669747227 : ℝ)/10^12 := by sorry

end Turan
