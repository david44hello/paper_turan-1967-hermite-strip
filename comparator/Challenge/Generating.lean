-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Normalized
import Mathlib.Topology.UniformSpace.UniformConvergence
open Filter
namespace Turan

theorem hermite_generating (z t : ℂ) :
    HasSum (fun k : ℕ => (hermite k).eval z * t^k / (k.factorial:ℂ))
      (Complex.exp (2*z*t-t^2)) := by sorry

theorem normalized_cauchy_bound (k : ℕ) (hk : 1 ≤ k) (z : ℂ) :
    ‖psi k z‖ ≤ (Real.exp 1 / Real.sqrt 2)^k * Real.exp (2*‖z‖*Real.sqrt k) := by sorry

theorem mehler_term_majorant (k : ℕ) (z w : ℂ) :
    ‖((1:ℂ)/5)^k * psi k z * psi k w‖ ≤
      (Real.exp 1 ^ 2/10)^k * Real.exp (2*Real.sqrt k*(‖z‖+‖w‖)) := by sorry

theorem mehler_growth_ratio : Real.exp 1 ^ 2 / 10 < (74:ℝ)/100 := by sorry

theorem mehler_kernel (r : ℝ) (hr : 0 ≤ r) (hr' : r < 1) (z w : ℂ) :
    HasSum (fun k : ℕ => (r:ℂ)^k * psi k z * psi k w)
      ((Real.sqrt (1-r^2):ℂ)⁻¹ * Complex.exp
        ((2*z*w*r-(z^2+w^2)*r^2)/(1-(r:ℂ)^2))) := by sorry

theorem mehler_uniform_on_balls (R : ℝ) :
    TendstoUniformlyOn
      (fun N (p : ℂ × ℂ) => ∑ k ∈ Finset.range N, ((1:ℂ)/5)^k*psi k p.1*psi k p.2)
      (fun p => (Real.sqrt (1-(1/5:ℝ)^2):ℂ)⁻¹ * Complex.exp
        ((2*p.1*p.2/5-(p.1^2+p.2^2)/25)/(1-(1/5:ℂ)^2)))
      atTop (Metric.closedBall 0 R) := by sorry

end Turan
