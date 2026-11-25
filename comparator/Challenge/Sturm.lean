-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Oscillator
namespace Turan

theorem sturm_interval {y v Q : ℝ → ℝ} {a k : ℝ} (hk : 0 < k)
    (hy : ∀ t ∈ Set.Icc a (a+Real.pi/k), HasDerivAt y (v t) t)
    (hv : ∀ t ∈ Set.Icc a (a+Real.pi/k), HasDerivAt v (-Q t*y t) t)
    (hQ : ∀ t ∈ Set.Ioo a (a+Real.pi/k), k^2 < Q t) :
    ∃ t ∈ Set.Ioo a (a+Real.pi/k), y t = 0 := by sorry

theorem sturm_closed_interval {y v Q : ℝ → ℝ} {a k : ℝ} (hk : 0 < k)
    (hy : ∀ t ∈ Set.Icc a (a+Real.pi/k), HasDerivAt y (v t) t)
    (hv : ∀ t ∈ Set.Icc a (a+Real.pi/k), HasDerivAt v (-Q t*y t) t)
    (hQ : ∀ t ∈ Set.Ioo a (a+Real.pi/k), k^2 ≤ Q t) :
    (∃ t ∈ Set.Ioo a (a+Real.pi/k), y t = 0) ∨
      (y a = 0 ∧ y (a+Real.pi/k) = 0) := by sorry

theorem hermite_sturm_interval (j : ℕ) (a k : ℝ) (hk : 0 < k)
    (hQ : ∀ t ∈ Set.Ioo a (a+Real.pi/k), k^2 < 2*(j:ℝ)+1-t^2) :
    ∃ t ∈ Set.Ioo a (a+Real.pi/k), psi j (t:ℂ) = 0 := by sorry

end Turan
