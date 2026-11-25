-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.TailDefs
import Turan.TrinomialDefs
import Turan.Oscillator
namespace Turan

theorem large_mode_circle (m : ℕ) (hm : 450 ≤ m) :
    ∃ x : ℝ, Real.sqrt (9*(m:ℝ)/5) ≤ x ∧
      x ≤ Real.sqrt (9*(m:ℝ)/5) + 3*Real.pi/Real.sqrt m ∧ psi m x = 0 ∧
      ∀ z : ℂ, ‖z - (x:ℂ)‖ = 1/Real.sqrt m → 1/(5*Real.sqrt m) < ‖phi m z‖ := by sorry

theorem large_mode_small_coefficient (n m : ℕ) (hm : 450 ≤ m) (hn : 2 ≤ n)
    (hhalf : 2*n ≤ m) (a b : ℂ) (hs : emptyStrip (normalizedFamily n m a b) (87/100)) :
    ‖b‖ ≤ 20*Real.sqrt m*Real.exp (-(197/1000)*(m:ℝ))*(1+‖a‖) := by sorry

theorem large_lower_index_gap (check : TrinomialDiskCheck) (n m : ℕ) (hm : 450 ≤ m)
    (hn : 2 ≤ n) (hhalf : 2*n ≤ m) (a b : ℂ) :
    ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| < 87/100 := by sorry

theorem lemma_eight_given (check : TrinomialDiskCheck) (n m : ℕ) (hn : 2 ≤ n)
    (hm : 450 ≤ m) (hnm : n < m) (a b : ℂ) :
    ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| < 87/100 := by sorry

end Turan
