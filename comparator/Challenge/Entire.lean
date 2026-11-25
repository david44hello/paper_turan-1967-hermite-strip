-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs
import Mathlib.Analysis.Analytic.Order
namespace Turan

theorem dominant_entire_term (f : ℂ → ℂ) (a : ℕ → ℂ) (l : ℕ) (hl : 1 ≤ l)
    (hf : Differentiable ℂ f) (ha : ∀ z : ℂ, HasSum (fun k => a k*z^k) (f z))
    (s : ℝ) (hs : HasSum (fun k => if k=l then 0 else ‖a k‖) s) (hd : s < ‖a l‖) :
    ∃ roots : Multiset ℂ, roots.card = l ∧ ∀ z : ℂ,
      (roots.count z : ℕ∞) = if ‖z‖ < 1 then analyticOrderAt f z else 0 := by sorry

end Turan
