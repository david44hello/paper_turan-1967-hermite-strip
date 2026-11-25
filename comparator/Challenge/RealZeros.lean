-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Oscillator
open Polynomial
namespace Turan

theorem hermite_real_simple (j : ℕ) (z : ℂ) (hz : (hermite j).eval z = 0) :
    z.im = 0 ∧ (hermite j).derivative.eval z ≠ 0 := by sorry

theorem real_rooted_circle (p : Polynomial ℂ) (hreal : ∀ w : ℂ, p.eval w = 0 → w.im = 0)
    (x r : ℝ) (hr : 0 < r) (z : ℂ) (hz : ‖z - (x : ℂ)‖ = r) :
    min ‖p.eval ((x-r : ℝ):ℂ)‖ ‖p.eval ((x+r : ℝ):ℂ)‖ ≤ ‖p.eval z‖ := by sorry

theorem real_rooted_weighted_circle (p : Polynomial ℂ) (hreal : ∀ w : ℂ, p.eval w = 0 → w.im = 0)
    (x r : ℝ) (hr : 0 < r) (z : ℂ) (hz : ‖z - (x : ℂ)‖ = r) :
    let f := fun w : ℂ => Complex.exp (-w^2/2) * p.eval w
    min ‖f ((x-r : ℝ):ℂ)‖ ‖f ((x+r : ℝ):ℂ)‖ ≤ ‖f z‖ := by sorry

end Turan
