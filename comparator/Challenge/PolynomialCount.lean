-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section
open Polynomial Metric
open scoped ComplexConjugate
namespace Turan

theorem polynomial_argument_principle (p : Polynomial ℂ) (c : ℂ) (r : ℝ)
    (hr : 0 < r) (hb : ∀ z ∈ sphere c r, p.eval z ≠ 0) :
    (∮ z in C(c, r), p.derivative.eval z / p.eval z) =
      2 * Real.pi * Complex.I * ((p.roots.filter (fun z => dist z c < r)).card : ℂ) := by sorry

theorem polynomial_rouche (p q : Polynomial ℂ) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hd : ∀ z ∈ sphere c r, ‖q.eval z - p.eval z‖ < ‖p.eval z‖) :
    (q.roots.filter (fun z => dist z c < r)).card =
      (p.roots.filter (fun z => dist z c < r)).card := by sorry

theorem dominant_polynomial_term (p : Polynomial ℂ) (l : ℕ) (hl : 1 ≤ l)
    (hd : (∑ k ∈ p.support.erase l, ‖p.coeff k‖) < ‖p.coeff l‖) :
    (p.roots.filter (fun z => ‖z‖ < 1)).card = l := by sorry

end Turan
