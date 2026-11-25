-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs

noncomputable section
open scoped ComplexConjugate
namespace Turan

theorem constants_spec :
    32 * u ^ 3 + 6 * u = 1 ∧ 0 < u ∧ u < 1/6 ∧
    (∀ r : ℝ, 32 * r ^ 3 + 6 * r = 1 → r = u) ∧
    h ^ 2 = 3/4 + 3 * u ^ 2 ∧ 1/2 < h := by sorry

theorem lemma_four :
    (∀ w : ℂ, 4 * w ^ 3 + 3 * w + 1 = 0 ↔
      w = -2 * (u : ℂ) ∨ w = W ∨ w = conj W) ∧
    0 < u ∧ u < 1/6 ∧ ‖W‖ ^ 2 = 1/(8*u) ∧
    h = Real.sqrt 3 / 2 * Real.cosh (Real.log (1 + Real.sqrt 2) / 3) := by sorry

theorem lemma_six (x y v : ℂ) (hr : rootRelation x y v) (hx : h ≤ x.im) (hy : h ≤ y.im) :
    v ≠ 0 ∧ ∃ w : ℂ,
      (w - (-1 / (4*v))) ^ 2 = (x - (-1 / (4*v))) * (y - (-1 / (4*v))) ∧
      h ≤ w.im ∧ rootRelation w w v ∧
      ((-1 / (4*v)).im < h → w.im = h → x = w ∧ y = w) := by sorry

theorem lemma_seven :
    (∀ w : ℂ, h ≤ w.im → AnalyticAt ℂ third w ∧ |(third w).im| ≤ h ∧
      (|(third w).im| = h ↔ w = W)) ∧ third W = W := by sorry

theorem proposition_five (x y v : ℂ) (hr : rootRelation x y v)
    (hx : h ≤ |x.im|) (hy : h ≤ |y.im|) (hv : h ≤ |v.im|) :
    (x = W ∧ y = W ∧ v = W) ∨ (x = conj W ∧ y = conj W ∧ v = conj W) := by sorry

theorem cubic_closed_strip (a b : ℂ) :
    ∃ z : ℂ, (family 2 3 a b).eval z = 0 ∧ |z.im| ≤ h := by sorry

theorem extremal_cubics :
    let p := family 2 3 extremalA extremalB
    let q := family 2 3 (conj extremalA) (conj extremalB)
    p ≠ q ∧ extremalB ≠ 0 ∧
    (∀ z : ℂ, p.eval z = 8 * extremalB * (z + 1/2 - W)^3 ∧
      q.eval z = 8 * conj extremalB * (z + 1/2 - conj W)^3) ∧
    (∀ z : ℂ, (p.eval z = 0 ↔ z = W - 1/2) ∧
              (q.eval z = 0 ↔ z = conj W - 1/2)) ∧
    |(W - 1/2).im| = h ∧ |(conj W - 1/2).im| = h := by sorry

theorem cubic_sharp (t : ℝ) (ht : t < h) :
    ∃ a b : ℂ, ∀ z : ℂ, (family 2 3 a b).eval z = 0 → t < |z.im| := by sorry

theorem cubic_open_strip (a b : ℂ) :
    (∀ z : ℂ, (family 2 3 a b).eval z = 0 → h ≤ |z.im|) ↔
      (a = extremalA ∧ b = extremalB) ∨ (a = conj extremalA ∧ b = conj extremalB) := by sorry

end Turan
