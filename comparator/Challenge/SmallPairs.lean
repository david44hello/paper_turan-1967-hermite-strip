-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs
open scoped ComplexConjugate
namespace Turan

theorem quartic_upper_root :
    ∃! w : ℂ, 0 < w.im ∧ 12*w^4 + 16*w^3 + 12*w^2 - 3 = 0 := by sorry

theorem lemma_eighteen (w : ℂ) (hw : 0 < w.im ∧ 12*w^4+16*w^3+12*w^2-3=0)
    (d : ℝ) (hd : d ≠ 0) (z : ℂ) (hz : w.im ≤ z.im) :
    (2*z+(d:ℂ))^2*(4*z^2+4*z+2) - (4*z^4-4*z^2+3) ≠ 0 := by sorry

theorem lemma_nineteen (w : ℂ) (hw : 0 < w.im ∧ 12*w^4+16*w^3+12*w^2-3=0) :
    let b₀ := (64*w^3)⁻¹
    let a₀ := (12-24*w^2)*b₀
    (8286/10000 < w.im ∧ w.im < 8287/10000 ∧ w.im < Real.sqrt 3/2) ∧
    (∀ a b : ℂ, ∃ z : ℂ, (family 2 4 a b).eval z = 0 ∧ |z.im| ≤ w.im) ∧
    (∀ a b : ℂ, (∀ z : ℂ, (family 2 4 a b).eval z = 0 → w.im ≤ |z.im|) ↔
      (a=a₀ ∧ b=b₀) ∨ (a=conj a₀ ∧ b=conj b₀)) ∧
    family 2 4 a₀ b₀ ≠ family 2 4 (conj a₀) (conj b₀) ∧ b₀ ≠ 0 ∧
    (∀ z : ℂ, (family 2 4 a₀ b₀).eval z = 16*b₀*(z-w)^3*(z+3*w) ∧
      (family 2 4 (conj a₀) (conj b₀)).eval z = 16*conj b₀*(z-conj w)^3*(z+3*conj w)) := by sorry

theorem lemma_twenty (a b : ℂ) : ∃ z : ℂ, (family 3 4 a b).eval z = 0 ∧ |z.im| < 5/7 := by sorry
theorem lemma_twenty_one (a b : ℂ) : ∃ z : ℂ, (family 4 5 a b).eval z = 0 ∧ |z.im| < 17/20 := by sorry
theorem lemma_twenty_two (a b : ℂ) : ∃ z : ℂ, (family 5 6 a b).eval z = 0 ∧ |z.im| < 43/50 := by sorry

end Turan
