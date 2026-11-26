module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs

@[expose] public section
namespace Turan

theorem quintic_node_exists :
    ∃! S : ℝ, 0 < S ∧ S < 1/4 ∧ 2*S^3 - 5*S^2 - 4*S + 1 = 0 := by sorry

theorem lemma_twenty_three_nodes (S : ℝ) (hS : 0 < S ∧ S < 1/4 ∧ 2*S^3 - 5*S^2 - 4*S + 1 = 0) :
    let X := (S-1)/2
    let s := Real.sqrt (1+S^2)/2
    let left := X-s
    let right := X+s
    S < 21/100 ∧ -1/2 < X ∧ X < 0 ∧ |X| < 1/2 ∧
    1/2 < s ∧ s < 511/1000 ∧ left + 1/2 < 0 ∧ 0 < right + 1/2 ∧
    ∀ j ∈ ({2,5} : Finset ℕ),
      (hermite j).eval (left:ℂ) / (2*(left:ℂ)+1) =
      (hermite j).eval (right:ℂ) / (2*(right:ℂ)+1) := by sorry

theorem lemma_twenty_three_strip (a b : ℂ) (hb : b ≠ 0) :
    ∃ z : ℂ, (family 2 5 a b).eval z = 0 ∧ |z.im| < 87/100 := by sorry

theorem quintic_all_coefficients (a b : ℂ) :
    ∃ z : ℂ, (family 2 5 a b).eval z = 0 ∧ |z.im| < 87/100 := by sorry

end Turan
