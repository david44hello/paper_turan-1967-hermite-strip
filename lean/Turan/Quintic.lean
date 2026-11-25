-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.CubicRoots
import Turan.QuinticNodes
import Turan.QuinticOrder
import Turan.QuinticFactors
import Turan.QuinticTop
import Turan.QuinticRectangle

noncomputable section
namespace Turan

theorem lemma_twenty_three_strip (a b : ℂ) (hb : b ≠ 0) :
    ∃ z : ℂ, (family 2 5 a b).eval z = 0 ∧ |z.im| < 87/100 := by
  by_contra! hno
  obtain ⟨S,hS,_⟩ := quintic_node_exists
  let X := (S-1)/2
  let s := Real.sqrt (1+S^2)/2
  obtain ⟨_,_,_,hX,hs₀,hs₁,hl,hr,heq⟩ := lemma_twenty_three_nodes S hS
  obtain ⟨z,hh,hz,hz2,ha⟩ := quintic_root_data a b hb X s hs₀ hs₁ hl hr heq hno
  obtain ⟨w,hhw,hzw,hzw2,hsort,hsum⟩ := quintic_order_angles X s z hh hz hz2 ha
  have htop := quintic_top_three X s w hX hs₀ hs₁ hhw hzw hzw2 hsort hsum
  exact quintic_angle_contradiction X s w hX hs₀ hs₁ hhw hzw hzw2 hsort hsum htop

theorem quintic_all_coefficients (a b : ℂ) :
    ∃ z : ℂ, (family 2 5 a b).eval z = 0 ∧ |z.im| < 87/100 := by
  by_cases hb : b = 0
  · subst b
    obtain ⟨z,hz,hh⟩ := cubic_zero_b_half_strip a
    exact ⟨z, by simpa [family] using hz, by linarith⟩
  · exact lemma_twenty_three_strip a b hb

end Turan
