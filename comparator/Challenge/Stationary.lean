module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.DeltaDefs

@[expose] public section
namespace Turan

theorem quartic_ratio_contact (w : ℂ) (hw : 0 < w.im ∧ 12*w^4+16*w^3+12*w^2-3=0) :
    quarticRatio w=4*w^2 ∧ HasDerivAt quarticRatio (-4*w) w := by sorry

theorem quartic_delta_contact (w : ℂ) (hw : 0 < w.im ∧ 12*w^4+16*w^3+12*w^2-3=0) :
    let s₀ := w.re+1/2
    quarticDelta w.im s₀=0 ∧ HasDerivAt (quarticDelta w.im) 0 s₀ ∧
      ∀ s : ℝ, s ≠ s₀ → 0 < quarticDelta w.im s := by sorry

theorem quartic_delta_criterion (w : ℂ) (hw : 0 < w.im ∧ 12*w^4+16*w^3+12*w^2-3=0)
    (s : ℝ) (ρ : ℂ) (hρ : ρ^2=quarticRatio ⟨s-1/2,w.im⟩) :
    quarticDelta w.im s = 0 ↔ (ρ.im=2*w.im ∨ ρ.im= -2*w.im) := by sorry

end Turan
