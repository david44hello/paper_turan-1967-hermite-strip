module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.DeltaDifferential
public import Turan.DeltaSign

@[expose] public section

namespace Turan

theorem quartic_delta_contact (w : ℂ) (hw : 0 < w.im ∧ 12*w^4+16*w^3+12*w^2-3=0) :
    let s₀ := w.re+1/2
    quarticDelta w.im s₀=0 ∧ HasDerivAt (quarticDelta w.im) 0 s₀ ∧
      ∀ s : ℝ, s ≠ s₀ → 0 < quarticDelta w.im s := by
  obtain ⟨hzero,hder⟩ := quartic_delta_stationary w hw
  exact ⟨hzero,hder,quartic_delta_positive_off w hw⟩

end Turan
