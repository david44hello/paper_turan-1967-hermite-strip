module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.QuarticPencilAlgebra
public import Turan.QuarticRoot

@[expose] public section

noncomputable section
namespace Turan

open QuarticPencil in
theorem lemma_eighteen (w : ℂ) (hw : 0 < w.im ∧ 12*w^4+16*w^3+12*w^2-3=0)
    (d : ℝ) (hd : d ≠ 0) (z : ℂ) (hz : w.im ≤ z.im) :
    (2*z+(d:ℂ))^2*(4*z^2+4*z+2) - (4*z^4-4*z^2+3) ≠ 0 := by
  intro hroot
  have h₀ := height_equation 0 w hw.1.ne' (by
    push_cast
    linear_combination hw.2)
  simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero] at h₀
  have h₁ := height_equation d z (hw.1.trans_le hz).ne' hroot
  have hlo := (quartic_root_height w hw).1
  have hs : 0 ≤ 3*w.im^2-2 := by
    nlinarith only [(sq_lt_sq₀ (by norm_num : (0:ℝ) ≤ 8286/10000) hw.1.le).2 hlo]
  have hst : 3*w.im^2-2 ≤ 3*z.im^2-2 := by
    linarith only [(sq_le_sq₀ hw.1.le (hw.1.trans_le hz).le).2 hz]
  have hb := base_mono hs hst
  have hp := mul_pos (sq_pos_of_ne_zero hd) (correction_pos (hs.trans hst) d)
  linarith only [h₀, h₁, hb, hp]

#print axioms lemma_eighteen

end Turan
