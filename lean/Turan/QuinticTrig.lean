module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.QuinticAngle

@[expose] public section

namespace Turan

theorem quintic_rectangle_angle :
    Real.arctan (45/28) = Real.pi - 2*Real.arctan (9/5) := by
  have hd := Real.two_mul_arctan_add_pi (by norm_num : (1:ℝ) < 9/5)
  rw [show (2*(9/5:ℝ)/(1-(9/5:ℝ)^2)) = -(45/28:ℝ) by norm_num, Real.arctan_neg] at hd
  linarith

theorem quintic_triple_angle :
    3*Real.arctan (9/5) - 2*Real.arctan (1/35) < Real.pi := by
  have ht := Real.arctan_add (by norm_num : (9/5:ℝ)*(-(45/28:ℝ)) < 1)
  rw [show ((9/5:ℝ)+-(45/28:ℝ))/(1-(9/5:ℝ)*-(45/28:ℝ)) = 27/545 by norm_num,
    Real.arctan_neg] at ht
  have hd := Real.two_mul_arctan (by norm_num : (-1:ℝ) < 1/35) (by norm_num : (1/35:ℝ)<1)
  rw [show 2*(1/35:ℝ)/(1-(1/35:ℝ)^2)=35/612 by norm_num] at hd
  linarith [quintic_rectangle_angle, Real.arctan_strictMono (show (27/545:ℝ)<35/612 by norm_num)]

end Turan
