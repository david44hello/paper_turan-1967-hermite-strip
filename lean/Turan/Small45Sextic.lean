-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Mathlib.Tactic

namespace Turan.Small45

/-- Completing the square with the denominators cleared. -/
private theorem quad (a b c x : ℝ) (ha : 0 < a) (hd : b^2 < 4*a*c) :
    0 < a*x^2 + b*x + c := by
  apply pos_of_mul_pos_right (a := 4*a) _ (by positivity)
  nlinarith only [sq_nonneg (2*a*x+b), hd]

/-- The squared-distance inequality on the boundary and throughout both exterior
half-planes. After setting t = 10000 y² - 7225, all four coefficients in t are
positive. The sextic and quartic coefficients are sums of positive quadratics
with nonnegative multipliers. -/
theorem model_sextic (x y : ℝ) (hy : 17/20 ≤ |y|) :
    ((x+20.10)^2+y^2)^2*((x-0.44)^2+y^2) <
      225^2*(x^2+y^2)^2*((x-2.47)^2+y^2) := by
  let t := 10000*y^2-7225
  have ht : 0 ≤ t := by
    dsimp [t]
    rcases le_abs.mp hy with h | h <;> nlinarith only [h, sq_nonneg (y-17/20), sq_nonneg (y+17/20)]
  let q (a b c : ℝ) := a*x^2+b*x+c
  have hq (a b c : ℝ) (ha : 0 < a) (hd : b^2 < 4*a*c) : 0 < q a b c :=
    quad a b c x ha hd
  let p₀ := x^4*q 50624000000000000 (-250167020000000000) 311000000000000000
    + x^2*q 105232080900000000 (-391856140540000000) 370000000000000000
    + q 18184831684500000 (-16206194714675000) 30254161131225625
  let p₁ := x^2*q 15187200000000 (-50033404000000) 45000000000000
    + q 38400944980000 (-39327825574000) 36102965208850
  let p₂ := q 1518720000 (-2501670200) 4177773689
  have h₀ : 0 < p₀ := by
    dsimp only [p₀]
    apply add_pos_of_nonneg_of_pos
    · apply add_nonneg <;> apply mul_nonneg (by positivity) <;> apply le_of_lt <;> apply hq <;> norm_num
    · apply hq <;> norm_num
  have h₁ : 0 < p₁ := by
    dsimp only [p₁]
    apply add_pos_of_nonneg_of_pos
    · exact mul_nonneg (sq_nonneg _) (hq _ _ _ (by norm_num) (by norm_num)).le
    · exact hq _ _ _ (by norm_num) (by norm_num)
  have h₂ : 0 < p₂ := hq _ _ _ (by norm_num) (by norm_num)
  have hid : 10000^3 * (225^2*(x^2+y^2)^2*((x-2.47)^2+y^2) -
      ((x+20.10)^2+y^2)^2*((x-0.44)^2+y^2)) =
      p₀ + t*(p₁+t*(p₂+t*50624)) := by
    dsimp [t,p₀,p₁,p₂,q]
    ring
  have hp : 0 < p₀ + t*(p₁+t*(p₂+t*50624)) := by positivity
  linarith only [hid, hp]

end Turan.Small45
