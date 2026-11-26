module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Small56Certificate

@[expose] public section

namespace Turan.Small56.Certificate
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

private theorem leftTest : test (-6000000) (-1) 0 = true := by decide +kernel
private theorem test₁ : test (-6000000) (-3000000) 1 = true := by decide +kernel
private theorem test₂ : test (-3000000) 0 1 = true := by decide +kernel
private theorem test₃ : test 0 1500000 1 = true := by decide +kernel
private theorem test₄ : test 1500000 3000000 1 = true := by decide +kernel
private theorem test₅ : test 3000000 6000000 1 = true := by decide +kernel
private theorem rightTest : test 6000000 1 0 = true := by decide +kernel

private theorem homogeneous (cs : List ℤ) (X V Y : ℝ) :
    product cs (X*V) V Y = (V^2)^cs.length * product cs X 1 Y := by
  induction cs with
  | nil => simp [product]
  | cons c cs ih =>
    simp only [product, List.map_cons, List.prod_cons, List.length_cons, pow_succ] at *
    rw [ih]
    ring

private theorem inside {a b : ℤ} (h : test a b 1 = true) (X t : ℝ) (ht : 0 ≤ t)
    (hl : (a:ℝ) ≤ X) (hu : X < (b:ℝ)) :
    25*product gamma X 1 (860000^2+t) < 81*product delta X 1 (860000^2+t) := by
  let x := (X-a)/(b-X)
  have hx : 0 ≤ x := div_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hu.le)
  have he : (a:ℝ)+b*x = X*(1+x) := by dsimp [x]; field_simp; ring
  have hh := chart h hx ht
  simp only [Int.cast_one, one_mul, he, homogeneous] at hh
  change 25*(((1+x)^2)^12 * _) < 81*(((1+x)^2)^12 * _) at hh
  rw [mul_left_comm (25:ℝ) _ _, mul_left_comm (81:ℝ) _ _] at hh
  exact lt_of_mul_lt_mul_left hh (by positivity)

/-- The cleared degree-24 difference is strictly positive on the boundary and beyond. -/
theorem exterior (X Y : ℝ) (hY : 860000^2 ≤ Y) :
    25*product gamma X 1 Y < 81*product delta X 1 Y := by
  let t := Y-860000^2
  have ht : 0 ≤ t := sub_nonneg.mpr hY
  have hY' : Y=860000^2+t := by dsimp [t]; ring
  rw [hY']
  by_cases h₀ : X < -6000000
  · have h := chart leftTest (x := -6000000-X) (by linarith) ht
    convert h using 1 <;> norm_num
  by_cases h₁ : X < -3000000
  · exact inside test₁ X t ht (by norm_num; linarith) (by exact_mod_cast h₁)
  by_cases h₂ : X < 0
  · exact inside test₂ X t ht (by norm_num; linarith) (by simpa using h₂)
  by_cases h₃ : X < 1500000
  · exact inside test₃ X t ht (by simp; linarith) (by exact_mod_cast h₃)
  by_cases h₄ : X < 3000000
  · exact inside test₄ X t ht (by norm_num; linarith) (by exact_mod_cast h₄)
  by_cases h₅ : X < 6000000
  · exact inside test₅ X t ht (by norm_num; linarith) (by exact_mod_cast h₅)
  have h := chart rightTest (x := X-6000000) (by linarith) ht
  convert h using 1 <;> norm_num

end Turan.Small56.Certificate
