-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

noncomputable section
open scoped ComplexConjugate
namespace Turan

/-- Signed angle subtended by the interval with midpoint X and half-length s,
for points where the denominator is positive. -/
def qAngle (X s : ℝ) (z : ℂ) : ℝ :=
  Real.arctan (2*s*z.im / ((z.re-X)^2 + z.im^2 - s^2))

theorem qAngle_conj (X s : ℝ) (w : ℂ) : qAngle X s (conj w) = -qAngle X s w := by
  simp [qAngle, mul_neg, neg_div, Real.arctan_neg]

theorem qAngle_abs_lt (X s : ℝ) (w : ℂ) (hs₀ : 1/2 < s) (hs₁ : s < 511/1000)
    (hh : 87/100 ≤ |w.im|) : |qAngle X s w| < Real.arctan (9/5) := by
  let D := (w.re-X)^2+w.im^2-s^2
  have hs2 : s^2 < (511/1000:ℝ)^2 := by
    nlinarith [mul_pos (sub_pos.mpr hs₁) (show 0 < 511/1000+s by linarith)]
  have hy2 : (87/100:ℝ)^2 ≤ w.im^2 := by
    have := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 87/100) hh
    nlinarith [sq_abs w.im]
  have hD : 0 < D := by dsimp [D]; nlinarith [sq_nonneg (w.re-X)]
  have hkey : 2*s*|w.im| < 9/5 * D := by
    dsimp [D]
    nlinarith [sq_nonneg (|w.im|-87/100), sq_abs w.im, sq_nonneg (w.re-X),
      mul_nonneg (le_of_lt (sub_pos.mpr hs₁)) (abs_nonneg w.im)]
  have hm : |2*s*w.im/D| < 9/5 := by
    rw [abs_div, abs_of_pos hD, abs_mul, abs_of_pos (by linarith : 0 < 2*s)]
    exact (div_lt_iff₀ hD).mpr hkey
  change |Real.arctan (2*s*w.im/D)| < _
  apply abs_lt.mpr
  constructor
  · rw [← Real.arctan_neg]; exact Real.arctan_strictMono (abs_lt.mp hm).1
  · exact Real.arctan_strictMono (abs_lt.mp hm).2

end Turan
