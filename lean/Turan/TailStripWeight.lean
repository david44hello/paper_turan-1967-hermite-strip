module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TailDefs
public import Turan.TailStripFactors

@[expose] public section

noncomputable section
namespace Turan.TailStrip
open Complex

/-- The fourth power of this affine function absorbs the growth of the line estimate. -/
def weightBase (m : ℕ) (z : ℂ) : ℂ := (Real.sqrt (2*(m:ℝ)) : ℝ) - 4*I*z

private theorem sqrt_lower {m : ℕ} (hm : 450 ≤ m) : 30 ≤ Real.sqrt (2*(m:ℝ)) := by
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  have : (450 : ℝ) ≤ m := by exact_mod_cast hm
  linarith

private theorem weight_re (m : ℕ) (z : ℂ) :
    (weightBase m z).re = Real.sqrt (2*(m:ℝ)) + 4*z.im := by
  simp [weightBase, Complex.mul_re, Complex.mul_im]

theorem weight_sq (m : ℕ) (z : ℂ) :
    ‖weightBase m z‖^2 = (Real.sqrt (2*(m:ℝ)) + 4*z.im)^2 + 16*z.re^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, weight_re]
  simp [weightBase, Complex.mul_re, Complex.mul_im]; ring

theorem one_le_weight {m : ℕ} (hm : 450 ≤ m) {z : ℂ} (hz : z ∈ strip) :
    1 ≤ ‖weightBase m z‖ := by
  have h := Complex.re_le_norm (weightBase m z)
  rw [weight_re] at h
  have hy := (abs_le.mp (show |z.im| ≤ (7:ℝ)/11 from hz)).1
  linarith [sqrt_lower hm]

private theorem omega_le_weight {m : ℕ} (hm : 450 ≤ m) {z : ℂ} (hz : z ∈ strip) :
    omega m z ≤ (11/10)*‖weightBase m z‖ := by
  have h := sqrt_lower hm
  have hy := (abs_le.mp (show |z.im| ≤ (7:ℝ)/11 from hz)).1
  have h1 : (10/11)*Real.sqrt (2*(m:ℝ)) ≤ Real.sqrt (2*(m:ℝ)) + 4*z.im := by linarith
  have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ (10/11)*Real.sqrt (2*(m:ℝ))) h1 2
  have hd := weight_sq m z
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 2*(m:ℝ))
  unfold omega
  apply (Real.sqrt_le_left (by positivity)).mpr
  nlinarith [sq_nonneg z.re]

theorem weighted_line_bound {n m j : ℕ} (hm : 450 ≤ m) (hden : 0 < (j:ℝ)*(m-n:ℝ))
    {u : ℂ → ℂ} (hline : ∀ z : ℂ, |z.im| = height →
      ‖u z‖ ≤ 4200 * (omega m z)^4 / ((j:ℝ)*(m-n:ℝ))) {z : ℂ}
    (hz : |z.im| = height) :
    ‖u z / weightBase m z ^ 4‖ ≤ (4200*(11/10)^4) / ((j:ℝ)*(m-n:ℝ)) := by
  have hw := one_le_weight hm hz.le
  have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) (omega_le_weight hm hz.le) 4
  rw [mul_pow] at h
  rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
  change (omega m z)^4 ≤ (11/10)^4 * ‖weightBase m z‖^4 at h
  calc
    _ ≤ 4200 * (omega m z)^4 / ((j:ℝ)*(m-n:ℝ)) := hline z hz
    _ ≤ 4200 * ((11/10)^4 * ‖weightBase m z‖^4) / ((j:ℝ)*(m-n:ℝ)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h (by norm_num)) hden.le
    _ = _ := by ring

theorem center_weight {m : ℕ} (hm : 450 ≤ m) :
    (4200*(11/10)^4)*‖weightBase m (-1/2)‖^4 ≤ 25000*(m:ℝ)^2 := by
  have hs := weight_sq m (-1/2)
  have h : ‖weightBase m (-1/2)‖ ^ 2 = 2*(m:ℝ)+4 := by
    rw [hs]
    norm_num [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  have hm' : (450:ℝ) ≤ m := by exact_mod_cast hm
  have h1 : 2*(m:ℝ)+4 ≤ (452/225)*(m:ℝ) := by linarith
  have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ 2*(m:ℝ)+4) h1 2
  rw [show ‖weightBase m (-1/2)‖ ^ 4 = (‖weightBase m (-1/2)‖ ^ 2)^2 by ring, h]
  nlinarith [sq_nonneg (m:ℝ)]

end Turan.TailStrip
