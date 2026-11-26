module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TailDefs
public import Mathlib.Tactic

@[expose] public section

noncomputable section
namespace Turan.TailLines

theorem omega_bounds {m : ℕ} (hm : 450 ≤ m) {z : ℂ} (hz : |z.im| = 7/11) :
    900 ≤ (omega m z)^2 ∧ (m:ℝ) ≤ (omega m z)^2/2 ∧ ‖z‖ ≤ 0.272 * omega m z := by
  have hm' : (450:ℝ) ≤ m := by exact_mod_cast hm
  have hsq : (omega m z)^2 = 2*(m:ℝ) + 16*z.re^2 :=
    Real.sq_sqrt (by positivity)
  have hW : 0 ≤ omega m z := Real.sqrt_nonneg _
  have h30 : 30 ≤ omega m z := by nlinarith [sq_nonneg z.re]
  have hx : |z.re| ≤ omega m z / 4 := by
    nlinarith [sq_abs z.re, abs_nonneg z.re]
  refine ⟨by nlinarith [sq_nonneg z.re], by nlinarith [sq_nonneg z.re], ?_⟩
  have h := Complex.norm_le_abs_re_add_abs_im z
  rw [hz] at h
  linarith

/-- Bounds on the two normalized Hermite operator values from the four derivative quotients. -/
theorem jet_bounds {z : ℂ} {W : ℝ} (hW : 0 ≤ W) (hlarge : 900 ≤ W^2)
    (hz : ‖z‖ ≤ 0.272 * W) (d : ℕ → ℂ)
    (hd : ∀ l, 1 ≤ l → l ≤ 4 → ‖d l‖ ≤ (11*W)^l) :
    ‖d 2/2 - z*d 1‖ ≤ 64*W^2 ∧
    ‖d 4/4 - z*d 3 + (z^2-1)*d 2 + z*d 1‖ ≤ 4035*W^4 := by
  have h1 := hd 1 (by decide) (by decide)
  have h2 := hd 2 (by decide) (by decide)
  have h3 := hd 3 (by decide) (by decide)
  have h4 := hd 4 (by decide) (by decide)
  simp only [pow_one] at h1
  have hz2 : ‖z‖^2 ≤ (0.272 * W)^2 := by gcongr
  have hlow : 900*W^2 ≤ W^4 := by
    nlinarith only [mul_nonneg (sq_nonneg W) (sub_nonneg.mpr hlarge)]
  constructor
  · calc
      _ ≤ ‖d 2/2‖ + ‖z*d 1‖ := norm_sub_le _ _
      _ = ‖d 2‖/2 + ‖z‖*‖d 1‖ := by norm_num [norm_div, norm_mul]
      _ ≤ (11*W)^2/2 + (0.272*W)*(11*W) := by gcongr
      _ ≤ _ := by nlinarith only [sq_nonneg W]
  · have hzz : ‖z^2-1‖ ≤ (0.272 * W)^2+1 := by
      calc
        _ ≤ ‖z^2‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ ≤ _ := by rw [norm_pow, norm_one]; linarith
    calc
      _ ≤ ‖d 4/4 - z*d 3 + (z^2-1)*d 2‖ + ‖z*d 1‖ := norm_add_le _ _
      _ ≤ (‖d 4/4 - z*d 3‖ + ‖(z^2-1)*d 2‖) + ‖z*d 1‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ((‖d 4/4‖ + ‖z*d 3‖) + ‖(z^2-1)*d 2‖) + ‖z*d 1‖ := by
        gcongr
        exact norm_sub_le _ _
      _ = ‖d 4‖/4 + ‖z‖*‖d 3‖ + ‖z^2-1‖*‖d 2‖ + ‖z‖*‖d 1‖ := by
        norm_num [norm_div, norm_mul]
      _ ≤ (11*W)^4/4 + (0.272*W)*(11*W)^3 + ((0.272*W)^2+1)*(11*W)^2 +
            (0.272*W)*(11*W) := by gcongr
      _ ≤ _ := by nlinarith only [hlow, sq_nonneg (W^2)]

/-- On either boundary line the affine-mode quotient differs from one by at most 5/j. -/
theorem affine_quotient {j k : ℕ} (hj : 225 ≤ j) (hk : 225 ≤ k)
    {z : ℂ} (hz : |z.im| = 7/11) :
    ∃ q : ℂ, ‖1-q‖ ≤ 5/(j:ℝ) ∧ ‖q‖ ≤ 46/45 ∧
      (1-q)*((k:ℂ)+2*(k-1)*z) + q/(j:ℂ)*(2*(k-1)*z) = 0 := by
  let x : ℝ := -((j:ℝ)*k)/(2*((j:ℝ)-1)*(k-1))
  have hj' : (225:ℝ) ≤ j := by exact_mod_cast hj
  have hk' : (225:ℝ) ≤ k := by exact_mod_cast hk
  have hj1 : 0 < (j:ℝ)-1 := by linarith
  have hk1 : 0 < (k:ℝ)-1 := by linarith
  have hj0 : 0 < (j:ℝ) := by linarith
  have hx : |x| ≤ 450/449 := by
    dsimp [x]
    rw [abs_div, abs_neg, abs_of_nonneg (by positivity), abs_of_pos (by positivity),
      div_le_iff₀ (by positivity)]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hj') (sub_nonneg.mpr hk'), hj', hk']
  have hdist : 7/11 ≤ ‖z-(x:ℂ)‖ := by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero, hz] using
      Complex.abs_im_le_norm (z-(x:ℂ))
  have hdist' : 0 < ‖z-(x:ℂ)‖ := by linarith
  have hratio : ‖z/(z-(x:ℂ))‖ ≤ 2.575 := by
    rw [norm_div, div_le_iff₀ hdist']
    have ht := norm_add_le (z-(x:ℂ)) (x:ℂ)
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] at ht
    linarith
  let t := (z/(z-(x:ℂ)))/((j:ℂ)-1)
  have hjnorm : ‖(j:ℂ)-1‖ = (j:ℝ)-1 := by
    change ‖((j:ℝ):ℂ) - ((1:ℝ):ℂ)‖ = _
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hj1]
  have ht : ‖t‖ ≤ 5/(j:ℝ) := by
    rw [show ‖t‖ = ‖z/(z-(x:ℂ))‖ / ((j:ℝ)-1) by rw [← hjnorm]; exact norm_div _ _]
    calc
      _ ≤ 2.575 / ((j:ℝ)-1) := by gcongr
      _ ≤ _ := by rw [div_le_div_iff₀ hj1 hj0]; linarith
  refine ⟨1+t, ?_, ?_, ?_⟩
  · simpa using ht
  · have h5 : 5/(j:ℝ) ≤ 5/225 := by gcongr
    simpa using (norm_add_le (1:ℂ) t).trans
      (by rw [norm_one]; linarith : ‖(1:ℂ)‖ + ‖t‖ ≤ 46/45)
  · have hxc : 2*((j:ℂ)-1)*(k-1)*(x:ℂ) = -((j:ℂ)*k) := by
      exact_mod_cast (show 2*((j:ℝ)-1)*(k-1)*x = -((j:ℝ)*k) by
        dsimp [x]; field_simp)
    have hjc : (j:ℂ) ≠ 0 := by exact_mod_cast hj0.ne'
    have hjc1 : (j:ℂ)-1 ≠ 0 := by exact_mod_cast hj1.ne'
    have hzc : z-(x:ℂ) ≠ 0 := norm_pos_iff.mp hdist'
    dsimp [t]
    field_simp [hjc, hjc1, hzc]
    linear_combination -z * hxc

end Turan.TailLines
