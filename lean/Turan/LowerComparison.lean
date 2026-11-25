-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Mehler
import Turan.Oscillator
import Turan.Circles
import Turan.TailDefs
import Turan.TailArithmetic
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section
open Metric
namespace Turan

theorem circle_geometry (m x : ℝ) (hm : 450 ≤ m)
    (hlo : Real.sqrt (9*m/5) ≤ x) (hhi : x ≤ Real.sqrt (9*m/5) + 3*Real.pi/Real.sqrt m)
    (z : ℂ) (hz : ‖z-(x:ℂ)‖ = 1/Real.sqrt m) :
    9*m/5-27/10 ≤ z.re^2-z.im^2 ∧ z.im^2 ≤ 1/m ∧ ‖1+2*z‖ ≤ 3*Real.sqrt m := by
  let M := Real.sqrt m
  have hM : 0 < M := Real.sqrt_pos.mpr (by linarith)
  have hM2 : M^2=m := Real.sq_sqrt (by linarith)
  have hM20 : 20 ≤ M := by nlinarith
  let K := Real.sqrt (9/5)
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hK2 : K^2 = 9/5 := Real.sq_sqrt (by norm_num)
  have hK1 : 1 ≤ K := by nlinarith
  have hKlim : K ≤ 27/20 := by nlinarith
  have hrad : Real.sqrt (9*m/5) = K*M := by
    rw [show 9*m/5=(9/5)*m by ring, Real.sqrt_mul (by norm_num)]
  rw [hrad] at hlo hhi
  have hr0 : 0 < 1/M := by positivity
  have hr1 : 1/M ≤ 1 := (div_le_iff₀ hM).mpr (by linarith)
  have hlow : 0 ≤ K*M - 1/M := by nlinarith [mul_le_mul_of_nonneg_right hK1 hM.le]
  have hr := Complex.abs_re_le_norm (z-(x:ℂ))
  have hi := Complex.abs_im_le_norm (z-(x:ℂ))
  rw [hz] at hr hi
  change |z.re-x| ≤ 1/M at hr
  rw [abs_le] at hr
  have hi' : |z.im| ≤ 1/M := by simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using hi
  have hl : K*M - 1/M ≤ z.re := by linarith [hr.1]
  have hxs := (sq_le_sq₀ hlow (hlow.trans hl)).mpr hl
  have hys := (sq_le_sq₀ (abs_nonneg _) hr0.le).mpr hi'
  rw [sq_abs] at hys
  have hid : M*(1/M) = 1 := by field_simp
  have hXY : 9*m/5-27/10 ≤ z.re^2-z.im^2 := by
    nlinarith only [hxs, hys, hKlim, congrArg (fun t : ℝ => K*t) hid,
      congrArg (fun t : ℝ => K^2*t) hM2, congrArg (fun t : ℝ => t*m) hK2]
  have hyb : z.im^2 ≤ 1/m := by simpa [div_pow, hM2] using hys
  have hx0 : 0 ≤ x := (mul_nonneg hK hM.le).trans hlo
  have hnorm : ‖z‖ ≤ 1/M+x := by
    have := norm_add_le (z-(x:ℂ)) (x:ℂ)
    simpa [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0] using this
  have hpi : 3*Real.pi/M ≤ 12/20 := by
    apply (div_le_iff₀ hM).mpr
    linarith [Real.pi_lt_four]
  refine ⟨hXY, hyb, ?_⟩
  have ha := norm_add_le (1:ℂ) (2*z)
  norm_num [norm_mul] at ha
  nlinarith [mul_le_mul_of_nonneg_right hKlim hM.le]

theorem large_mode_comparisons (n m : ℕ) (hm : 450 ≤ m) (hhalf : 2*n ≤ m) (x : ℝ)
    (hlo : Real.sqrt (9*(m:ℝ)/5) ≤ x)
    (hhi : x ≤ Real.sqrt (9*(m:ℝ)/5) + 3*Real.pi/Real.sqrt m)
    (hbound : ∀ z : ℂ, ‖z - (x:ℂ)‖ = 1/Real.sqrt m → 1/(5*Real.sqrt m) < ‖phi m z‖)
    (z : ℂ) (hz : ‖z - (x:ℂ)‖ = 1/Real.sqrt m) :
    ‖psi n z‖ < 20*Real.sqrt m*Real.exp (-(197/1000)*(m:ℝ))*‖psi m z‖ ∧
    ‖1+2*z‖ < 20*Real.sqrt m*Real.exp (-(197/1000)*(m:ℝ))*‖psi m z‖ := by
  have hm' : (450:ℝ) ≤ m := by exact_mod_cast hm
  have hM : 0 < Real.sqrt (m:ℝ) := Real.sqrt_pos.mpr (by linarith)
  obtain ⟨hXY, hY, ha⟩ := circle_geometry m x hm' hlo hhi z hz
  let A := Real.exp ((z.re^2-z.im^2)/2)
  let E := Real.exp (-(197/1000)*(m:ℝ))
  have hE : 0 < E := Real.exp_pos _
  have hphi : ‖phi m z‖ = ‖psi m z‖ / A := by
    have hzRe : (-z^2/2).re = -((z.re^2-z.im^2)/2) := by
      norm_num [Complex.neg_re, Complex.div_ofNat_re, pow_two, Complex.mul_re]
      <;> ring
    rw [phi, norm_mul, Complex.norm_exp, hzRe, Real.exp_neg]
    unfold A
    ring
  have hp := hbound z hz
  rw [hphi, div_lt_div_iff₀ (by positivity) (Real.exp_pos _)] at hp
  have low := lemma_nine n z
  have hlow : ‖psi n z‖ ≤ (1-1/25:ℝ)^(-(1:ℝ)/4) *
      Real.exp (z.re^2/6+z.im^2/4+(n:ℝ)/2*Real.log 5) := by
    have h := mul_le_mul_of_nonneg_right low (Real.exp_pos (z.re^2/2)).le
    convert h using 1 <;> rw [mul_assoc, ← Real.exp_add] <;> ring_nf <;> simp
  have hratio := lower_mode_exponent m n z.re z.im hm' (Nat.cast_nonneg _) (by exact_mod_cast hhalf) hXY hY
  have hlin := affine_mode_exponent m z.re z.im hm' hXY
  simp only [neg_div] at hratio hlin hlow
  have hlast := mul_lt_mul_of_pos_left hp (mul_pos (by norm_num : (0:ℝ)<20) hE)
  dsimp only [E, A] at hlast
  constructor <;> nlinarith only [hlast, hratio, hlow, ha, hlin]

end Turan
