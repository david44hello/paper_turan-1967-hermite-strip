module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.GaussianParts
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

noncomputable section
open MeasureTheory Polynomial
namespace Turan

/-- Squared modulus of the complex Gaussian integral with constant polynomial. -/
theorem gaussianMoment_one_norm_sq (A : ℝ) (hA : 0 < A) (B : ℂ) :
    ‖gaussianMoment A B 1‖ ^ 2 =
      (Real.pi / A) * Real.exp ((B ^ 2).re / (2 * A)) := by
  have hquad := integral_cexp_quadratic (b := -(A : ℂ)) (by simpa using hA) B 0
  simp only [add_zero, neg_neg, zero_sub, mul_neg, div_neg] at hquad
  simp only [gaussianMoment, eval_one, mul_one, hquad, norm_mul, mul_pow, Complex.norm_exp]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_real,
    ← Real.sqrt_eq_rpow, Real.sq_sqrt (norm_nonneg _), ← Complex.ofReal_div,
    Complex.norm_real, Real.norm_of_nonneg (by positivity), ← Complex.ofReal_ofNat (n := 4),
    ← Complex.ofReal_mul, Complex.div_ofReal_re, sq, ← Real.exp_add]
  congr 2
  ring

private theorem norm_integral_mul_sq_le (F G : ℝ → ℂ)
    (hF : MemLp F 2 volume) (hG : MemLp G 2 volume) :
    ‖∫ t, F t * G t‖ ^ 2 ≤ (∫ t, ‖F t‖ ^ 2) * (∫ t, ‖G t‖ ^ 2) := by
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hF : MemLp F (ENNReal.ofReal 2) volume)
    (by simpa using hG : MemLp G (ENNReal.ofReal 2) volume)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at h
  have hnorm := norm_integral_le_integral_norm (μ := volume) (fun t => F t * G t)
  simp only [norm_mul] at hnorm
  calc
    _ ≤ (Real.sqrt (∫ t, ‖F t‖ ^ 2) * Real.sqrt (∫ t, ‖G t‖ ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hnorm.trans h) 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]

/-- Cauchy–Schwarz bound for a polynomial real on the real axis. -/
theorem gaussianMoment_cauchy (B : ℂ) (p : Polynomial ℂ)
    (hreal : ∀ t : ℝ, (p.eval (t : ℂ)).im = 0) :
    ‖gaussianMoment (5 / 4) B p‖ ^ 2 ≤
      (Real.sqrt (2 * Real.pi / 3) * Real.exp ((2 / 3) * B.re ^ 2)) *
        (gaussianMoment 1 0 (p ^ 2)).re := by
  let F (t : ℝ) := Complex.exp (((-(3 / 4) * t ^ 2 : ℝ) : ℂ) + B * t)
  let G (t : ℝ) := Complex.exp (((-(1 / 2) * t ^ 2 : ℝ) : ℂ)) * p.eval (t : ℂ)
  have hFG : gaussianMoment (5 / 4) B p = ∫ t, F t * G t := by
    apply integral_congr_ae
    filter_upwards with t
    dsimp only [F, G]
    rw [← mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  -- Complete the square and translate the real Gaussian.
  have hFsq (t : ℝ) : ‖F t‖ ^ 2 =
      Real.exp (-(3 / 2) * (t + -(2 / 3) * B.re) ^ 2) * Real.exp ((2 / 3) * B.re ^ 2) := by
    dsimp only [F]
    rw [Complex.norm_exp, sq, ← Real.exp_add, ← Real.exp_add]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.re_mul_ofReal]
    congr 1
    ring
  have hFint : (∫ t, ‖F t‖ ^ 2) = Real.sqrt (2 * Real.pi / 3) * Real.exp ((2 / 3) * B.re ^ 2) := by
    simp_rw [hFsq]
    rw [integral_mul_const, integral_add_right_eq_self
      (fun t : ℝ => Real.exp (-(3 / 2) * t ^ 2)), integral_gaussian]
    ring_nf
  have hF : MemLp F 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm (by dsimp [F]; fun_prop)).2
    apply Integrable.of_integral_ne_zero
    rw [hFint]
    positivity
  let W (t : ℝ) := Complex.exp (-((1 : ℝ) : ℂ) * (t : ℂ) ^ 2 + 0 * t) *
    (p ^ 2).eval (t : ℂ)
  have hW : Integrable W := gaussianMoment_integrable 1 (by norm_num) 0 (p ^ 2)
  have hGsq (t : ℝ) : ‖G t‖ ^ 2 = (W t).re := by
    have hp : ‖p.eval (t : ℂ)‖ ^ 2 = ((p.eval (t : ℂ)) ^ 2).re := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [sq, Complex.mul_re, hreal t]
    simp only [G, W, eval_pow, norm_mul, mul_pow, Complex.norm_exp_ofReal,
      Complex.ofReal_one, neg_one_mul, zero_mul, add_zero, hp]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
      Complex.re_ofReal_mul]
    rw [sq (Real.exp _), ← Real.exp_add]
    ring_nf
  have hG : MemLp G 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm (by dsimp [G]; fun_prop)).2
    simpa only [hGsq] using (show Integrable (fun t => (W t).re) from hW.re)
  have hGint : (∫ t, ‖G t‖ ^ 2) = (gaussianMoment 1 0 (p ^ 2)).re := by
    simp_rw [hGsq]
    exact integral_re hW
  rw [hFG, ← hFint, ← hGint]
  exact norm_integral_mul_sq_le F G hF hG

end Turan
