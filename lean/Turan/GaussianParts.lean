-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.GaussianDefs

noncomputable section
open MeasureTheory Polynomial
namespace Turan

/-- Absorb the linear term into half of the Gaussian decay. -/
theorem gaussianWeight_norm_le (A : ℝ) (hA : 0 < A) (B : ℂ) (t : ℝ) :
    ‖Complex.exp (-(A : ℂ) * (t : ℂ)^2 + B*t)‖ ≤
      Real.exp (‖B‖^2 / (2*A)) * Real.exp (-(A/2) * t^2) := by
  rw [Complex.norm_exp, ← Real.exp_add, Real.exp_le_exp, Complex.add_re,
    ← Complex.ofReal_pow, Complex.re_mul_ofReal, Complex.re_mul_ofReal,
    Complex.neg_re, Complex.ofReal_re]
  rw [← sub_le_iff_le_add, le_div_iff₀ (by positivity : 0 < 2*A)]
  nlinarith [sq_nonneg (A*t - B.re), sq_nonneg B.im, Complex.sq_norm_sub_sq_re B]

/-- Every polynomial moment is absolutely integrable. -/
theorem gaussianMoment_integrable (A : ℝ) (hA : 0 < A) (B : ℂ) (p : Polynomial ℂ) :
    Integrable (fun t : ℝ => Complex.exp (-(A : ℂ) * (t : ℂ)^2 + B*t) * p.eval (t : ℂ)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [eval_add, mul_add, Pi.add_def] using hp.add hq
  | monomial n c =>
    have hpow : Integrable (fun t : ℝ => |t|^n * Real.exp (-(A/2) * t^2)) := by
      simpa only [Real.rpow_natCast, Real.norm_eq_abs, abs_mul, abs_pow,
        abs_of_pos (Real.exp_pos _)] using
        (integrable_rpow_mul_exp_neg_mul_sq (half_pos hA)
          (by linarith [Nat.cast_nonneg (α := ℝ) n] : -1 < (n : ℝ))).norm
    simp only [eval_monomial]
    apply (hpow.const_mul (Real.exp (‖B‖^2 / (2*A)) * ‖c‖)).mono' (by fun_prop)
    apply Filter.Eventually.of_forall
    intro t
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ (Real.exp (‖B‖^2 / (2*A)) * Real.exp (-(A/2) * t^2)) * (‖c‖ * |t|^n) :=
        mul_le_mul_of_nonneg_right (gaussianWeight_norm_le A hA B t) (by positivity)
      _ = _ := by ring

theorem gaussianMoment_norm_integrable (A : ℝ) (hA : 0 < A) (B : ℂ) (p : Polynomial ℂ) :
    Integrable (fun t : ℝ => ‖Complex.exp (-(A : ℂ) * (t : ℂ)^2 + B*t) * p.eval (t : ℂ)‖) :=
  (gaussianMoment_integrable A hA B p).norm

theorem gaussianMoment_add (A : ℝ) (hA : 0 < A) (B : ℂ) (p q : Polynomial ℂ) :
    gaussianMoment A B (p + q) = gaussianMoment A B p + gaussianMoment A B q := by
  simpa only [gaussianMoment, eval_add, mul_add] using
    integral_add (gaussianMoment_integrable A hA B p) (gaussianMoment_integrable A hA B q)

theorem gaussianMoment_C_mul (A : ℝ) (hA : 0 < A) (B c : ℂ) (p : Polynomial ℂ) :
    gaussianMoment A B (C c * p) = c * gaussianMoment A B p := by
  simpa only [gaussianMoment, eval_mul, eval_C, mul_left_comm _ c] using
    integral_const_mul_of_integrable (c := c) (gaussianMoment_integrable A hA B p)

theorem gaussianMoment_sub (A : ℝ) (hA : 0 < A) (B : ℂ) (p q : Polynomial ℂ) :
    gaussianMoment A B (p - q) = gaussianMoment A B p - gaussianMoment A B q := by
  simpa only [gaussianMoment, eval_sub, mul_sub] using
    integral_sub (gaussianMoment_integrable A hA B p) (gaussianMoment_integrable A hA B q)

/-- Integrating the derivative of the weighted polynomial over the real line gives zero. -/
theorem gaussianMoment_parts (A : ℝ) (hA : 0 < A) (B : ℂ) (p : Polynomial ℂ) :
    gaussianMoment A B p.derivative =
      (2 * (A : ℂ)) * gaussianMoment A B (X * p) - B * gaussianMoment A B p := by
  let q := p.derivative + C B * p - C (2 * (A : ℂ)) * (X * p)
  have hz : gaussianMoment A B q = 0 := by
    refine integral_eq_zero_of_hasDerivAt_of_integrable ?_
      (gaussianMoment_integrable A hA B q) (gaussianMoment_integrable A hA B p)
    intro t
    have hquad := ((hasDerivAt_pow 2 (t : ℂ)).const_mul (-(A : ℂ))).add
      ((hasDerivAt_id (t : ℂ)).const_mul B)
    convert (hquad.cexp.mul (p.hasDerivAt (t : ℂ))).comp_ofReal using 1 <;>
      simp [q, id, eval_mul]
    ring
  dsimp only [q] at hz
  rw [gaussianMoment_sub A hA, gaussianMoment_add A hA, gaussianMoment_C_mul A hA,
    gaussianMoment_C_mul A hA] at hz
  linear_combination hz

end Turan
