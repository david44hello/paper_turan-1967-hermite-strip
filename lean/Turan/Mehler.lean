-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.GaussianParts
import Turan.HermiteMoments
import Turan.Normalized
import Turan.GaussianBound
import Turan.MehlerScalar

noncomputable section
open Polynomial MeasureTheory
open scoped ComplexConjugate
namespace Turan

private def momentMap (A : ℝ) (hA : 0 < A) (B : ℂ) : Polynomial ℂ →ₗ[ℂ] ℂ where
  toFun := gaussianMoment A B
  map_add' := gaussianMoment_add A hA B
  map_smul' c p := by simpa [← Polynomial.C_mul'] using gaussianMoment_C_mul A hA B c p

private theorem gaussian_one : gaussianMoment 1 0 1 = (Real.sqrt Real.pi : ℂ) := by
  unfold gaussianMoment
  simp only [Complex.ofReal_one, neg_one_mul, zero_mul, add_zero, eval_one, mul_one]
  calc
    _ = ∫ t : ℝ, (Real.exp (-1 * t^2) : ℂ) := by
      congr 1
      funext t
      simp
    _ = _ := by rw [integral_complex_ofReal, integral_gaussian]; simp

/-- A Gaussian integral reproduces the Hermite polynomial. Cauchy--Schwarz
against its Gaussian square norm gives the bound for each individual degree. -/
theorem lemma_nine (n : ℕ) (z : ℂ) :
    ‖psi n z‖ * Real.exp (-z.re^2/2) ≤
      (1 - (1:ℝ)/25) ^ (-(1:ℝ)/4) *
      Real.exp (-z.re^2/3 + z.im^2/4 + ((n:ℝ)/2)*Real.log 5) := by
  let s : ℝ := Real.sqrt (1/5)
  have hs : s^2 = 1/5 := Real.sq_sqrt (by norm_num)
  have hs₀ : 0 ≤ s := Real.sqrt_nonneg _
  let B : ℂ := 5 * (s : ℂ) * z / 2
  let D : ℝ := 2^n * (n.factorial : ℝ)
  have hD : 0 < D := by dsimp [D]; positivity
  have hbRe : (2/3) * B.re^2 = 5*z.re^2/6 := by
    simp [B, Complex.div_ofNat_re, Complex.mul_re] <;> linear_combination (25*z.re^2/6) * hs
  have hbSq : (B^2).re/(2*(5/4)) = (z.re^2-z.im^2)/2 := by
    norm_num [B, pow_two, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
    linear_combination (5/2*(z.re^2-z.im^2)) * hs
  have hmass : gaussianMoment 1 0 (hermite n ^ 2) = (D * Real.sqrt Real.pi : ℝ) := by
    have hw := hermite_square_moment (momentMap 1 (by norm_num) 0) (fun p => by
      simpa [momentMap] using gaussianMoment_parts 1 (by norm_num) 0 p) n
    simpa [momentMap, D, gaussian_one] using hw
  have hsC : 5*(s:ℂ)^2 = 1 := by exact_mod_cast (show 5*s^2=1 by linarith)
  have hrep : gaussianMoment (5/4) B (hermite n) =
      (s : ℂ)^n * (hermite n).eval z * gaussianMoment (5/4) B 1 :=
    hermite_shifted_moment (momentMap (5/4) (by norm_num) B) s z hsC (fun p => by
      have hp := gaussianMoment_parts (5/4) (by norm_num) B p
      norm_num [momentMap, B] at hp ⊢
      exact hp) n
  have hreal (t : ℝ) : ((hermite n).eval (t : ℂ)).im = 0 := by
    have hconj := congrArg Complex.im (hermite_symmetry n (t : ℂ)).1
    simp at hconj
    linarith
  have hc := gaussianMoment_cauchy B (hermite n) hreal
  rw [hmass, Complex.ofReal_re, hrep, norm_mul, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hs₀, mul_pow, mul_pow,
    gaussianMoment_one_norm_sq (5/4) (by norm_num) B, hbSq, hbRe] at hc
  have hsN : (s^n)^2 = (1/5:ℝ)^n := by rw [← pow_mul, Nat.mul_comm, pow_mul, hs]
  rw [hsN] at hc
  have hroot : Real.sqrt (2*Real.pi/3) * Real.sqrt Real.pi =
      Real.pi * Real.sqrt (2/3) := by
    rw [show 2*Real.pi/3 = (2/3)*Real.pi by ring, Real.sqrt_mul (by norm_num)]
    nlinarith [Real.sq_sqrt Real.pi_pos.le, mul_assoc (Real.sqrt (2/3)) (Real.sqrt Real.pi)
      (Real.sqrt Real.pi), congrArg (fun t : ℝ => Real.sqrt (2/3)*t) (Real.sq_sqrt Real.pi_pos.le)]
  apply mehler_scalar n z.re z.im _ (norm_nonneg _)
  apply (le_of_mul_le_mul_right (a := D) _ hD)
  have hpsi : ‖psi n z‖^2 * D = ‖(hermite n).eval z‖^2 := by
    simp only [psi, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_pow]
    change ‖(hermite n).eval z‖^2 / (Real.sqrt D)^2 * D = _
    rw [Real.sq_sqrt hD.le, div_mul_cancel₀ _ hD.ne']
  calc
    _ = (1/5:ℝ)^n * ‖(hermite n).eval z‖^2 *
        (Real.pi / (5/4) * Real.exp ((z.re^2-z.im^2)/2)) := by rw [← hpsi]; ring
    _ ≤ _ := hc
    _ = _ := by rw [← hroot]; ring

end Turan
