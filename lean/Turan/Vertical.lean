-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Normalized
import Turan.Hermite
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace Turan

private def scale (j : ℕ) : ℝ := Real.sqrt (2^j * (j.factorial : ℝ))
private def freq (j : ℕ) : ℝ := Real.sqrt (2*((j:ℝ)+1))

private theorem scale_pos (j : ℕ) : 0 < scale j := by
  have := Nat.factorial_pos j
  unfold scale
  positivity

private theorem freq_pos (j : ℕ) : 0 < freq j := by unfold freq; positivity

private theorem freq_sq (j : ℕ) : freq j ^ 2 = 2*((j:ℝ)+1) := Real.sq_sqrt (by positivity)

private theorem scale_succ (j : ℕ) : scale (j+1) = freq j * scale j := by
  unfold scale freq
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  ring

private theorem raising (j : ℕ) :
    (hermite j).derivative = 2 * X * hermite j - hermite (j+1) := by
  cases j with
  | zero => simp [hermite]
  | succ j =>
    rw [hermite_derivative]
    change _ = _ - (2 * X * hermite (j+1) - _)
    abel

private theorem psi_derivatives (j : ℕ) (z : ℂ) :
    HasDerivAt (psi (j+1)) ((freq j : ℂ)*psi j z) z ∧
    HasDerivAt (psi j) (2*z*psi j z - (freq j : ℂ)*psi (j+1) z) z := by
  have hscale : (scale j : ℂ) ≠ 0 := by exact_mod_cast (scale_pos j).ne'
  have hfreq : (freq j : ℂ) ≠ 0 := by exact_mod_cast (freq_pos j).ne'
  have hsq : (freq j : ℂ)^2 = 2*((j:ℂ)+1) := by exact_mod_cast freq_sq j
  constructor
  · convert (((hermite (j+1)).hasDerivAt z).div_const (scale (j+1) : ℂ)) using 1
    · rfl
    change (freq j : ℂ)*((hermite j).eval z/(scale j:ℂ)) =
      (hermite (j+1)).derivative.eval z/(scale (j+1):ℂ)
    rw [hermite_derivative, eval_smul, nsmul_eq_mul, scale_succ]
    push_cast
    field_simp [hscale,hfreq]
    linear_combination (hermite j).eval z * hsq
  · convert (((hermite j).hasDerivAt z).div_const (scale j : ℂ)) using 1
    · rfl
    change 2*z*((hermite j).eval z/(scale j:ℂ)) -
      (freq j:ℂ)*((hermite (j+1)).eval z/(scale (j+1):ℂ)) = _
    rw [raising, eval_sub, eval_mul, eval_mul, eval_X, eval_ofNat, scale_succ]
    push_cast
    field_simp [hscale,hfreq]

/-- The adjacent normalized modes give the real-axis and vertical first-order systems. -/
theorem psi_adjacent_derivatives (j : ℕ) (z : ℂ) :
    let f : ℝ := Real.sqrt (2*((j:ℝ)+1))
    HasDerivAt (psi (j+1)) ((f : ℂ)*psi j z) z ∧
    HasDerivAt (psi j) (2*z*psi j z - (f : ℂ)*psi (j+1) z) z :=
  psi_derivatives j z

/-- The sum of squared consecutive normalized values at zero is at most one.
The recurrence at zero multiplies every other value by a factor of modulus at most one. -/
private theorem energy_zero (j : ℕ) : ‖psi (j+1) 0‖^2 + ‖psi j 0‖^2 ≤ 1 := by
  induction j with
  | zero => norm_num [psi, hermite]
  | succ j ih =>
    have hscale : (scale j : ℂ) ≠ 0 := by exact_mod_cast (scale_pos j).ne'
    have hfreq : (freq j : ℂ) ≠ 0 := by exact_mod_cast (freq_pos j).ne'
    have hnext : (freq (j+1) : ℂ) ≠ 0 := by exact_mod_cast (freq_pos _).ne'
    have hf : (freq j : ℂ)^2 = 2*((j:ℂ)+1) := by exact_mod_cast freq_sq j
    have he : psi (j+2) 0 = -(freq j / freq (j+1) : ℝ) * psi j 0 := by
      change (2*X*hermite (j+1) - (2*(j+1) : ℕ) • hermite j).eval (0:ℂ) / (scale (j+2):ℂ) =
        _ * ((hermite j).eval 0 / (scale j:ℂ))
      rw [eval_sub, eval_smul]
      simp only [eval_mul, eval_X, mul_zero, zero_mul, zero_sub,
        nsmul_eq_mul, Nat.cast_mul, Nat.cast_succ, scale_succ, Complex.ofReal_mul,
        Complex.ofReal_div]
      field_simp [hscale,hfreq,hnext]
      linear_combination (hermite j).eval 0 * hf
    have hr : |freq j / freq (j+1)| ≤ 1 := by
      rw [abs_of_pos (div_pos (freq_pos _) (freq_pos _)), div_le_one (freq_pos _)]
      unfold freq
      apply Real.sqrt_le_sqrt
      push_cast
      linarith
    have hn : ‖psi (j+2) 0‖ ≤ ‖psi j 0‖ := by
      rw [he, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      simpa using mul_le_mul_of_nonneg_right hr (norm_nonneg (psi j 0))
    nlinarith [sq_le_sq' (by linarith [norm_nonneg (psi j 0), norm_nonneg (psi (j+2) 0)]) hn]

private theorem energy_rate (P Q c : ℂ) (t k : ℝ) (hk : 0 ≤ k) (ht : t ∈ Set.Icc 0 1) :
    2 * inner ℝ P ((k:ℂ)*Q*c) + 2 * inner ℝ Q ((2*((t:ℂ)*c)*Q-(k:ℂ)*P)*c) ≤
    (4*c.re^2 + 2*k*|c.im|)*(‖P‖^2+‖Q‖^2) := by
  let d := P.im*Q.re-P.re*Q.im
  let E := ‖P‖^2+‖Q‖^2
  have hd : 2*|d| ≤ E := by
    dsimp [d,E]
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    cases le_total 0 (P.im*Q.re-P.re*Q.im) with
    | inl hn => rw [abs_of_nonneg hn]; nlinarith [sq_nonneg (P.im-Q.re), sq_nonneg (P.re+Q.im)]
    | inr hn => rw [abs_of_nonpos hn]; nlinarith [sq_nonneg (P.im+Q.re), sq_nonneg (P.re-Q.im)]
  have he : 2 * inner ℝ P ((k:ℂ)*Q*c) + 2 * inner ℝ Q ((2*((t:ℂ)*c)*Q-(k:ℂ)*P)*c) =
      4*k*(c.im*d) + 4*t*(c.re^2-c.im^2)*‖Q‖^2 := by
    simp [d, real_inner_eq_re_inner ℂ, RCLike.inner_apply, Complex.mul_re, Complex.mul_im,
      Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  rw [he]
  have hdet : c.im*d ≤ |c.im| *|d| := by rw [← abs_mul]; exact le_abs_self _
  have hc : 4*k*(c.im*d) ≤ 2*k*|c.im| *E := by
    nlinarith only [mul_le_mul_of_nonneg_left hdet (show 0 ≤ 4*k by positivity),
      mul_le_mul_of_nonneg_left hd (show 0 ≤ 2*k*|c.im| by positivity)]
  have ht' : t*(c.re^2-c.im^2) ≤ c.re^2 := by
    nlinarith [mul_nonneg ht.1 (sq_nonneg c.im), mul_nonneg (sub_nonneg.mpr ht.2) (sq_nonneg c.re)]
  have hc' := mul_le_mul_of_nonneg_right ht' (sq_nonneg ‖Q‖)
  dsimp [E] at hc
  nlinarith only [hc, hc', mul_nonneg (sq_nonneg c.re) (sq_nonneg ‖P‖)]

/-- Apply the Hermite equation along the line from zero to the evaluation point.
Only the imaginary component of the direction contributes to the cross term
in the derivative of the energy. -/
private theorem energy_segment (j : ℕ) (c : ℂ) :
    ‖psi (j+1) c‖^2 ≤ Real.exp (4*c.re^2 + 2*freq j*|c.im|) := by
  let P (t : ℝ) := psi (j+1) ((t:ℂ)*c)
  let Q (t : ℝ) := psi j ((t:ℂ)*c)
  let E (t : ℝ) := ‖P t‖^2 + ‖Q t‖^2
  let K := 4*c.re^2 + 2*freq j*|c.im|
  let V (t : ℝ) := 2 * inner ℝ (P t) ((freq j:ℂ)*Q t*c) +
    2 * inner ℝ (Q t) ((2*((t:ℂ)*c)*Q t - (freq j:ℂ)*P t)*c)
  have hE (t : ℝ) : HasDerivAt E (V t) t := by
    obtain ⟨hp,hq⟩ := psi_derivatives j ((t:ℂ)*c)
    have hline : HasDerivAt (fun z : ℂ => z*c) c (t:ℂ) := by simpa using (hasDerivAt_id (t:ℂ)).mul_const c
    exact ((hp.comp (t:ℂ) hline).comp_ofReal.norm_sq).add ((hq.comp (t:ℂ) hline).comp_ofReal.norm_sq)
  let g (t : ℝ) := E t * Real.exp (-K*t)
  have hg (t : ℝ) : HasDerivAt g ((V t - K*E t)*Real.exp (-K*t)) t := by
    have he : HasDerivAt (fun t : ℝ => -K*t) (-K) t := by simpa using (hasDerivAt_id t).const_mul (-K)
    convert (hE t).mul he.exp using 1
    ring
  have hanti : AntitoneOn g (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun t _ => (hg t).continuousAt.continuousWithinAt)
      (fun t _ => (hg t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hg t).deriv]
    apply mul_nonpos_of_nonpos_of_nonneg _ (Real.exp_pos _).le
    exact sub_nonpos.mpr (energy_rate (P t) (Q t) c t (freq j) (freq_pos j).le (interior_subset ht))
  have hle := hanti (show (0:ℝ) ∈ Set.Icc 0 1 by simp) (show (1:ℝ) ∈ Set.Icc 0 1 by simp) zero_le_one
  simp only [g,E,P,Q, Complex.ofReal_one, one_mul, mul_one, Complex.ofReal_zero, zero_mul,
    mul_zero, Real.exp_zero] at hle
  rw [Real.exp_neg, ← div_eq_mul_inv] at hle
  have he := (div_le_iff₀ (Real.exp_pos K)).mp (hle.trans (energy_zero j))
  nlinarith only [he, sq_nonneg ‖psi j c‖, show K = 4*c.re^2+2*freq j*|c.im| by rfl]

theorem lemma_twelve (m : ℕ) (hm : 1 ≤ m) (c : ℂ) (hx : |c.re| ≤ 2)
    (hy : |c.im| < 76/100) :
    ‖psi m c‖ ≤ Real.exp (8 + (76/100) * Real.sqrt (2 * (m : ℝ))) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hbound := energy_segment j c
  have hx2 : c.re^2 ≤ 4 := by nlinarith [sq_abs c.re, sq_le_sq' (by linarith [abs_nonneg c.re]) hx]
  have hK : 4*c.re^2+2*freq j*|c.im| ≤ 2*(8 + (76/100)*freq j) := by
    nlinarith [mul_le_mul_of_nonneg_left hy.le (freq_pos j).le]
  have hsq := hbound.trans (Real.exp_le_exp.mpr hK)
  rw [two_mul, Real.exp_add] at hsq
  rw [Nat.cast_succ]
  change ‖psi (j+1) c‖ ≤ Real.exp (8 + (76/100)*freq j)
  nlinarith [Real.exp_pos (8 + (76/100)*freq j)]

end Turan
