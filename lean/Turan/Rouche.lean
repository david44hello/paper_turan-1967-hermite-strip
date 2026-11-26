module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Argument
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

@[expose] public section

noncomputable section
open Polynomial Metric
namespace Turan

theorem polynomial_rouche (p q : Polynomial ℂ) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hd : ∀ z ∈ sphere c r, ‖q.eval z - p.eval z‖ < ‖p.eval z‖) :
    (q.roots.filter (fun z => dist z c < r)).card =
      (p.roots.filter (fun z => dist z c < r)).card := by
  have hp (z) (hz : z ∈ sphere c r) : p.eval z ≠ 0 :=
    norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg _) (hd z hz))
  have hq (z) (hz : z ∈ sphere c r) : q.eval z ≠ 0 := by
    intro heq
    simpa [heq] using hd z hz
  -- The ratio lies in the disk of radius one about one, so its principal
  -- logarithm gives a single primitive along the whole circle.
  have hprimitive : (∮ z in C(c, r),
      q.derivative.eval z / q.eval z - p.derivative.eval z / p.eval z) = 0 := by
    apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt
      (f := fun z => Complex.log (q.eval z / p.eval z)) hr.le
    intro z hz
    have hpz := hp z hz
    have hqz := hq z hz
    have hslit : q.eval z / p.eval z ∈ Complex.slitPlane := by
      apply Complex.ball_one_subset_slitPlane
      rw [mem_ball, dist_eq_norm, show q.eval z / p.eval z - 1 =
        (q.eval z - p.eval z) / p.eval z by rw [sub_div, div_self hpz],
        norm_div, div_lt_one (norm_pos_iff.mpr hpz)]
      exact hd z hz
    have hratio := (q.hasDerivAt z).div (p.hasDerivAt z) hpz
    have hlog := (Complex.hasDerivAt_log hslit).comp z hratio
    apply hlog.hasDerivWithinAt.congr_deriv
    field_simp [hpz, hqz]
  have integrable (s : Polynomial ℂ) (hs : ∀ z ∈ sphere c r, s.eval z ≠ 0) :
      CircleIntegrable (fun z => s.derivative.eval z / s.eval z) c r :=
    ContinuousOn.circleIntegrable hr.le (s.derivative.continuousOn.div s.continuousOn hs)
  rw [circleIntegral.integral_sub (integrable q hq) (integrable p hp),
    polynomial_argument_principle q c r hr hq, polynomial_argument_principle p c r hr hp] at hprimitive
  have hperiod : 2 * Real.pi * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  exact_mod_cast mul_left_cancel₀ hperiod (sub_eq_zero.mp hprimitive)

theorem dominant_polynomial_term (p : Polynomial ℂ) (l : ℕ) (_hl : 1 ≤ l)
    (hd : (∑ k ∈ p.support.erase l, ‖p.coeff k‖) < ‖p.coeff l‖) :
    (p.roots.filter (fun z => ‖z‖ < 1)).card = l := by
  classical
  have hc : p.coeff l ≠ 0 := norm_pos_iff.mp <| lt_of_le_of_lt
    (Finset.sum_nonneg fun _ _ => norm_nonneg _) hd
  let m := monomial l (p.coeff l)
  have boundary (z : ℂ) (hz : z ∈ sphere (0 : ℂ) 1) :
      ‖p.eval z - m.eval z‖ < ‖m.eval z‖ := by
    have hz' : ‖z‖ = 1 := by simpa using mem_sphere.mp hz
    have htail : p.eval z - m.eval z = ∑ k ∈ p.support.erase l, p.coeff k * z^k := by
      apply sub_eq_iff_eq_add.mpr
      rw [eval_eq_sum, Polynomial.sum, eval_monomial]
      exact (Finset.sum_erase_add _ _ (mem_support_iff.mpr hc)).symm
    rw [htail]
    calc
      _ ≤ ∑ k ∈ p.support.erase l, ‖p.coeff k * z^k‖ := norm_sum_le _ _
      _ = ∑ k ∈ p.support.erase l, ‖p.coeff k‖ := by simp [norm_pow, hz']
      _ < ‖p.coeff l‖ := hd
      _ = ‖m.eval z‖ := by simp [m, eval_monomial, norm_pow, hz']
  have hcount := polynomial_rouche m p 0 1 zero_lt_one boundary
  simpa [m, roots_monomial hc, Multiset.filter_nsmul, Multiset.filter_singleton] using hcount

end Turan
