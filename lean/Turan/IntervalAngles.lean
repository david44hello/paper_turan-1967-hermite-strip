-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.RouteDefs
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
open Polynomial Real
namespace Turan

private theorem endpoint_ne (t : ℝ) {z : ℂ} (hz : z.im ≠ 0) : (t:ℂ)-z ≠ 0 := by
  intro h
  exact hz (by rw [← sub_eq_zero.mp h]; rfl)

/-- The principal argument is continuous along the horizontal line t − z.
    Its derivative is the signed integrand, on either side of the real axis. -/
private theorem angle_endpoints (l r : ℝ) (z : ℂ) (hz : z.im ≠ 0) :
    intervalAngle l r z = ((r:ℂ)-z).arg - ((l:ℂ)-z).arg := by
  have hden (t : ℝ) : 0 < (t-z.re)^2 + z.im^2 := add_pos_of_nonneg_of_pos
    (sq_nonneg _) (sq_pos_of_ne_zero hz)
  have hd (t : ℝ) : HasDerivAt (fun x : ℝ => ((x:ℂ)-z).arg)
      (z.im / ((t-z.re)^2 + z.im^2)) t := by
    have hs : (t:ℂ)-z ∈ Complex.slitPlane := Or.inr (by simpa using hz)
    have hlog := (((hasDerivAt_id (t:ℂ)).sub_const z).clog hs).mul_const (-Complex.I)
    simpa [mul_neg, Complex.mul_I_re, Complex.log_im, Complex.inv_im, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, sq] using hlog.real_of_complex
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
  exact (continuous_const.div (by fun_prop) (fun t => (hden t).ne')).intervalIntegrable _ _

private theorem angle_quotient (l r : ℝ) (z : ℂ) (hz : z.im ≠ 0) :
    (intervalAngle l r z : Angle) = ((((r:ℂ)-z)/((l:ℂ)-z)).arg : ℝ) := by
  rw [angle_endpoints l r z hz, Angle.coe_sub, Complex.arg_div_coe_angle
    (endpoint_ne r hz) (endpoint_ne l hz)]

theorem interval_angle_cot (l r : ℝ) (hlr : l < r) (z : ℂ) (hz : z.im ≠ 0) :
    let μ := (l+r)/2
    let s := (r-l)/2
    Real.cot |intervalAngle l r z| = ((z.re-μ)^2+z.im^2-s^2)/(2*|z.im| * s) := by
  dsimp only
  let q := ((r:ℂ)-z)/((l:ℂ)-z)
  have hq : q ≠ 0 := div_ne_zero (endpoint_ne r hz) (endpoint_ne l hz)
  have hlen : |intervalAngle l r z| ≤ π := by
    rw [angle_endpoints l r z hz, abs_le]
    have halfl (x : ℝ) : 0 ≤ ((x:ℂ)-z).arg ↔ z.im ≤ 0 := by
      simp [Complex.sub_im]
    rcases le_or_gt z.im 0 with h | h
    · constructor <;> linarith [(halfl r).mpr h, (halfl l).mpr h,
        Complex.arg_le_pi ((r:ℂ)-z), Complex.arg_le_pi ((l:ℂ)-z)]
    · have hneg (x : ℝ) := lt_of_not_ge (fun hh => h.not_ge ((halfl x).mp hh))
      constructor <;> linarith [hneg r, hneg l, Complex.neg_pi_lt_arg ((r:ℂ)-z),
        Complex.neg_pi_lt_arg ((l:ℂ)-z)]
  have ha : (intervalAngle l r z : Angle) = (q.arg : Angle) := angle_quotient l r z hz
  have hcos := congrArg Angle.cos ha
  have hsin := congrArg Angle.sin ha
  simp only [Angle.cos_coe, Complex.cos_arg hq] at hcos
  simp only [Angle.sin_coe, Complex.sin_arg] at hsin
  have hnorm := Complex.normSq_pos.mpr (endpoint_ne l hz)
  have hre : q.re = ((r-z.re)*(l-z.re)+z.im^2)/((l:ℂ)-z).normSq := by
    simp only [q, Complex.div_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_sub, neg_mul_neg, ← add_div, sq]
  have him : q.im = z.im*(r-l)/((l:ℂ)-z).normSq := by
    simp only [q, Complex.div_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_sub, ← sub_div]
    ring
  rw [Real.cot_eq_cos_div_sin, Real.cos_abs, ← Real.abs_sin_eq_sin_abs_of_abs_le_pi hlen,
    hcos, hsin, abs_div, abs_of_nonneg (norm_nonneg q), div_div_div_cancel_right₀ (norm_ne_zero_iff.mpr hq),
    hre, him, abs_div, abs_mul, abs_of_pos (sub_pos.mpr hlr), abs_of_pos hnorm,
    div_div_div_cancel_right₀ hnorm.ne']
  congr 1 <;> ring

/-- Addition of signed angles for a multiset of nonreal roots, including
    repeated roots. The equality is in ℝ modulo 2π. -/
private theorem roots_angle (l r : ℝ) (s : Multiset ℂ) (hs : ∀ z ∈ s, z.im ≠ 0) :
    (((s.map (intervalAngle l r)).sum : ℝ) : Angle) =
      ((s.map (fun z => ((r:ℂ)-z)/((l:ℂ)-z))).prod.arg : ℝ) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    have hz := hs z (Multiset.mem_cons_self ..)
    have hrest (w : ℂ) (hw : w ∈ s) := hs w (Multiset.mem_cons_of_mem hw)
    have hprod : (s.map (fun w => ((r:ℂ)-w)/((l:ℂ)-w))).prod ≠ 0 := by
      apply Multiset.prod_ne_zero
      intro h
      obtain ⟨w, hw, he⟩ := Multiset.mem_map.mp h
      exact div_ne_zero (endpoint_ne r (hrest w hw)) (endpoint_ne l (hrest w hw)) he
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons, Angle.coe_add]
    rw [Complex.arg_mul_coe_angle (div_ne_zero (endpoint_ne r hz) (endpoint_ne l hz)) hprod,
      angle_quotient l r z hz, ih hrest]

theorem equal_value_angle_sum (p : Polynomial ℂ) (l r : ℝ) (hlr : l < r)
    (hl : l ≠ -1/2) (hr : r ≠ -1/2) (hfree : ∀ x : ℝ, p.eval (x:ℂ) ≠ 0)
    (hval : p.eval (r:ℂ) / p.eval (l:ℂ) = (2*(r:ℂ)+1)/(2*(l:ℂ)+1)) :
    ∃ k : ℤ, (p.roots.map (intervalAngle l r)).sum =
      (2*(k:ℝ)+(if l < -1/2 ∧ -1/2 < r then 1 else 0))*Real.pi := by
  have hoff (z : ℂ) (hz : z ∈ p.roots) : z.im ≠ 0 := by
    intro h
    have he : (z.re:ℂ) = z := Complex.ext rfl h.symm
    exact hfree z.re (he.symm ▸ (isRoot_of_mem_roots hz : p.eval z = 0))
  have hp : p ≠ 0 := by rintro rfl; simpa using hfree 0
  have hprod := roots_angle l r p.roots hoff
  rw [Multiset.prod_map_div] at hprod
  have hf := (IsAlgClosed.splits p).eval_eq_prod_roots
  rw [hf, hf, mul_div_mul_left _ _ (leadingCoeff_ne_zero.mpr hp)] at hval
  let b : ℝ := if l < -1/2 ∧ -1/2 < r then 1 else 0
  have hsign : (((2*r+1)/(2*l+1) : ℝ):ℂ).arg = b*π := by
    by_cases h : l < -1/2 ∧ -1/2 < r
    · rw [Complex.arg_ofReal_of_neg (div_neg_of_pos_of_neg (by linarith [h.2]) (by linarith [h.1]))]
      simp [b, h]
    · have hpos : 0 < (2*r+1)/(2*l+1) := by
        rcases lt_or_gt_of_ne hl with hleft | hleft
        · have hright : r < -1/2 := lt_of_le_of_ne (le_of_not_gt (fun hh => h ⟨hleft, hh⟩)) hr
          exact div_pos_of_neg_of_neg (by linarith) (by linarith)
        · exact div_pos (by linarith) (by linarith)
      rw [Complex.arg_ofReal_of_nonneg hpos.le]
      simp [b, h]
  rw [hval, show (2*(r:ℂ)+1)/(2*(l:ℂ)+1) = (((2*r+1)/(2*l+1) : ℝ):ℂ) by push_cast; rfl,
    hsign] at hprod
  obtain ⟨k, hk⟩ := Angle.angle_eq_iff_two_pi_dvd_sub.mp hprod
  refine ⟨k, ?_⟩
  change _ = (2*(k:ℝ)+b)*π
  linear_combination hk

/-- A continuous phase along the real axis, with its increment computed by summing
the changes of argument of the linear factors with multiplicity. -/
theorem polynomial_argument_on_real_axis (p : Polynomial ℂ) (hf : ∀ t : ℝ, p.eval (t:ℂ) ≠ 0) :
    ∃ A : ℝ → ℝ, Continuous A ∧
    (∀ t : ℝ, Complex.exp ((A t:ℂ)*Complex.I) = p.eval (t:ℂ) / (‖p.eval (t:ℂ)‖:ℂ)) ∧
    ∀ l r : ℝ, l<r → A r - A l = (p.roots.map (intervalAngle l r)).sum := by
  classical
  have hexp (z : ℂ) (hz : z ≠ 0) :
      Complex.exp ((z.arg:ℂ)*Complex.I) = z / (‖z‖:ℂ) := by
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))).mpr
    rw [mul_comm, Complex.norm_mul_exp_arg_mul_I]
  let P (s : Multiset ℂ) (t : ℝ) := (s.map (fun z => (t:ℂ)-z)).prod
  have hphase (s : Multiset ℂ) (hs : ∀ z ∈ s, z.im ≠ 0) :
      ∃ A : ℝ → ℝ, Continuous A ∧
        (∀ t, Complex.exp ((A t:ℂ)*Complex.I) = P s t / (‖P s t‖:ℂ)) ∧
        ∀ l r, A r - A l = (s.map (intervalAngle l r)).sum := by
    induction s using Multiset.induction_on with
    | empty => exact ⟨fun _ => 0, continuous_const, by simp [P], by simp⟩
    | cons z s ih =>
      have hz := hs z (Multiset.mem_cons_self ..)
      obtain ⟨B,hB,hval,hinc⟩ := ih fun w hw => hs w (Multiset.mem_cons_of_mem hw)
      have hcont : Continuous (fun t : ℝ => ((t:ℂ)-z).arg) := by
        apply continuous_iff_continuousAt.mpr
        intro t
        have hsl : (t:ℂ)-z ∈ Complex.slitPlane := Or.inr (by simpa using hz)
        have hd : ContinuousAt (fun v : ℝ => (v:ℂ)-z) t := by fun_prop
        exact ContinuousAt.comp (g := Complex.arg) (f := fun v : ℝ => (v:ℂ)-z)
          (Complex.continuousAt_arg hsl) hd
      refine ⟨fun t => ((t:ℂ)-z).arg + B t, hcont.add hB, ?_, ?_⟩
      · intro t
        rw [Complex.ofReal_add, add_mul, Complex.exp_add, hexp _ (endpoint_ne t hz), hval]
        simp [P, norm_mul, div_mul_div_comm]
      · intro l r
        simp only [Multiset.map_cons, Multiset.sum_cons, angle_endpoints l r z hz, ← hinc]
        ring
  have hp : p ≠ 0 := by rintro rfl; simpa using hf 0
  have hoff (z : ℂ) (hz : z ∈ p.roots) : z.im ≠ 0 := by
    intro h
    have he : (z.re:ℂ) = z := Complex.ext rfl h.symm
    exact hf z.re (he.symm ▸ (isRoot_of_mem_roots hz : p.eval z = 0))
  obtain ⟨A,hA,hval,hinc⟩ := hphase p.roots hoff
  refine ⟨fun t => p.leadingCoeff.arg + A t, continuous_const.add hA, ?_, ?_⟩
  · intro t
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, hexp _ (leadingCoeff_ne_zero.mpr hp), hval]
    rw [(IsAlgClosed.splits p).eval_eq_prod_roots]
    simp [P, norm_mul, div_mul_div_comm]
  · intro l r _
    rw [← hinc]
    ring

end Turan
