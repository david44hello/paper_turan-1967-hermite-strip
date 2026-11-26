module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.GeneratingJets
public import Turan.GeneratingProducts
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

noncomputable section
namespace Turan.Generating
open Metric Filter
open scoped Topology

private def kernel (A S t : ℂ) := Complex.exp
  (-Complex.log (1-t^2)/2 + (A*t-S*t^2)/(1-t^2))

private theorem kernel_diff (A S t : ℂ) (ht : ‖t‖ < 1) :
    HasDerivAt (kernel A S)
      ((A+(1-2*S)*t+A*t^2-t^3)/(1-t^2)^2 * kernel A S t) t := by
  have hsl : 1-t^2 ∈ Complex.slitPlane := by
    apply Or.inl
    have h := Complex.re_le_norm (t^2)
    rw [norm_pow] at h
    simpa only [Complex.sub_re, Complex.one_re, sub_pos] using
      h.trans_lt (pow_lt_one₀ (norm_nonneg _) ht (by decide))
  have hd : (1-t^2 : ℂ) ≠ 0 := Complex.slitPlane_ne_zero hsl
  have hq : HasDerivAt (fun u : ℂ => 1-u^2) (-(2*t)) t := by
    simpa using ((hasDerivAt_id t).pow 2).const_sub (1:ℂ)
  have hn : HasDerivAt (fun u : ℂ => A*u-S*u^2) (A-S*(2*t)) t := by
    simpa [Pi.sub_def] using! ((hasDerivAt_id t).const_mul A).sub (((hasDerivAt_id t).pow 2).const_mul S)
  have h := (((((Complex.hasDerivAt_log hsl).comp t hq).neg.div_const 2).add
    (hn.div hq hd)).cexp)
  convert h using 1
  · rfl
  · change _ = kernel A S t * _
    field_simp [hd]
    ring

/-- The Taylor coefficients of the analytic kernel and the normalized Hermite
products have the same initial values and the same four-step recurrence. -/
private theorem kernel_coeffs (z w : ℂ) :
    ∀ n, jet (kernel (2*z*w) (z^2+w^2)) n = term z w n := by
  let A := 2*z*w
  let S := z^2+w^2
  let f := kernel A S
  have hd : DifferentiableOn ℂ f (ball 0 1) := fun t ht =>
    (kernel_diff A S t (mem_ball_zero_iff.mp ht)).differentiableAt.differentiableWithinAt
  have ha : AnalyticAt ℂ f 0 := hd.analyticAt (ball_mem_nhds _ zero_lt_one)
  have he : deriv f =ᶠ[𝓝 0] rhs A (1-2*S) f := by
    filter_upwards [ball_mem_nhds (0:ℂ) zero_lt_one] with t ht
    have ht' := mem_ball_zero_iff.mp ht
    have hdiff := (kernel_diff A S t ht').deriv
    change deriv f t = _ at hdiff
    have hne : 1-t^2 ≠ 0 := sub_ne_zero.mpr (fun h => by
      have hlt := pow_lt_one₀ (norm_nonneg t) ht' (by decide : 2 ≠ 0)
      rw [← norm_pow, ← h, norm_one] at hlt
      exact (lt_irrefl _ hlt))
    simp only [rhs, Pi.add_apply, shift, scale, hdiff]
    change _ = A*f t+t*((1-2*S)*f t+2*(t*(_*f t))+t*(A*f t+t*(-1*f t + -1*(t*(_*f t)))))
    field_simp [hne]
    ring
  obtain ⟨j1,j2,j3,jrec⟩ := jet_recurrences f A (1-2*S) ha he
  obtain ⟨t0,t1,t2,t3⟩ := term_init z w
  have h0 : jet f 0 = term z w 0 := by simp [jet,f,kernel,t0]
  have h1 : jet f 1 = term z w 1 := by rw [j1,h0,t0,t1,mul_one]
  have h2 : jet f 2 = term z w 2 := by
    rw [h0,h1] at j2
    dsimp [A,S] at j2
    linear_combination (j2-t2)/2
  have h3 : jet f 3 = term z w 3 := by
    rw [h0,h1,h2] at j3
    dsimp [A,S] at j3
    linear_combination (j3-t3)/3
  intro n
  change jet f n = _
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | ⟨_ | ⟨_ | ⟨_ | n⟩⟩⟩
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · have u := jrec n
      rw [ih (n+3) (by omega), ih (n+2) (by omega), ih (n+1) (by omega), ih n (by omega)] at u
      have hn : (n:ℂ)+4 ≠ 0 := by exact_mod_cast (show n+4 ≠ 0 by omega)
      exact mul_left_cancel₀ hn (u.trans (term_recurrence z w n).symm)

end Turan.Generating

namespace Turan
open Generating Metric

theorem mehler_kernel (r : ℝ) (hr : 0 ≤ r) (hr' : r < 1) (z w : ℂ) :
    HasSum (fun k : ℕ => (r:ℂ)^k * psi k z * psi k w)
      ((Real.sqrt (1-r^2):ℂ)⁻¹ * Complex.exp
        ((2*z*w*r-(z^2+w^2)*r^2)/(1-(r:ℂ)^2))) := by
  let f := kernel (2*z*w) (z^2+w^2)
  have hd : DifferentiableOn ℂ f (ball 0 1) := fun t ht =>
    (kernel_diff _ _ _ (mem_ball_zero_iff.mp ht)).differentiableAt.differentiableWithinAt
  have hrC : (r:ℂ) ∈ ball (0:ℂ) 1 := by simpa [abs_of_nonneg hr] using hr'
  have hp : 0 < 1-r^2 := sub_pos.mpr (pow_lt_one₀ hr hr' (by decide))
  have hpre : Complex.exp (-Complex.log (1-(r:ℂ)^2)/2) = (Real.sqrt (1-r^2):ℂ)⁻¹ := by
    rw [show 1-(r:ℂ)^2 = ((1-r^2:ℝ):ℂ) by push_cast; rfl, ← Complex.ofReal_log hp.le]
    norm_cast
    rw [neg_div, Real.exp_neg, ← Real.log_sqrt hp.le, Real.exp_log (Real.sqrt_pos.mpr hp)]
  have hsum := Complex.hasSum_taylorSeries_on_ball hd hrC
  rw [← hpre, ← Complex.exp_add]
  apply hsum.congr_fun
  intro k
  have h := (kernel_coeffs z w k).trans (term_psi z w k)
  change iteratedDeriv k f 0 / k.factorial = _ at h
  simp only [sub_zero, smul_eq_mul]
  linear_combination -(r:ℂ)^k * h

end Turan
