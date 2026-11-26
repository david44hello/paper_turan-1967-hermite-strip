module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Metric
namespace Turan

/-- Strict boundary dominance implies a zero in the open disk. The proof uses
the maximum modulus principle on the exponential of a holomorphic quotient. -/
theorem circle_comparison {F P : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (Metric.closedBall c r))
    (hP : DifferentiableOn ℂ P (Metric.closedBall c r))
    (hzero : ∃ z ∈ Metric.ball c r, P z = 0)
    (hdom : ∀ z ∈ Metric.sphere c r, ‖F z - P z‖ < ‖P z‖) :
    ∃ z ∈ Metric.ball c r, F z = 0 := by
  by_contra! hf
  have nonzero (z : ℂ) (hz : z ∈ closedBall c r) : F z ≠ 0 := by
    rcases lt_or_eq_of_le (mem_closedBall.mp hz) with hin | heq
    · exact hf z hin
    · intro hzF
      simpa [hzF] using hdom z heq
  let g (z : ℂ) := Complex.exp (-(P z / F z))
  have hg : DifferentiableOn ℂ g (closedBall c r) :=
    Complex.differentiable_exp.comp_differentiableOn (hP.div hF nonzero).neg
  have bd (w : ℂ) (hw : w ∈ frontier (ball c r)) : ‖g w‖ ≤ Real.exp (-1/2) := by
    have hs := frontier_ball_subset_sphere hw
    have hn := hdom w hs
    have hpos := Complex.normSq_pos.mpr (nonzero w (sphere_subset_closedBall hs))
    have hsq := (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hsq
    rw [show ‖g w‖ = Real.exp (-(P w / F w).re) by simp [g, Complex.norm_exp],
      Real.exp_le_exp]
    rw [Complex.div_re, ← add_div]
    have hhalf : 1/2 < ((P w).re * (F w).re + (P w).im * (F w).im) / (F w).normSq := by
      apply (lt_div_iff₀ hpos).mpr
      rw [Complex.normSq_apply]
      nlinarith only [hsq]
    linarith
  obtain ⟨z, hz, hzP⟩ := hzero
  have he := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    (hg.diffContOnCl_ball subset_rfl) bd (subset_closure hz)
  have hbad : (1 : ℝ) ≤ Real.exp (-1/2) := by simpa [g, hzP] using he
  exact (not_le_of_gt (Real.exp_lt_one_iff.mpr (by norm_num : (-1/2:ℝ) < 0))) hbad

theorem circle_at_neg_half (r : ℝ) (z : ℂ) (hz : ‖z + 1/2‖ = r) :
    ‖1 + 2*z‖ = 2*r := by
  rw [show 1 + 2*z = 2 * (z+1/2) by ring, norm_mul, hz]
  norm_num

theorem disk_in_strip (c z : ℂ) (r t : ℝ) (hr : |c.im| + r < t)
    (hz : z ∈ Metric.closedBall c r) : |z.im| < t := by
  have hi := Complex.abs_im_le_norm (z-c)
  rw [Complex.sub_im] at hi
  have hd : ‖z-c‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hz
  have := abs_add_le (z.im-c.im) c.im
  rw [sub_add_cancel] at this
  linarith

theorem circle_coefficient_bound (a b : ℂ) (d e s t : ℝ)
    (horient : (a * star b).re * d * e ≥ 0) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s^2 + t^2 ≤ 1) :
    s * ‖a * (d : ℂ)‖ + t * ‖b * (e : ℂ)‖ ≤ ‖a*(d : ℂ) + b*(e : ℂ)‖ := by
  let x := a*(d : ℂ)
  let y := b*(e : ℂ)
  have cross : 0 ≤ x.re*y.re + x.im*y.im := by
    simp [x, y, Complex.mul_re, Complex.mul_im, Complex.star_def] at horient ⊢
    linarith only [horient]
  have hadd : ‖x‖^2 + ‖y‖^2 ≤ ‖x+y‖^2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im]
    nlinarith only [cross]
  have hsum : 0 ≤ ‖x‖^2 + ‖y‖^2 := by positivity
  change s * ‖x‖ + t * ‖y‖ ≤ ‖x+y‖
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
  nlinarith only [sq_nonneg (t*‖x‖-s*‖y‖), mul_nonneg (sub_nonneg.mpr hst) hsum, hadd]

end Turan
