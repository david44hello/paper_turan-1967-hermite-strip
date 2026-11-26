module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs
public import Mathlib.Analysis.MeanInequalities

@[expose] public section

noncomputable section
open Polynomial
namespace Turan

/-- The geometric interpolation of the endpoint moduli is a lower bound at z. -/
private def EndpointBound (t : ℝ) (L R z : ℂ) (f : ℂ → ℂ) : Prop :=
  ‖f L‖ ^ (1 - t) * ‖f R‖ ^ t ≤ ‖f z‖

private theorem EndpointBound.mul {t L R z} {f g : ℂ → ℂ}
    (hf : EndpointBound t L R z f) (hg : EndpointBound t L R z g) :
    EndpointBound t L R z (fun v => f v * g v) := by
  unfold EndpointBound at *
  simp only [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  rw [mul_mul_mul_comm]
  exact mul_le_mul hf hg (by positivity) (norm_nonneg _)

private theorem EndpointBound.minimum {t L R z} {f : ℂ → ℂ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hf : EndpointBound t L R z f) : min ‖f L‖ ‖f R‖ ≤ ‖f z‖ := by
  -- If either endpoint is a zero, the lower bound is already zero.
  rcases eq_or_lt_of_le (le_min (norm_nonneg (f L)) (norm_nonneg (f R))) with hzero | hpos
  · rw [← hzero]
    exact norm_nonneg _
  let m := min ‖f L‖ ‖f R‖
  calc
    m = m ^ (1 - t) * m ^ t := by rw [← Real.rpow_add hpos, sub_add_cancel, Real.rpow_one]
    _ ≤ ‖f L‖ ^ (1 - t) * ‖f R‖ ^ t :=
      mul_le_mul (Real.rpow_le_rpow hpos.le (min_le_left ..) (sub_nonneg.mpr ht'))
        (Real.rpow_le_rpow hpos.le (min_le_right ..) ht) (by positivity) (by positivity)
    _ ≤ ‖f z‖ := hf

private theorem polynomial_endpoint_bound (p : Polynomial ℂ)
    (hreal : ∀ w : ℂ, p.eval w = 0 → w.im = 0) {t L R z}
    (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hfactor : ∀ w : ℂ, w.im = 0 → EndpointBound t L R z (· - w)) :
    EndpointBound t L R z (fun v => p.eval v) := by
  have hprod (s : Multiset ℂ) (hs : ∀ w ∈ s, w.im = 0) :
      EndpointBound t L R z (fun v => (s.map (v - ·)).prod) := by
    induction s using Multiset.induction_on with
    | empty => simp [EndpointBound]
    | cons w s ih =>
      have hw := hfactor w (hs w (Multiset.mem_cons_self ..))
      have hrest := ih (fun a ha => hs a (Multiset.mem_cons_of_mem ha))
      simpa only [Multiset.map_cons, Multiset.prod_cons] using hw.mul hrest
  have hconst : EndpointBound t L R z (fun _ => p.leadingCoeff) := by
    unfold EndpointBound
    rw [← Real.rpow_add_of_nonneg (norm_nonneg _) (sub_nonneg.mpr ht') ht,
      sub_add_cancel, Real.rpow_one]
  have hroots := hprod p.roots (fun w hw => hreal w (isRoot_of_mem_roots hw))
  simpa only [(IsAlgClosed.splits p).eval_eq_prod_roots] using hconst.mul hroots

/-- The horizontal coordinate determines the same interpolation weight for
    every real root and for the Gaussian. -/
private theorem circle_endpoint_bounds (p : Polynomial ℂ)
    (hreal : ∀ w : ℂ, p.eval w = 0 → w.im = 0)
    (x r : ℝ) (hr : 0 < r) (z : ℂ) (hz : ‖z - (x : ℂ)‖ = r) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      EndpointBound t (↑(x-r)) (↑(x+r)) z (fun v => p.eval v) ∧
      EndpointBound t (↑(x-r)) (↑(x+r)) z (fun v => Complex.exp (-v^2/2)) := by
  let t := (z.re - x + r) / (2 * r)
  have hrad : 0 < 2 * r := by positivity
  have hre := Complex.abs_re_le_norm (z - (x : ℂ))
  rw [hz, Complex.sub_re, Complex.ofReal_re, abs_le] at hre
  have ht : 0 ≤ t := div_nonneg (by linarith [hre.1]) hrad.le
  have ht' : t ≤ 1 := (div_le_iff₀ hrad).mpr (by linarith [hre.2])
  have hcoord : 2 * r * t = z.re - x + r := by dsimp [t]; field_simp
  have hcircle := congrArg (fun a : ℝ => a^2) hz
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, sub_zero] at hcircle
  have distances (w : ℂ) (hw : w.im = 0) :
      (1-t) * ‖(↑(x-r) : ℂ) - w‖^2 + t * ‖(↑(x+r) : ℂ) - w‖^2 = ‖z-w‖^2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, hw, sub_zero, mul_zero, add_zero]
    linear_combination 2 * (x - w.re) * hcoord - hcircle
  refine ⟨t, ht, ht', polynomial_endpoint_bound p hreal ht ht' ?_, ?_⟩
  · intro w hw
    unfold EndpointBound
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
    rw [mul_pow, Real.rpow_pow_comm (norm_nonneg _), Real.rpow_pow_comm (norm_nonneg _),
      ← distances w hw]
    exact Real.geom_mean_le_arith_mean2_weighted (sub_nonneg.mpr ht') ht
      (sq_nonneg _) (sq_nonneg _) (sub_add_cancel _ _)
  · -- The Gaussian log modulus exceeds the endpoint interpolation by z.im².
    have hzero := distances 0 rfl
    simp only [sub_zero, Complex.sq_norm, Complex.normSq_apply, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, add_zero] at hzero
    unfold EndpointBound
    rw [Complex.norm_exp, Complex.norm_exp, Complex.norm_exp, ← Real.exp_mul, ← Real.exp_mul,
      ← Real.exp_add, Real.exp_le_exp]
    norm_num [pow_two, Complex.mul_re, Complex.div_re]
    nlinarith only [hzero, sq_nonneg z.im]

theorem real_rooted_circle (p : Polynomial ℂ) (hreal : ∀ w : ℂ, p.eval w = 0 → w.im = 0)
    (x r : ℝ) (hr : 0 < r) (z : ℂ) (hz : ‖z - (x : ℂ)‖ = r) :
    min ‖p.eval ((x-r : ℝ):ℂ)‖ ‖p.eval ((x+r : ℝ):ℂ)‖ ≤ ‖p.eval z‖ := by
  obtain ⟨_, ht, ht', hp, _⟩ := circle_endpoint_bounds p hreal x r hr z hz
  exact hp.minimum ht ht'

theorem real_rooted_weighted_circle (p : Polynomial ℂ) (hreal : ∀ w : ℂ, p.eval w = 0 → w.im = 0)
    (x r : ℝ) (hr : 0 < r) (z : ℂ) (hz : ‖z - (x : ℂ)‖ = r) :
    let f := fun w : ℂ => Complex.exp (-w^2/2) * p.eval w
    min ‖f ((x-r : ℝ):ℂ)‖ ‖f ((x+r : ℝ):ℂ)‖ ≤ ‖f z‖ := by
  obtain ⟨_, ht, ht', hp, hg⟩ := circle_endpoint_bounds p hreal x r hr z hz
  exact (hg.mul hp).minimum ht ht'

end Turan
