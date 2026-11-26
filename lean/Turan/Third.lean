module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Constants
public import Mathlib.Tactic

@[expose] public section

noncomputable section
namespace Turan

private def den (s y : ℝ) := 16 * (s^2 + y^2)^2 + 8 * (s^2 - y^2) + 1
private def num (s y : ℝ) := y * (8 * (s^2 + y^2) + 8*s - 2)

private theorem den_pos (s y : ℝ) (hy : 1/2 < y) : 0 < den s y := by
  have h₁ : 0 < 2*y-1 := by linarith
  have h₂ : 0 < 2*y+1 := by linarith
  have he : den s y = (4*s^2+(2*y-1)^2)*(4*s^2+(2*y+1)^2) := by unfold den; ring
  rw [he]
  positivity

private theorem normSq_den (w : ℂ) : Complex.normSq (4*w^2+1) = den w.re w.im := by
  norm_num [den, Complex.normSq_apply, pow_two, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im]
  ring

theorem third_den_ne (w : ℂ) (hw : 1/2 < w.im) : 4*w^2+1 ≠ 0 := by
  apply Complex.normSq_pos.mp
  rw [normSq_den]
  exact den_pos _ _ hw

private theorem third_im (w : ℂ) (hw : 1/2 < w.im) :
    (third w).im * den w.re w.im = num w.re w.im := by
  rw [third, Complex.div_im, normSq_den]
  have hp := (den_pos w.re w.im hw).ne'
  field_simp [hp]
  norm_num [num, Complex.neg_im, Complex.neg_re, Complex.add_re, Complex.add_im,
    pow_two, Complex.mul_im, Complex.mul_re]
  ring

/-- On moving vertically above the boundary, both cleared strip inequalities
increase strictly from their boundary values. -/
private theorem vertical_bounds (s H t : ℝ) (hH : 0 < H) (hH2 : 3/4 ≤ H^2) (ht : 0 < t) :
    H * den s H - num s H < H * den s (H+t) - num s (H+t) ∧
    H * den s H + num s H < H * den s (H+t) + num s (H+t) := by
  set d := H^2-3/4 with hd
  have hd₀ : 0 ≤ d := by dsimp [d]; linarith
  have hm₁ : 0 < d*(64*H^2+8) + 64*d*s^2 + 4*(s-1)^2+36*s^2+4 := by positivity
  have hp₁ : 0 < d*(64*H^2+56) + 64*d*s^2 + 4*(s+1)^2+52*s^2+36 := by positivity
  have hm₂ : 0 < H*(96*d+40+32*s^2) := by positivity
  have hp₂ : 0 < H*(96*d+88+32*s^2) := by positivity
  have hm₃ : 0 < 64*d+40 := by positivity
  have hp₃ : 0 < 64*d+56 := by positivity
  constructor
  · apply sub_pos.mp
    convert add_pos (mul_pos ht hm₁) (add_pos (mul_pos (sq_pos_of_pos ht) hm₂)
      (add_pos (mul_pos (pow_pos ht 3) hm₃) (show 0 < t^4*(16*H) by positivity))) using 1
    unfold den num
    rw [hd]
    ring
  · apply sub_pos.mp
    convert add_pos (mul_pos ht hp₁) (add_pos (mul_pos (sq_pos_of_pos ht) hp₂)
      (add_pos (mul_pos (pow_pos ht 3) hp₃) (show 0 < t^4*(16*H) by positivity))) using 1
    unfold den num
    rw [hd]
    ring

theorem lemma_seven :
    (∀ w : ℂ, h ≤ w.im → AnalyticAt ℂ third w ∧ |(third w).im| ≤ h ∧
      (|(third w).im| = h ↔ w = W)) ∧ third W = W := by
  obtain ⟨hu, _, _, _, hH, hh⟩ := constants_spec
  have hroot := (lemma_four.1 W).2 (Or.inr (Or.inl rfl))
  have hpos : 0 < h := by linarith
  have hbase : 3/4 ≤ h^2 := by nlinarith [sq_nonneg u]
  have hfixed : third W = W := by
    apply (div_eq_iff (third_den_ne W hh)).2
    linear_combination -hroot
  have heval := third_im W hh
  rw [hfixed] at heval
  change h * den u h = num u h at heval
  have hslope : 64*u*(u^2+h^2) = 8 := by rw [hH]; linarith only [show 64*u*(u^2+(3/4+3*u^2)) = 8*(32*u^3+6*u) by ring, hu]
  refine ⟨?_, hfixed⟩
  intro w hw
  have hden := den_pos w.re w.im (hh.trans_le hw)
  have hi := third_im w (hh.trans_le hw)
  have ha : AnalyticAt ℂ third w := by
    unfold third
    fun_prop (disch := exact third_den_ne _ (hh.trans_le hw))
  have hmarg : h * den w.re h - num w.re h =
        16*h*(w.re-u)^2*((w.re+u)^2+2*u^2+2*h^2) := by
    unfold den num at heval ⊢
    linear_combination heval + h*(w.re-u)*hslope
  have hplus : 0 < h * den w.re h + num w.re h := by
    have hfour : 9/16 ≤ h^4 := by nlinarith [sq_nonneg (h^2-3/4)]
    have hq : 0 < 16*(w.re^2+h^2)^2+16*w.re^2+8*w.re-1 := by
      nlinarith [sq_nonneg (4*w.re+1), sq_nonneg (w.re^2),
        mul_nonneg (sq_nonneg w.re) (sq_nonneg h)]
    convert mul_pos hpos hq using 1
    unfold den num
    ring
  have hm : 0 ≤ h * den w.re h - num w.re h := by rw [hmarg]; positivity
  rcases eq_or_lt_of_le hw with hb | hb
  · have hb' := hb.symm
    rw [hb'] at hden hi
    have hlow : -h < (third w).im := by
      apply (mul_lt_mul_iff_left₀ hden).mp
      linarith
    have hupp : (third w).im ≤ h := by
      apply (mul_le_mul_iff_left₀ hden).mp
      linarith
    refine ⟨ha, abs_le.mpr ⟨hlow.le, hupp⟩, ?_, ?_⟩
    · intro he
      have hx : (third w).im = h := (abs_eq hpos.le |>.mp he).resolve_right (by linarith)
      have hz : 16*h*(w.re-u)^2*((w.re+u)^2+2*u^2+2*h^2) = 0 := by
        rw [← hmarg, ← hi, hx]; ring
      have hfac : 0 < (w.re+u)^2+2*u^2+2*h^2 := by positivity
      rcases mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hfac.ne') with hbad | hsq
      · exfalso; exact (mul_pos (by norm_num) hpos).ne' hbad
      · exact Complex.ext (by change w.re = u; nlinarith) hb'
    · rintro rfl
      rw [hfixed]; exact abs_of_pos hpos
  · obtain ⟨hv₁,hv₂⟩ := vertical_bounds w.re h (w.im-h) hpos hbase (sub_pos.mpr hb)
    rw [add_sub_cancel] at hv₁ hv₂
    have hlt : |(third w).im| < h := by
      apply abs_lt.mpr
      constructor
      · apply (mul_lt_mul_iff_left₀ hden).mp
        linarith
      · apply (mul_lt_mul_iff_left₀ hden).mp
        linarith
    refine ⟨ha, hlt.le, iff_of_false hlt.ne ?_⟩
    rintro rfl
    exact lt_irrefl _ hb

end Turan
