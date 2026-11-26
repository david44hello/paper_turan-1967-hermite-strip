module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.CubicRoots
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Polynomial
namespace Turan

theorem small34_cubic (a : ℂ) :
    ∃ z : ℂ, (family 3 4 a 0).eval z = 0 ∧ |z.im| < 5/7 := by
  by_cases ha : a = 0
  · subst a
    exact ⟨-1/2, by norm_num [family, eval_add, eval_mul], by norm_num⟩
  obtain ⟨x,y,v,hr,hf⟩ := cubic_shifted_factorization 0 a ha
  have hp : x*y*v = -5/8 := by
    have hc := congrArg (eval 0) hf
    norm_num [family, hermite, eval_comp, eval_mul, eval_add, eval_sub, nsmul_eq_mul] at hc
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp (show a*(x*y*v - -5/8) = 0 by linear_combination hc / 8)).resolve_left ha
  have hprod : ‖x‖*‖y‖*‖v‖ = 5/8 := by simpa [norm_mul, norm_div] using congrArg norm hp
  have hsum : x.im + y.im + v.im = 0 := by
    unfold rootRelation at hr
    have he : x+y+v = 3/2 := by linear_combination hr - 4*hp
    simpa using congrArg Complex.im he
  by_contra! hn
  have lower (w : ℂ) (hw : w=x ∨ w=y ∨ w=v) : 5/7 ≤ |w.im| := by
    have hz := (cubic_shifted_zero_iff 0 a x y v ha hf (w-1/2)).mpr (by simpa using hw)
    have hz' : (family 3 4 a 0).eval (w-1/2) = 0 := by simpa [family] using hz
    simpa using hn _ hz'
  have hx := lower x (.inl rfl)
  have hy := lower y (.inr (.inl rfl))
  have hv := lower v (.inr (.inr rfl))
  have bound (u w t : ℂ) (hu : 5/7 ≤ |u.im|) (hw : 5/7 ≤ |w.im|)
      (ht : ‖u‖*‖w‖*‖t‖ = 5/8) : |t.im| < 10/7 := by
    have huw := mul_le_mul (hu.trans (Complex.abs_im_le_norm u))
      (hw.trans (Complex.abs_im_le_norm w)) (by norm_num : (0:ℝ) ≤ 5/7) (norm_nonneg _)
    have he := mul_le_mul_of_nonneg_right huw (norm_nonneg t)
    linarith [Complex.abs_im_le_norm t]
  have xv := bound x y v hx hy hprod
  have yv := bound x v y hx hv (by linear_combination hprod)
  have vv := bound y v x hy hv (by linear_combination hprod)
  rw [le_abs] at hx hy hv
  rw [abs_lt] at xv yv vv
  rcases hx with h | h <;> rcases hy with j | j <;> rcases hv with k | k <;> linarith

end Turan
