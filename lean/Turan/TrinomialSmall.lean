module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.CubicRoots
public import Turan.TrinomialDefs
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Polynomial
namespace Turan

private theorem prod_lower (x y v : ℂ) (X Y V : ℝ) (hx : X ≤ ‖x‖) (hy : Y ≤ ‖y‖)
    (hv : V ≤ ‖v‖) (hx₀ : 0 ≤ X) (hy₀ : 0 ≤ Y) :
    X*Y*V ≤ ‖x‖*‖y‖*‖v‖ :=
  mul_le_mul_of_nonneg_left hv (mul_nonneg hx₀ hy₀) |>.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul hx hy hy₀ (norm_nonneg _)) (norm_nonneg _))

private theorem cubic_trinomial (b : ℂ) (hb : b ≠ 0) :
    ∃ c : ℂ, (family 2 3 0 b).eval c = 0 ∧ |c.re| ≤ 2 ∧ |c.im| < 76/100 := by
  obtain ⟨x,y,v,hr,hf⟩ := cubic_shifted_factorization 0 b hb
  have hscale : x*y*v = -5/8 := by
    have hconst := congrArg (eval 0) hf
    norm_num [family, hermite, eval_comp, eval_mul, eval_add, eval_sub, nsmul_eq_mul] at hconst
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show b*(x*y*v - -5/8) = 0 by linear_combination hconst / 8)).resolve_left hb
  have habs : ‖x‖*‖y‖*‖v‖ = 5/8 := by simpa [norm_mul, norm_div] using congrArg norm hscale
  have hsum : x.im + y.im + v.im = 0 := by
    unfold rootRelation at hr
    have hc : x+y+v = 3/2 := by
      linear_combination hr - 4*hscale
    simpa using congrArg Complex.im hc
  by_contra! hfail
  have witness (w : ℂ) (hw : w=x ∨ w=y ∨ w=v) :
      |(w-1/2).re| ≤ 2 → 76/100 ≤ |w.im| := by
    have hz := (cubic_shifted_zero_iff 0 b x y v hb hf (w-1/2)).mpr (by simpa using hw)
    simpa using hfail _ hz
  have lower (w : ℂ) (hw : w=x ∨ w=y ∨ w=v) :
      76/100 ≤ ‖w‖ ∧ (|(w-1/2).re| > 2 → 3/2 ≤ ‖w‖) := by
    have hre := Complex.abs_re_le_norm w
    have him := Complex.abs_im_le_norm w
    have ht : |(w-1/2).re| ≤ ‖w‖ + 1/2 := by
      simpa [Complex.sub_re] using (abs_sub w.re (1/2)).trans (by linarith : |w.re| + |1/2| ≤ ‖w‖+1/2)
    refine ⟨?_, fun _ => by linarith⟩
    by_cases h : |(w-1/2).re| ≤ 2
    · exact (witness w hw h).trans him
    · linarith
  have hx := lower x (.inl rfl)
  have hy := lower y (.inr (.inl rfl))
  have hv := lower v (.inr (.inr rfl))
  have upper : ‖x‖ < 3/2 ∧ ‖y‖ < 3/2 ∧ ‖v‖ < 3/2 := by
    refine ⟨?_, ?_, ?_⟩ <;> by_contra! h
    · linarith [prod_lower _ _ _ _ _ _ h hy.1 hv.1 (by norm_num) (by norm_num)]
    · linarith [prod_lower _ _ _ _ _ _ hx.1 h hv.1 (by norm_num) (by norm_num)]
    · linarith [prod_lower _ _ _ _ _ _ hx.1 hy.1 h (by norm_num) (by norm_num)]
  have xi := witness x (.inl rfl) (le_of_not_gt (fun h => upper.1.not_ge (hx.2 h)))
  have yi := witness y (.inr (.inl rfl)) (le_of_not_gt (fun h => upper.2.1.not_ge (hy.2 h)))
  have vi := witness v (.inr (.inr rfl)) (le_of_not_gt (fun h => upper.2.2.not_ge (hv.2 h)))
  have xb := (Complex.abs_im_le_norm x).trans_lt upper.1
  have yb := (Complex.abs_im_le_norm y).trans_lt upper.2.1
  have vb := (Complex.abs_im_le_norm v).trans_lt upper.2.2
  rw [le_abs] at xi yi vi
  rw [abs_lt] at xb yb vb
  rcases xi with h | h <;> rcases yi with j | j <;> rcases vi with k | k <;> linarith

theorem trinomial_small (n : ℕ) (hn : n = 2 ∨ n = 3) (a : ℂ) :
    ∃ c : ℂ, 1 + 2*c + a*psi n c = 0 ∧ |c.re| ≤ 2 ∧ |c.im| < 76/100 := by
  let b := a / (Real.sqrt (2^n * (n.factorial:ℝ)) : ℂ)
  have heq (c : ℂ) : 1+2*c+a*psi n c = 1+2*c+b*(hermite n).eval c := by
    simp only [psi, b, div_eq_mul_inv]
    ring
  rcases hn with rfl | rfl
  · obtain ⟨c, hzero, hc⟩ := quadratic_half_disk b
    have hre := (Complex.abs_re_le_norm (c+1/2)).trans hc
    have him := (Complex.abs_im_le_norm (c+1/2)).trans hc
    simp [Complex.add_re, abs_le] at hre
    simp at him
    refine ⟨c, ?_, abs_le.mpr ⟨by linarith, by linarith⟩, by linarith⟩
    simpa [heq, family, eval_add, eval_mul] using hzero
  · by_cases hb : b = 0
    · exact ⟨-1/2, by rw [heq, hb]; ring, by norm_num, by norm_num⟩
    obtain ⟨c, hzero, hre, him⟩ := cubic_trinomial b hb
    exact ⟨c, by simpa [heq, family, eval_add, eval_mul] using hzero, hre, him⟩

end Turan
