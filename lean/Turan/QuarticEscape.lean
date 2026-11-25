-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Degree
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace Turan

/-- On the complement of the open half-strip, the squared modulus of
z²-1/2 is at least 1/2. Its real part at equality is exactly -1/2. -/
private theorem shifted_square_boundary (z : ℂ) (hz : 1/2 ≤ |z.im|) :
    1/2 ≤ Complex.normSq (z^2-1/2) ∧
    (Complex.normSq (z^2-1/2) = 1/2 → (z^2-1/2).re = -1/2) := by
  have hsq : 1/4 ≤ z.im^2 := by nlinarith [sq_abs z.im, sq_le_sq' (by linarith [abs_nonneg z.im]) hz]
  have hid : Complex.normSq (z^2-1/2) = (z.re^2+z.im^2-1/2)^2 + 2*z.im^2 := by
    norm_num [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,pow_two,Complex.mul_re,Complex.mul_im]
    ring
  rw [hid]
  constructor
  · nlinarith [sq_nonneg (z.re^2+z.im^2-1/2)]
  · intro he
    have hzero : (z.re^2+z.im^2-1/2)^2 = 0 := by
      nlinarith only [sq_nonneg (z.re^2+z.im^2-1/2),hsq,he]
    have hc : z.re^2+z.im^2-1/2 = 0 := by simpa using hzero
    norm_num [Complex.sub_re,pow_two,Complex.mul_re]
    nlinarith only [he,hzero,hc]

theorem quartic_homogeneous_small (a b : ℂ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ z : ℂ, a*(hermite 2).eval z+b*(hermite 4).eval z=0 ∧ |z.im|<1/2 := by
  by_cases hb : b=0
  · refine ⟨((Real.sqrt 2 / 2 : ℝ):ℂ), ?_, by norm_num⟩
    norm_num [hb,hermite,eval_mul,nsmul_eq_mul]
    push_cast
    have h : (Real.sqrt 2 : ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    right
    linear_combination h
  let p : Polynomial ℂ := C (16*b)*X^2+C (4*a-32*b)*X+C (-8*b)
  have hl : 16*b ≠ 0 := mul_ne_zero (by norm_num) hb
  have hd : p.roots.card = 2 :=
    (IsAlgClosed.splits p).natDegree_eq_card_roots.symm.trans (natDegree_quadratic hl)
  obtain ⟨u,v,huv⟩ := Multiset.card_eq_two.mp hd
  have hfac := (IsAlgClosed.splits p).eq_prod_roots
  rw [show p.leadingCoeff=16*b from leadingCoeff_quadratic hl,huv] at hfac
  have hfac' : p=C (16*b)*((X-C u)*(X-C v)) := by simpa using hfac
  have hprod : u*v = -1/2 := by
    have he := congrArg (eval 0) hfac'
    simp [p,eval_add,eval_mul,eval_pow,eval_sub] at he
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show (16*b)*(u*v- -1/2)=0 by linear_combination -he)).resolve_left hl
  have hroot (x : ℂ) (hx : x=u ∨ x=v) : ∃ z : ℂ, z^2-1/2=x ∧
      a*(hermite 2).eval z+b*(hermite 4).eval z=0 := by
    obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (x+1/2) (by decide : 0<2)
    have hz' : z^2-1/2=x := by linear_combination hz
    refine ⟨z,hz',?_⟩
    have he : p.eval (z^2-1/2)=0 := by rw [hz',hfac']; rcases hx with rfl|rfl <;> simp [eval_sub,eval_mul]
    norm_num [p,eval_add,eval_sub,eval_pow,eval_mul] at he
    norm_num [hermite,nsmul_eq_mul,eval_sub,eval_mul]
    linear_combination he
  obtain ⟨z,hz,hez⟩ := hroot u (Or.inl rfl)
  obtain ⟨w,hw,hew⟩ := hroot v (Or.inr rfl)
  by_contra! hall
  obtain ⟨hzu,hezu⟩ := shifted_square_boundary z (hall z hez)
  obtain ⟨hwv,hewv⟩ := shifted_square_boundary w (hall w hew)
  rw [hz] at hzu hezu
  rw [hw] at hwv hewv
  have hs := congrArg Complex.normSq hprod
  norm_num [map_mul] at hs
  have hu : Complex.normSq u=1/2 := by
    nlinarith only [hs,hzu,hwv,mul_nonneg (sub_nonneg.mpr hzu) (sub_nonneg.mpr hwv)]
  have hv : Complex.normSq v=1/2 := by rw [hu] at hs; linarith only [hs]
  have hconj : v = -starRingEnd ℂ u := by
    apply mul_left_cancel₀ (show u≠0 by intro he; simp [he] at hu)
    rw [hprod,mul_neg,Complex.mul_conj,hu]
    norm_num
  have here := congrArg Complex.re hconj
  simp only [Complex.neg_re,Complex.conj_re] at here
  linarith only [hezu hu,hewv hv,here]

end Turan
