module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Degree
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Polynomial
namespace Turan.QuarticContacts

private theorem family_eval (a b z : ℂ) :
    (family 2 4 a b).eval z =
      16*b*z^4 + (4*a-48*b)*z^2 + 2*z + (1-2*a+12*b) := by
  norm_num [family, hermite, eval_add, eval_sub, eval_mul, eval_pow, eval_smul, nsmul_eq_mul]
  ring

/-- The family constraint is linear in the constant term of the residual quadratic. -/
def denom (s p : ℂ) : ℂ := 4*p+2+2*s

def numer (s p : ℂ) : ℂ := 2*s^2+2*s*p-2*p-3

theorem denom_ne (u v : ℂ) (hu : 4/5 < |u.im|) (hv : 4/5 < |v.im|) :
    denom (u+v) (u*v) ≠ 0 := by
  intro h
  have he : (u+1/2)*(v+1/2) = -1/4 := by
    unfold denom at h
    linear_combination h / 4
  have hnorm : ‖u+1/2‖*‖v+1/2‖ = 1/4 := by
    simpa [norm_mul, norm_div] using congrArg norm he
  have hbound (z : ℂ) : |z.im| ≤ ‖z+1/2‖ := by
    simpa using Complex.abs_im_le_norm (z+1/2)
  have hp := mul_lt_mul_of_pos_right (hu.trans_le (hbound u))
    (show 0 < ‖v+1/2‖ by linarith [hbound v])
  linarith [hbound v]

theorem root_data (a b u v r w : ℂ) (hb : b ≠ 0)
    (hroots : (family 2 4 a b).roots = {r,w,u,v}) :
    let s := u+v
    let p := u*v
    let q := r*w
    r+w = -s ∧ denom s p * q = numer s p ∧ s*(p-q) ≠ 0 := by
  let F := family 2 4 a b
  have hd : F.natDegree = 4 := by simp [F, family_degree 2 4 (by decide) (by decide), hb]
  have h₂ : hermite 2 = 4*X^2-2 := by norm_num [hermite, nsmul_eq_mul]; ring
  have h₄ : hermite 4 = 16*X^4-48*X^2+12 := by norm_num [hermite, nsmul_eq_mul]; ring
  have hl : F.leadingCoeff = 16*b := by
    rw [leadingCoeff, hd]
    norm_num [F, family, h₂, h₄, coeff_add, coeff_sub, coeff_C_mul, coeff_ofNat_mul,
      coeff_X_pow, coeff_X, coeff_one]
    ring
  let s := u+v
  let p := u*v
  let k := r+w
  let q := r*w
  have H (z : ℂ) : 16*b*(z^2-s*z+p)*(z^2-k*z+q) =
      16*b*z^4+(4*a-48*b)*z^2+2*z+(1-2*a+12*b) := by
    rw [← family_eval]
    change _ = F.eval z
    have he := (IsAlgClosed.splits F).eval_eq_prod_roots (x := z)
    rw [hl, show F.roots = {r,w,u,v} from hroots] at he
    rw [he]
    simp [s,p,k,q]
    ring
  have hn : 16*b ≠ 0 := mul_ne_zero (by norm_num) hb
  have hsum : 16*b*(s+k) = 0 := by
    linear_combination (2*(H 1 - H (-1)) - (H 2 - H (-2))) / 12
  have hk : k = -s := by linear_combination (mul_eq_zero.mp hsum).resolve_left hn
  simp only [hk] at H
  have hc : 16*b*(denom s p*q - numer s p) = 0 := by
    unfold denom numer
    linear_combination 4*H 0 + (H 1 + H (-1) - 2*H 0) - (H 1 - H (-1))
  have hlin : 16*b*(s*(p-q)) = 2 := by linear_combination (H 1-H (-1))/2
  refine ⟨hk, sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left hn), ?_⟩
  change s*(p-q) ≠ 0
  intro h
  simp [h] at hlin

/-- Recover actual coefficients of the family for the two monic quadratic factors. -/
theorem realize (u v q : ℂ) (hc : denom (u+v) (u*v)*q = numer (u+v) (u*v))
    (hl : (u+v)*(u*v-q) ≠ 0) :
    ∃ a b : ℂ, b ≠ 0 ∧ ∀ z : ℂ,
      (family 2 4 a b).eval z = 16*b*(z-u)*(z-v)*(z^2+(u+v)*z+q) := by
  let s := u+v
  let p := u*v
  let b := (8*(s*(p-q)))⁻¹
  have hb : 8*(s*(p-q)) ≠ 0 := mul_ne_zero (by norm_num) hl
  have hscale : 8*(s*(p-q))*b = 1 := mul_inv_cancel₀ hb
  refine ⟨4*b*(p+q-s^2+3), b, inv_ne_zero hb, ?_⟩
  intro z
  rw [family_eval, show 16*b*(z-u)*(z-v) = 16*b*(z^2-s*z+p) by dsimp [s,p]; ring]
  change _ = 16*b*(z^2-s*z+p)*(z^2+s*z+q)
  change denom s p*q = numer s p at hc
  unfold denom numer at hc
  linear_combination -(2*z+1)*hscale - 4*b*hc

end Turan.QuarticContacts
