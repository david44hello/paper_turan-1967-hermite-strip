-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.QuinticAngle
import Turan.QuinticFactorRoots
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

noncomputable section
open Polynomial
namespace Turan

private theorem endpoint_sub_ne (t : ℝ) (w : ℂ) (hh : 87/100 ≤ |w.im|) :
    (t : ℂ) - w ≠ 0 := by
  intro h
  rw [← sub_eq_zero.mp h] at hh
  norm_num at hh

/-- The endpoint quotient has positive real part, so its principal argument
is the arctangent in the definition of the signed angle. -/
private theorem qAngle_eq_arg (X s : ℝ) (w : ℂ)
    (hs : 1/2 < s) (hs' : s < 511/1000) (hh : 87/100 ≤ |w.im|) :
    qAngle X s w = (((↑(X+s) : ℂ) - w) / (↑(X-s) - w)).arg := by
  let u := (↑(X+s) : ℂ) - w
  let v := (↑(X-s) : ℂ) - w
  let D := (w.re-X)^2 + w.im^2 - s^2
  have hv : 0 < Complex.normSq v := Complex.normSq_pos.mpr (endpoint_sub_ne _ _ hh)
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [sq_abs w.im, sq_nonneg (w.re-X),
      mul_pos (show 0 < |w.im| - s by linarith) (show 0 < |w.im| + s by linarith)]
  have hre : (u/v).re = D / Complex.normSq v := by
    rw [Complex.div_re, ← add_div]
    congr 1
    simp [u, v, D, Complex.sub_re, Complex.sub_im]
    ring
  have him : (u/v).im = (2*s*w.im) / Complex.normSq v := by
    rw [Complex.div_im, ← sub_div]
    congr 1
    simp [u, v, Complex.sub_re, Complex.sub_im]
    ring
  change Real.arctan (2*s*w.im/D) = (u/v).arg
  apply Real.arctan_eq_of_tan_eq
  · rw [Complex.tan_arg, him, hre]
    field_simp [hv.ne', hD.ne']
  · apply abs_lt.mp
    exact Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (hre ▸ div_pos hD hv))

private theorem arg_product (f : Fin 5 → ℂ) (hf : ∀ i, f i ≠ 0) (t : Finset (Fin 5)) :
    (((∏ i ∈ t, f i).arg : ℝ) : Real.Angle) = ∑ i ∈ t, ((f i).arg : Real.Angle) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Complex.arg_mul_coe_angle (hf i) (Finset.prod_ne_zero_iff.mpr (fun j _ => hf j)), ih]

/-- Equal normalized values at endpoints on opposite sides of -1/2 force the
product of the endpoint quotients to be a negative real number. -/
private theorem endpoint_product (a b : ℂ) (hb : b ≠ 0) (L R : ℝ)
    (hl : L + 1/2 < 0) (hr : 0 < R + 1/2)
    (hnodes : ∀ j ∈ ({2,5} : Finset ℕ),
      (hermite j).eval (L : ℂ)/(2*(L : ℂ)+1) = (hermite j).eval (R : ℂ)/(2*(R : ℂ)+1))
    (z : Fin 5 → ℂ) (hh : ∀ i, 87/100 ≤ |(z i).im|)
    (hfac : family 2 5 a b = C (32*b) * ∏ i, (X - C (z i))) :
    ∏ i, (((R : ℂ)-z i) / ((L : ℂ)-z i)) = (↑((2*R+1)/(2*L+1)) : ℂ) := by
  have hL : 2*(L : ℂ)+1 ≠ 0 := by exact_mod_cast (show 2*L+1 ≠ 0 by linarith)
  have hR : 2*(R : ℂ)+1 ≠ 0 := by exact_mod_cast (show 2*R+1 ≠ 0 by linarith)
  have h₂ := (div_eq_div_iff hL hR).mp (hnodes 2 (by simp))
  have h₅ := (div_eq_div_iff hL hR).mp (hnodes 5 (by simp))
  have heq : (family 2 5 a b).eval (L : ℂ) * (2*(R : ℂ)+1) =
      (family 2 5 a b).eval (R : ℂ) * (2*(L : ℂ)+1) := by
    simp only [family, eval_add, eval_one, eval_mul, eval_ofNat, eval_X, eval_C]
    linear_combination a * h₂ + b * h₅
  simp only [hfac, eval_mul, eval_C, eval_prod, eval_sub, eval_X] at heq
  rw [Finset.prod_div_distrib]
  push_cast
  apply (div_eq_div_iff (Finset.prod_ne_zero_iff.mpr (fun i _ => endpoint_sub_ne L _ (hh i))) hL).mpr
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (32 : ℂ) ≠ 0) hb)
  linear_combination -heq

/-- The five roots with multiplicity, their first two power sums, and the
absolute lower bound for their signed angle sum at the equal-value nodes. -/
theorem quintic_root_data (a b : ℂ) (hb : b ≠ 0) (X s : ℝ)
    (hs : 1/2 < s) (hs' : s < 511/1000)
    (hleft : X-s+1/2 < 0) (hright : 0 < X+s+1/2)
    (hnodes : ∀ j ∈ ({2,5} : Finset ℕ),
      (hermite j).eval ((X-s : ℝ) : ℂ)/(2*((X-s : ℝ) : ℂ)+1) =
      (hermite j).eval ((X+s : ℝ) : ℂ)/(2*((X+s : ℝ) : ℂ)+1))
    (hno : ∀ z : ℂ, (family 2 5 a b).eval z = 0 → 87/100 ≤ |z.im|) :
    ∃ z : Fin 5 → ℂ, (∀ i, 87/100 ≤ |(z i).im|) ∧
      (∑ i, z i = 0) ∧ (∑ i, z i^2 = 10) ∧ Real.pi ≤ |∑ i, qAngle X s (z i)| := by
  classical
  obtain ⟨z, hfac, hsum, hsq⟩ := quintic_factorization a b hb
  have hh (i) : 87/100 ≤ |(z i).im| := by
    apply hno
    rw [hfac, eval_mul, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (sub_self (z i)), mul_zero]
  refine ⟨z, hh, hsum, hsq, ?_⟩
  let f (i : Fin 5) := ((↑(X+s) : ℂ)-z i) / (↑(X-s)-z i)
  have hf (i) : f i ≠ 0 := div_ne_zero (endpoint_sub_ne _ _ (hh i)) (endpoint_sub_ne _ _ (hh i))
  have hp := endpoint_product a b hb (X-s) (X+s) hleft hright hnodes z hh hfac
  have hneg : (2*(X+s)+1)/(2*(X-s)+1) < 0 :=
    div_neg_of_pos_of_neg (by linarith) (by linarith)
  have hangle : ((∑ i, qAngle X s (z i) : ℝ) : Real.Angle) = Real.pi := by
    change Real.Angle.coeHom (∑ i, qAngle X s (z i)) = _
    rw [map_sum]
    calc
      _ = ∑ i, ((f i).arg : Real.Angle) := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg ((↑) : ℝ → Real.Angle) (qAngle_eq_arg X s (z i) hs hs' (hh i))
      _ = ((∏ i, f i).arg : Real.Angle) := (arg_product f hf _).symm
      _ = _ := by rw [show ∏ i, f i = _ from hp, Complex.arg_ofReal_of_neg hneg]
  by_contra! hsmall
  have h := congrArg Real.Angle.toReal hangle
  rw [Real.Angle.toReal_pi, Real.Angle.toReal_coe_eq_self_iff.mpr
    ⟨(abs_lt.mp hsmall).1, (abs_lt.mp hsmall).2.le⟩] at h
  exact (abs_lt.mp hsmall).2.ne h

end Turan
