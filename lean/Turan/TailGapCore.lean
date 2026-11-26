module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TailDefs
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Polynomial
namespace Turan

private theorem mode_small (n m : ℕ) (hnm : n < m) (a b : ℂ) (j : ℕ) (hj : 0 < j)
    (hbound : ‖modeQuotient n m j a b (-1/2)‖ ≤ 25000*(m:ℝ)^2/((j:ℝ)*(m-n:ℝ))*nodeProduct j)
    (hnodes : psi j (-1/2) = 0 ∨
      -Real.log (nodeProduct j) > (608/1000)*Real.sqrt (2*(j:ℝ)-1125/100) - 315/1000)
    (hcompare : Real.log (50000*(m:ℝ)^2 / ((j:ℝ)*(m-n:ℝ))) <
      (608/1000)*Real.sqrt (2*(j:ℝ)-1125/100) - 315/1000) :
    ‖modeQuotient n m j a b (-1/2)‖ < 1/2 := by
  rcases hnodes with hz | hlog
  · unfold modeQuotient
    rw [hz,mul_zero,zero_div,norm_zero]; norm_num
  let D := (j:ℝ)*((m:ℝ)-(n:ℝ))
  have hdiff : (0:ℝ) < (m:ℝ)-(n:ℝ) := sub_pos.mpr (by exact_mod_cast hnm)
  have hD : 0 < D := mul_pos (by exact_mod_cast hj) hdiff
  have hm : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  let R := 50000*(m:ℝ)^2 / D
  have hR : 0 < R := by dsimp [R]; positivity
  by_cases hn : nodeProduct j ≤ 0
  · have hn' := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 25000*(m:ℝ)^2/D by positivity) hn
    change ‖_‖ ≤ 25000*(m:ℝ)^2/D * _ at hbound
    linarith
  have hpn : 0 < nodeProduct j := lt_of_not_ge hn
  have hl : Real.log R + Real.log (nodeProduct j) < 0 := by dsimp [R,D]; linarith
  rw [← Real.log_mul hR.ne' hpn.ne'] at hl
  have hprod := (Real.log_neg_iff (mul_pos hR hpn)).mp hl
  dsimp [R,D] at hprod
  apply hbound.trans_lt
  convert div_lt_div_of_pos_right hprod (by norm_num : (0:ℝ)<2) using 1
  ring

def scaleCoeff (j : ℕ) (a : ℂ) : ℂ := a*(Real.sqrt (2^j*(j.factorial:ℝ)):ℂ)

theorem rescale_family (n m : ℕ) (a b z : ℂ) :
    normalizedFamily n m (scaleCoeff n a) (scaleCoeff m b) z = (family n m a b).eval z := by
  have hs (j : ℕ) : (Real.sqrt (2^j*(j.factorial:ℝ)):ℂ) ≠ 0 := by
    have h := Nat.factorial_pos j
    exact_mod_cast (show Real.sqrt (2^j*(j.factorial:ℝ)) ≠ 0 by positivity)
  simp only [normalizedFamily,scaleCoeff,psi,family,eval_add,eval_mul,eval_C,eval_X,eval_ofNat,eval_one]
  have cancel (c t v : ℂ) (ht : t ≠ 0) : (c*t)*(v/t) = c*v := by field_simp
  rw [cancel _ _ _ (hs n),cancel _ _ _ (hs m)]

theorem upper_index_gap_of_mode_bounds (n m : ℕ) (hm : 450 ≤ m) (hhalf : m ≤ 2*n) (hnm : n < m)
    (a b : ℂ)
    (h16 : ∀ A B : ℂ, emptyStrip (normalizedFamily n m A B) (87/100) →
      ∀ j : ℕ, j=n ∨ j=m → ‖modeQuotient n m j A B (-1/2)‖ ≤ 25000*(m:ℝ)^2/((j:ℝ)*(m-n:ℝ))*nodeProduct j)
    (h17 : ∀ j : ℕ, 225 ≤ j → psi j (-1/2)=0 ∨
      -Real.log (nodeProduct j) > (608/1000)*Real.sqrt (2*(j:ℝ)-1125/100)-315/1000)
    (hnum : ∀ j : ℕ, j=n ∨ j=m → Real.log (50000*(m:ℝ)^2/((j:ℝ)*(m-n:ℝ))) <
      (608/1000)*Real.sqrt (2*(j:ℝ)-1125/100)-315/1000) :
    ∃ z : ℂ, (family n m a b).eval z=0 ∧ |z.im|<87/100 := by
  by_contra! hno
  let A := scaleCoeff n a
  let B := scaleCoeff m b
  have hempty : emptyStrip (normalizedFamily n m A B) (87/100) := by
    intro z hz
    rw [rescale_family]
    intro hroot
    exact hz.not_ge (hno z hroot)
  have hsmall (j : ℕ) (hj : j=n ∨ j=m) : ‖modeQuotient n m j A B (-1/2)‖ < 1/2 := by
    have hj₀ : 225 ≤ j := by rcases hj with rfl|rfl <;> omega
    exact mode_small n m hnm A B j (by omega) (h16 A B hempty j hj) (h17 j hj₀) (hnum j hj)
  have hF := hempty (-1/2) (by norm_num)
  have hsum : modeQuotient n m n A B (-1/2) + modeQuotient n m m A B (-1/2) = 1 := by
    simp only [modeQuotient, ite_true, ite_eq_right hnm.ne', ← add_div]
    apply (div_eq_iff hF).2
    unfold normalizedFamily
    ring
  have htriangle := norm_add_le (modeQuotient n m n A B (-1/2)) (modeQuotient n m m A B (-1/2))
  rw [hsum,norm_one] at htriangle
  linarith [hsmall n (Or.inl rfl),hsmall m (Or.inr rfl)]

end Turan
