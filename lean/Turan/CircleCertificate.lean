module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.CircleBasic
public import Turan.CircleWeighted
public import Turan.Giroux

@[expose] public section

noncomputable section
open Polynomial
namespace Turan

theorem circle_certificate_gap (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m)
    (check : CircleCertificate n m) (a b : ℂ) :
    ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| < 87/100 := by
  let A := a / (128:ℂ)^n
  let B := b / (128:ℂ)^m
  have repr (z : ℂ) : scaledFamily n m A B z = (family n m a b).eval z := by
    simp [scaledFamily, scaledMode, family, eval_add, eval_mul, A, B, div_eq_mul_inv, mul_assoc]
  by_contra! outside
  have hs : emptyStrip (scaledFamily n m A B) (87/100) :=
    fun z hz hzero => hz.not_ge (outside z ((repr z).symm.trans hzero))
  let sign : ℝ := if 0 ≤ (A*star B).re then 1 else -1
  have hsign : sign = -1 ∨ sign = 1 := by dsimp [sign]; split <;> simp
  have hphase : 0 ≤ sign*(A*star B).re := by
    dsimp only [sign]
    split <;> rename_i hx
    · simpa only [one_mul] using hx
    · simpa only [neg_one_mul, neg_nonneg] using le_of_not_ge hx
  obtain ⟨rows, hv, hbad⟩ := check sign (by rcases hsign with h | h <;> simp [h])
  apply hbad ‖A‖ ‖B‖ (norm_nonneg _) (norm_nonneg _)
  intro w hw
  cases htest : w.test with
  | weighted => exact circle_weighted_cut w n m A B sign hs hphase hsign (hv w hw) htest
  | giroux => exact circle_giroux_cut w n m hn hnm A B hs htest
  | _ => exact circle_basic_cut w n m A B sign hs hphase hsign (hv w hw) (by simp [htest])

end Turan
