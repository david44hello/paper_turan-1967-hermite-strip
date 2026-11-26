module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TransferDisks

@[expose] public section

noncomputable section
open Polynomial
open scoped ComplexConjugate
namespace Turan

private theorem even_hermite_origin (j : ℕ) :
    ∃ v : ℝ, v ≠ 0 ∧ (hermite (2*j)).eval 0 = (v : ℂ) := by
  induction j with
  | zero => exact ⟨1, one_ne_zero, by simp [hermite]⟩
  | succ j ih =>
    obtain ⟨v, hv, he⟩ := ih
    let c : ℕ := 2*(2*j+1)
    have hc : (c : ℝ) ≠ 0 := by dsimp [c]; positivity
    refine ⟨-((c : ℝ)*v), neg_ne_zero.mpr (mul_ne_zero hc hv), ?_⟩
    rw [Nat.mul_succ, hermite, eval_sub, eval_mul, eval_mul, eval_X, eval_smul, he]
    simp [c, nsmul_eq_mul]

/-- The certificate uses value one for even modes and derivative two for odd modes. -/
theorem transferMode_eq_real_mul (n : ℕ) :
    ∃ s : ℝ, s ≠ 0 ∧ transferMode n = C (s : ℂ) * hermite n := by
  by_cases he : Even n
  · obtain ⟨j, rfl⟩ := even_iff_two_dvd.mp he
    obtain ⟨v, hv, hval⟩ := even_hermite_origin j
    exact ⟨v⁻¹, inv_ne_zero hv, by simp [transferMode, he, hval]⟩
  · obtain ⟨j, rfl⟩ := Nat.not_even_iff_odd.mp he
    obtain ⟨v, hv, hval⟩ := even_hermite_origin j
    let c : ℕ := 2*(2*j+1)
    have hc : (c : ℝ) ≠ 0 := by dsimp [c]; positivity
    refine ⟨2/((c : ℝ)*v), div_ne_zero (by norm_num) (mul_ne_zero hc hv), ?_⟩
    simp [transferMode, he, hermite_derivative, nsmul_eq_mul, hval, c]

private theorem transfer_pencil_unit (n m : ℕ) (check : TransferCertificate n m)
    (swap : Bool) (θ : ℂ) (hθ : ‖θ‖ ≤ 1) (b : ℂ) :
    ∃ z : ℂ, (transferPencil n swap θ).eval z + b*(hermite m).eval z = 0 ∧ |z.im| < 87/100 := by
  by_cases him : 0 ≤ θ.im
  · exact transfer_pencil_upper n m check swap θ hθ him b
  obtain ⟨s, _, hs⟩ := transferMode_eq_real_mul n
  obtain ⟨z, hz, hy⟩ := transfer_pencil_upper n m check swap (conj θ)
    (by simpa using hθ) (by simpa using le_of_not_ge him) (conj b)
  refine ⟨conj z, ?_, by simpa using hy⟩
  have h := congrArg (fun v : ℂ => conj v) hz
  cases swap <;> simpa [transferPencil, hs, eval_mul, map_ofNat,
    (hermite_symmetry n z).1, (hermite_symmetry m z).1] using h

-- The paired-circle certificate itself supplies the positive-degree pivot
-- and the bracketed high-mode zero for the indices in the reviewed statement.
set_option linter.unusedVariables false in
theorem transfer_certificate_gap (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m)
    (check : TransferCertificate n m) (a b : ℂ) :
    ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| < 87/100 := by
  obtain ⟨s, hs0, hs⟩ := transferMode_eq_real_mul n
  let θ := a/(s : ℂ)
  have ha : θ*(s : ℂ) = a := div_mul_cancel₀ a (Complex.ofReal_ne_zero.mpr hs0)
  have hroot : ∃ z : ℂ, (transferPencil n false θ).eval z + b*(hermite m).eval z = 0 ∧
      |z.im| < 87/100 := by
    by_cases hθ : ‖θ‖ ≤ 1
    · exact transfer_pencil_unit n m check false θ hθ b
    have hne : θ ≠ 0 := fun h => hθ (by simp [h])
    have hinv : ‖θ⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ (le_of_not_ge hθ)
    obtain ⟨z, hz, hy⟩ := transfer_pencil_unit n m check true θ⁻¹ hinv (b/θ)
    have hswap : transferPencil n false θ = C θ * transferPencil n true θ⁻¹ := by
      change 1+2*X+C θ*transferMode n = C θ * (transferMode n + C θ⁻¹*(1+2*X))
      rw [mul_add, ← mul_assoc (C θ) (C θ⁻¹), ← C_mul, mul_inv_cancel₀ hne,
        map_one, one_mul, add_comm]
    refine ⟨z, ?_, hy⟩
    calc
      _ = θ*((transferPencil n true θ⁻¹).eval z + (b/θ)*(hermite m).eval z) := by
        rw [hswap, eval_mul, eval_C, mul_add, ← mul_assoc θ (b/θ)]
        field_simp
      _ = 0 := by rw [hz, mul_zero]
  obtain ⟨z, hz, hy⟩ := hroot
  refine ⟨z, ?_, hy⟩
  have hpoly : family n m a b = transferPencil n false θ + C b * hermite m := by
    simp only [family, transferPencil, Bool.false_eq_true, ite_false, hs, ← mul_assoc, ← C_mul, ha]
  simpa only [hpoly, eval_add, eval_mul, eval_C] using hz

end Turan
