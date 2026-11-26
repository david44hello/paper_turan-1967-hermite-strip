module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Normalized
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Polynomial
namespace Turan.Generating

def D (n : ℕ) : ℂ := 2^n * n.factorial
def term (z w : ℂ) (n : ℕ) : ℂ := (hermite n).eval z * (hermite n).eval w / D n

private theorem d_ne (n : ℕ) : D n ≠ 0 := by
  unfold D; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero n)

private theorem d_step (n : ℕ) : D (n+1) = 2*((n:ℂ)+1)*D n := by
  simp [D, pow_succ, Nat.factorial_succ]; ring

theorem term_psi (z w : ℂ) (n : ℕ) : term z w n = psi n z * psi n w := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 2^n*(n.factorial:ℝ))
  have hc : (Real.sqrt (2^n*(n.factorial:ℝ)) : ℂ)^2 = D n := by unfold D; exact_mod_cast hs
  rw [psi, psi, div_mul_div_comm, ← sq, hc]; rfl

private theorem hstep (n : ℕ) (z : ℂ) :
    (hermite (n+2)).eval z = 2*z*(hermite (n+1)).eval z - 2*((n:ℂ)+1)*(hermite n).eval z := by
  rw [hermite, eval_sub, eval_mul, eval_mul, eval_X, eval_ofNat, eval_smul, nsmul_eq_mul]
  push_cast
  ring

theorem term_init (z w : ℂ) :
    term z w 0 = 1 ∧ term z w 1 = 2*z*w ∧
    2*term z w 2 = (2*z*w)*term z w 1 + (1-2*(z^2+w^2))*term z w 0 ∧
    3*term z w 3 = (2*z*w)*term z w 2 + (3-2*(z^2+w^2))*term z w 1 + (2*z*w)*term z w 0 := by
  norm_num [term, D, hermite, eval_mul, eval_sub, eval_smul, nsmul_eq_mul, Nat.factorial]
  (repeat' constructor) <;> ring

/-- The four-step recurrence for products of equal-degree Hermite values.
Multiplication by the last denominator clears all factorials before expansion. -/
theorem term_recurrence (z w : ℂ) (n : ℕ) :
    ((n:ℂ)+4)*term z w (n+4) = (2*z*w)*term z w (n+3) +
      (1-2*(z^2+w^2)+2*((n:ℂ)+2))*term z w (n+2) +
      (2*z*w)*term z w (n+1) - ((n:ℂ)+1)*term z w n := by
  have cancel (i : ℕ) : term z w i * D i = (hermite i).eval z * (hermite i).eval w :=
    div_mul_cancel₀ _ (d_ne i)
  let step (i : ℕ) : ℂ := 2*((i:ℂ)+1)
  have h (i : ℕ) : D (i+1) = D i * step i := (d_step i).trans (mul_comm ..)
  apply mul_right_cancel₀ (d_ne (n+4))
  simp only [add_mul, sub_mul, mul_assoc]
  rw [cancel, h (n+3)]
  simp only [← mul_assoc (term z w (n+3)), cancel]
  rw [h (n+2)]
  simp only [← mul_assoc (term z w (n+2)), cancel]
  rw [h (n+1)]
  simp only [← mul_assoc (term z w (n+1)), cancel]
  rw [h n]
  simp only [← mul_assoc (term z w n), cancel]
  simp only [show n+4 = (n+2)+2 by omega, hstep (n+2), hstep (n+1), hstep n, step,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  ring

end Turan.Generating
