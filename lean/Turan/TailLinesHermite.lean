module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TailDefs
public import Turan.Hermite
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Polynomial
namespace Turan
namespace TailLines

private def E (p : Polynomial ℂ) : Polynomial ℂ :=
  C (1/2 : ℂ) * p.derivative.derivative - X * p.derivative

private theorem E_add (p q : Polynomial ℂ) : E (p+q) = E p + E q := by
  simp only [E, derivative_add]
  ring

private theorem E_C_mul (c : ℂ) (p : Polynomial ℂ) : E (C c * p) = C c * E p := by
  simp only [E, derivative_C_mul]
  ring

private theorem E_hermite (n : ℕ) : E (hermite n) = C (-(n:ℂ)) * hermite n := by
  have h := hermite_equation n
  simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] at h
  simp only [E, map_neg, map_natCast]
  have htwo : C (1/2 : ℂ) * 2 = (1 : Polynomial ℂ) := by
    simpa only [map_mul, map_ofNat, map_one] using
      congrArg (C : ℂ →+* Polynomial ℂ) (show (1/2 : ℂ)*2 = 1 by norm_num)
  rw [sub_eq_iff_eq_add.mp h]
  linear_combination (X * (hermite n).derivative - (n : Polynomial ℂ) * hermite n) * htwo

private theorem E_affine : E (1 + 2 * X) = C (-2 : ℂ) * X := by
  norm_num [E, derivative_add, derivative_mul, map_ofNat]
  ring

private theorem E_X : E X = -X := by simp [E]

private theorem E_squared (p : Polynomial ℂ) (z : ℂ) :
    (E (E p)).eval z =
      p.derivative.derivative.derivative.derivative.eval z / 4 -
      z * p.derivative.derivative.derivative.eval z +
      (z^2-1) * p.derivative.derivative.eval z + z * p.derivative.eval z := by
  simp only [E, derivative_sub, derivative_mul, derivative_X,
    derivative_C, derivative_add, zero_mul, one_mul, zero_add, eval_sub, eval_add,
    eval_mul, eval_C, eval_X]
  ring

private theorem iter_poly (p : Polynomial ℂ) (l : ℕ) :
    iteratedDeriv l (fun z => p.eval z) = fun z => ((derivative^[l]) p).eval z := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    exact funext fun z => (((derivative^[l]) p).hasDerivAt z).deriv

/-- The first two powers of the Hermite operator on the normalized family,
written both as derivative jets and as sums over its four modes. -/
theorem family_jets (n m : ℕ) (a b z : ℂ) :
    let d := fun l => iteratedDeriv l (normalizedFamily n m a b) z
    let u := a * psi n z
    let v := b * psi m z
    d 2 / 2 - z * d 1 = -2*z - n*u - m*v ∧
    d 4 / 4 - z*d 3 + (z^2-1)*d 2 + z*d 1 = 2*z + (n:ℂ)^2*u + (m:ℂ)^2*v := by
  let coeff := fun (j : ℕ) (c : ℂ) => c / (Real.sqrt (2 ^ j * (j.factorial : ℝ)) : ℂ)
  let P := 1 + 2*X + C (coeff n a) * hermite n + C (coeff m b) * hermite m
  have hF : normalizedFamily n m a b = fun w => P.eval w := by
    funext w
    simp only [P, coeff, normalizedFamily, psi, eval_add, eval_one, eval_mul, eval_C,
      eval_ofNat, eval_X]
    ring
  have hE : E P = C (-2:ℂ)*X + C (coeff n a)*(C (-(n:ℂ))*hermite n) +
      C (coeff m b)*(C (-(m:ℂ))*hermite m) := by
    unfold P
    rw [E_add, E_add, E_affine, E_C_mul, E_C_mul, E_hermite, E_hermite]
  have hEE := congrArg E hE
  simp only [E_add, E_C_mul, E_X, E_hermite] at hEE
  dsimp only
  simp only [hF, iter_poly]
  change P.derivative.derivative.eval z / 2 - z * P.derivative.eval z = _ ∧
    P.derivative.derivative.derivative.derivative.eval z / 4 -
      z * P.derivative.derivative.derivative.eval z +
      (z^2-1) * P.derivative.derivative.eval z + z * P.derivative.eval z = _
  constructor
  · have he := congrArg (fun p : Polynomial ℂ => p.eval z) hE
    simp only [E, eval_sub, eval_add, eval_mul, eval_C, eval_X] at he
    dsimp only [coeff, psi]
    linear_combination he
  · rw [← E_squared, hEE]
    simp only [eval_add, eval_mul, eval_C, eval_neg, eval_X, coeff, psi]
    ring

end TailLines
end Turan
