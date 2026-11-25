-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Hermite
import Turan.Normalized
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Tactic

noncomputable section
open Polynomial Matrix
namespace Turan.Giroux

def scale (j : ℕ) : ℝ := Real.sqrt (2^j * (j.factorial : ℝ))
def gamma (j : ℕ) : ℝ := Real.sqrt (2*(j:ℝ))/2
def mode (j : ℕ) : Polynomial ℂ := C ((scale j : ℂ)⁻¹) * hermite j

theorem scale_pos (j : ℕ) : 0 < scale j := by
  have := Nat.factorial_pos j
  dsimp [scale]; positivity

theorem mode_eval (j : ℕ) (z : ℂ) : (mode j).eval z = psi j z := by
  simp [mode, scale, psi, div_eq_inv_mul]

private theorem scale_succ (j : ℕ) : scale (j+1) = 2*gamma (j+1)*scale j := by
  have ha : 2*gamma (j+1) = Real.sqrt (2*((j+1:ℕ):ℝ)) := by unfold gamma; ring
  rw [ha, scale, scale, ← Real.sqrt_mul (by positivity)]
  congr 1
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  ring

private theorem recur (j : ℕ) : X * mode j =
    C (gamma (j+1) : ℂ)*mode (j+1) + C (gamma j : ℂ)*mode (j-1) := by
  have hg (i : ℕ) : (gamma (i+1) : ℂ)^2 = ((i:ℂ)+1)/2 := by
    have h : gamma (i+1)^2 = ((i:ℝ)+1)/2 := by
      dsimp [gamma]; rw [div_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
    simpa only [Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one, Complex.ofReal_ofNat] using congrArg Complex.ofReal h
  have hs (i : ℕ) : (scale i : ℂ) ≠ 0 := by exact_mod_cast (scale_pos i).ne'
  have hf (i : ℕ) : (gamma (i+1) : ℂ) ≠ 0 := by
    exact_mod_cast (show gamma (i+1) ≠ 0 by dsimp [gamma]; positivity)
  apply Polynomial.funext
  intro z
  simp only [mode, eval_add, eval_mul, eval_X, eval_C]
  cases j with
  | zero => norm_num [hermite, gamma, scale, eval_mul]; field_simp
  | succ i =>
    simp only [Nat.add_one_sub_one]
    rw [show hermite (i+2) = 2*X*hermite (i+1) - (2*(i+1)) • hermite i from rfl]
    simp only [eval_sub, eval_mul, eval_X, eval_ofNat, nsmul_eq_mul, eval_add, eval_one, eval_natCast,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, scale_succ, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    field_simp [hs, hf]
    grind only [hg i]

/-- The two off-diagonals of the real symmetric Hermite Jacobi matrix. -/
def jacobi (m : ℕ) : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j =>
  (if i.val+1 = j.val then (gamma j.val : ℂ) else 0) +
  (if j.val+1 = i.val then (gamma i.val : ℂ) else 0)

theorem jacobi_hermitian (m : ℕ) : (jacobi m).IsHermitian := by
  ext i j
  by_cases h : i.val+1 = j.val <;> by_cases h' : j.val+1 = i.val <;>
    simp [jacobi, Matrix.conjTranspose_apply, h, h', add_comm]

/-- The rank-one perturbation changes only the last row. -/
def perturbed (k : ℕ) (d : Fin (k+1) → ℂ) : Matrix (Fin (k+1)) (Fin (k+1)) ℂ :=
  jacobi (k+1) - vecMulVec (Pi.single (Fin.last k) (gamma (k+1) : ℂ)) d

def combination (k : ℕ) (d : Fin (k+1) → ℂ) : Polynomial ℂ :=
  mode (k+1) + ∑ j, C (d j) * mode j.val

private theorem jacobi_row (k : ℕ) (i : Fin (k+1)) :
    (∑ j, C (jacobi (k+1) i j) * mode j.val) =
    (if i = Fin.last k then 0 else C (gamma (i.val+1) : ℂ)*mode (i.val+1)) +
      C (gamma i.val : ℂ)*mode (i.val-1) := by
  classical
  simp only [jacobi, of_apply, map_add, add_mul, Finset.sum_add_distrib]
  congr 1
  · by_cases hi : i = Fin.last k
    · subst i
      simp [show ∀ j : Fin (k+1), ¬(k+1 = j.val) by intro j; omega]
    · let t : Fin (k+1) := ⟨i.val+1, by have := i.isLt; have : i.val ≠ k := fun h => hi (Fin.ext h); omega⟩
      have he (j : Fin (k+1)) : i.val+1 = j.val ↔ j = t := by simp [Fin.ext_iff, t, eq_comm]
      simp [hi, he, apply_ite, ite_mul, t]
  · by_cases hi : i.val = 0
    · simp [hi, gamma]
    · let t : Fin (k+1) := ⟨i.val-1, by have := i.isLt; omega⟩
      have he (j : Fin (k+1)) : j.val+1 = i.val ↔ j = t := by
        rw [Fin.ext_iff]; dsimp [t]; omega
      simp [he, apply_ite, ite_mul, t]

/-- The first coordinate of the Jacobi recurrence is 1. Multiplying the
characteristic-matrix identity by its adjugate retains all root multiplicities. -/
theorem combination_dvd_charpoly (k : ℕ) (d : Fin (k+1) → ℂ) :
    combination k d ∣ (perturbed k d).charpoly := by
  classical
  let A := (perturbed k d).charmatrix
  let v (i : Fin (k+1)) := mode i.val
  let u (i : Fin (k+1)) : Polynomial ℂ := C ((Pi.single (Fin.last k) (gamma (k+1) : ℂ) : Fin (k+1) → ℂ) i)
  have hv : A *ᵥ v = combination k d • u := by
    ext1 i
    simp only [A, mulVec, dotProduct, charmatrix_apply, perturbed, Matrix.sub_apply,
      map_sub, sub_mul, Finset.sum_sub_distrib, vecMulVec_apply, map_mul,
      mul_assoc, ← Finset.mul_sum, Matrix.diagonal_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, v, jacobi_row]
    by_cases hi : i = Fin.last k
    · subst i
      simp [u, Pi.smul_apply, combination, recur k, Fin.last]
      ring
    · simp [hi, u, Pi.smul_apply, recur]
  have h := congrArg (fun f => (A.adjugate *ᵥ f) (0 : Fin (k+1))) hv
  rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec, mulVec_smul] at h
  simpa [A, v, mode, scale, hermite, Matrix.charpoly] using
    (show combination k d ∣ A.det * v 0 from ⟨_, h⟩)

end Turan.Giroux
