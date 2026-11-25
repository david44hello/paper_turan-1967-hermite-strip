-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Generating
import Turan.Hermite
import Turan.MehlerJetsSpatial
import Turan.MehlerJetsGeometry
import Turan.MehlerJetsRoots
import Turan.MehlerJetsG1

noncomputable section
open Polynomial
open scoped ComplexConjugate
namespace Turan.MehlerJets

theorem diagonal_substitution (z : ℂ) (r : ℝ) :
    z^2 + (conj z)^2 = ((2*(z.re^2-z.im^2) : ℝ) : ℂ) ∧
    2*z*conj z*(r:ℂ) - (z^2+(conj z)^2)*(r:ℂ)^2 =
      ((2*r*(z.re^2+z.im^2)-2*r^2*(z.re^2-z.im^2) : ℝ) : ℂ) := by
  have h : z^2 + (conj z)^2 = ((2*(z.re^2-z.im^2) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;> ring
  refine ⟨h, ?_⟩
  rw [h, mul_assoc 2 z, Complex.mul_conj, Complex.normSq_apply]
  push_cast
  ring

def diagonalExponent (z : ℂ) (r : ℝ) : ℂ :=
  (2*z*conj z*(r:ℂ) - (z^2+(conj z)^2)*(r:ℂ)^2) / (1-(r:ℂ)^2)

theorem diagonal_exponent (z : ℂ) (r : ℝ) (hr : 0 ≤ r) (hr' : r < 1) :
    diagonalExponent z r =
      ((2*r/(1+r)*z.re^2 + 2*r/(1-r)*z.im^2 : ℝ) : ℂ) ∧
    diagonalExponent z (1/5) = ((z.re^2/3 + z.im^2/2 : ℝ) : ℂ) := by
  have general (s : ℝ) (hs : 0 ≤ s) (hs' : s < 1) :
      diagonalExponent z s = ((2*s/(1+s)*z.re^2 + 2*s/(1-s)*z.im^2 : ℝ) : ℂ) := by
    rw [diagonalExponent, (diagonal_substitution z s).2]
    have hden : 0 < 1-s^2 := sub_pos.mpr (pow_lt_one₀ hs hs' (by decide))
    rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div]
    congr 1
    field_simp [hden.ne', (sub_pos.mpr hs').ne', (by linarith : (1+s) ≠ 0)]
    ring
  refine ⟨general r hr hr', ?_⟩
  rw [general _ (by norm_num) (by norm_num)]
  congr 1
  ring

theorem mehler_diagonal_extraction (z : ℂ) (n : ℕ) :
    let a := fun k : ℕ => (1/5 : ℝ)^k * ‖psi k z‖^2
    let S := (Real.sqrt (1-1/25 : ℝ))⁻¹ * Real.exp (z.re^2/3 + z.im^2/2)
    (∀ k, (1/5 : ℂ)^k * psi k z * psi k (conj z) = (a k : ℂ)) ∧
    (∀ k, 0 ≤ a k) ∧ HasSum a S ∧ a n ≤ S := by
  intro a S
  have term (k : ℕ) : (1/5 : ℂ)^k * psi k z * psi k (conj z) = (a k : ℂ) := by
    have hconj : psi k (conj z) = conj (psi k z) := by
      simp [psi, (hermite_symmetry k z).1]
    rw [hconj, mul_assoc, Complex.mul_conj, ← Complex.sq_norm]
    simp [a]
  have hk := mehler_kernel (1/5) (by norm_num) (by norm_num) z (conj z)
  have hS : HasSum a S := by
    apply Complex.hasSum_ofReal.mp
    convert hk using 1
    · funext k
      simpa using (term k).symm
    · have he := (diagonal_exponent z 0 (by norm_num) (by norm_num)).2
      dsimp [diagonalExponent] at he
      dsimp [S]
      push_cast at he ⊢
      rw [he]
      norm_num
  have hpos (k : ℕ) : 0 ≤ a k := by dsimp [a]; positivity
  exact ⟨term, hpos, hS, hS.summable.le_tsum n (fun i _ => hpos i) |>.trans_eq hS.tsum_eq⟩

end Turan.MehlerJets
