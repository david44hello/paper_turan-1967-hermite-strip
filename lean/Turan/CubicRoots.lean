module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs
public import Mathlib.Algebra.CubicDiscriminant

@[expose] public section

noncomputable section
open Polynomial
namespace Turan

/-- Coefficients in descending order after the substitution z = w - 1/2. -/
private def shiftedCoeffs (a b : ℂ) : Cubic ℂ :=
  ⟨8 * b, 4 * a - 12 * b, 2 - 4 * a - 6 * b, 5 * b - a⟩

private theorem shifted_family (a b : ℂ) :
    (family 2 3 a b).comp (X - C (1 / 2)) = (shiftedCoeffs a b).toPoly := by
  apply Polynomial.funext
  intro w
  norm_num [family, hermite, shiftedCoeffs, Cubic.toPoly, eval_comp, eval_sub,
    eval_add, eval_mul, eval_pow, eval_smul, nsmul_eq_mul]
  ring

/-- The three shifted roots, counted with multiplicity, and their symmetric relation. -/
theorem cubic_shifted_factorization (a b : ℂ) (hb : b ≠ 0) :
    ∃ x y v : ℂ, rootRelation x y v ∧
      (family 2 3 a b).comp (X - C (1 / 2)) =
        C (8 * b) * (X - C x) * (X - C y) * (X - C v) := by
  let p := shiftedCoeffs a b
  have hlead : p.a ≠ 0 := mul_ne_zero (by norm_num : (8 : ℂ) ≠ 0) hb
  have hsplit := IsAlgClosed.splits p.toPoly
  have hcard : p.toPoly.roots.card = 3 :=
    hsplit.natDegree_eq_card_roots.symm.trans (Cubic.natDegree_of_a_ne_zero hlead)
  obtain ⟨x, y, v, hroots⟩ := Multiset.card_eq_three.mp hcard
  have hfac : p.toPoly = C (8 * b) * (X - C x) * (X - C y) * (X - C v) := by
    calc
      p.toPoly = _ := hsplit.eq_prod_roots
      _ = _ := by
        rw [Cubic.leadingCoeff_of_a_ne_zero hlead, hroots]
        simp [p, shiftedCoeffs, mul_assoc]
  refine ⟨x, y, v, ?_, (shifted_family a b).trans hfac⟩
  rw [Cubic.C_mul_prod_X_sub_C_eq] at hfac
  have h₂ : 4 * a - 12 * b = 8 * b * -(x + y + v) := Cubic.b_of_eq hfac
  have h₀ : 5 * b - a = 8 * b * -(x * y * v) := Cubic.d_of_eq hfac
  have hscaled : 8 * b * (4 * x * y * v + x + y + v + 1) = 0 := by
    linear_combination h₂ + 4 * h₀
  exact (mul_eq_zero.mp hscaled).resolve_left hlead

/-- A zero in the original variable is exactly one of the three roots after shifting. -/
theorem cubic_shifted_zero_iff (a b x y v : ℂ) (hb : b ≠ 0)
    (hfac : (family 2 3 a b).comp (X - C (1 / 2)) =
      C (8 * b) * (X - C x) * (X - C y) * (X - C v)) (z : ℂ) :
    (family 2 3 a b).eval z = 0 ↔
      z + 1 / 2 = x ∨ z + 1 / 2 = y ∨ z + 1 / 2 = v := by
  have heval := congrArg (eval (z + 1 / 2)) hfac
  simp only [eval_comp, eval_sub, eval_X, eval_C, add_sub_cancel_right, eval_mul] at heval
  rw [heval]
  simp [mul_eq_zero, sub_eq_zero, hb, or_assoc]

/-- The quadratic and linear coefficients recover the parameters from a shifted triple root. -/
theorem cubic_triple_root_coefficients (a b w : ℂ)
    (hfac : (family 2 3 a b).comp (X - C (1 / 2)) = C (8 * b) * (X - C w) ^ 3) :
    b * (12 * w ^ 2 - 12 * w + 9) = 1 ∧ a = (3 - 6 * w) * b := by
  rw [shifted_family, show C (8 * b) * (X - C w) ^ 3 =
      C (8 * b) * (X - C w) * (X - C w) * (X - C w) by ring,
    Cubic.C_mul_prod_X_sub_C_eq] at hfac
  have h₂ : 4 * a - 12 * b = 8 * b * -(w + w + w) := Cubic.b_of_eq hfac
  have h₁ : 2 - 4 * a - 6 * b = 8 * b * (w * w + w * w + w * w) := Cubic.c_of_eq hfac
  constructor
  · linear_combination -(h₁ + h₂) / 2
  · linear_combination h₂ / 4

/-- The shifted quadratic has a zero at distance at most one half from its origin. -/
theorem quadratic_half_disk (a : ℂ) :
    ∃ z : ℂ, (family 2 3 a 0).eval z = 0 ∧ ‖z + 1/2‖ ≤ 1/2 := by
  by_cases ha : a = 0
  · subst a
    exact ⟨-1 / 2, by norm_num [family, eval_add, eval_mul], by norm_num⟩

  -- The shifted quadratic has constant term -a and leading coefficient 4a.
  let q : Polynomial ℂ := C (4 * a) * X ^ 2 + C (2 - 4 * a) * X + C (-a)
  have hshift : (family 2 3 a 0).comp (X - C (1 / 2)) = q := by
    rw [shifted_family]
    simp [q, shiftedCoeffs, Cubic.toPoly]
  have hlead : 4 * a ≠ 0 := mul_ne_zero (by norm_num) ha
  have hcard : q.roots.card = 2 :=
    (IsAlgClosed.splits q).natDegree_eq_card_roots.symm.trans (natDegree_quadratic hlead)
  obtain ⟨x, y, hroots⟩ := Multiset.card_eq_two.mp hcard
  have hfac := (IsAlgClosed.splits q).eq_prod_roots
  rw [show q.leadingCoeff = 4 * a from leadingCoeff_quadratic hlead, hroots] at hfac
  have hfac' : q = C (4 * a) * ((X - C x) * (X - C y)) := by simpa using hfac
  have hconst : -a = 4 * a * (x * y) := by
    simpa [q, eval_add, eval_mul, eval_pow, eval_sub] using congrArg (eval 0) hfac'
  have hprod : x * y = -1 / 4 := by
    apply sub_eq_zero.mp
    have hscaled : a * (x * y - -1 / 4) = 0 := by linear_combination -hconst / 4
    exact (mul_eq_zero.mp hscaled).resolve_left ha
  have hnorm : ‖x‖ * ‖y‖ = 1 / 4 := by
    simpa [norm_mul, norm_div] using congrArg norm hprod
  have hsmall : ‖x‖ ≤ 1 / 2 ∨ ‖y‖ ≤ 1 / 2 := by
    by_contra! hlarge
    nlinarith [mul_pos (sub_pos.mpr hlarge.1) (sub_pos.mpr hlarge.2)]

  obtain ⟨w, hw, hbound⟩ : ∃ w : ℂ, q.eval w = 0 ∧ ‖w‖ ≤ 1 / 2 := by
    rcases hsmall with hx | hy
    · exact ⟨x, by rw [hfac']; simp [eval_mul, eval_sub], hx⟩
    · exact ⟨y, by rw [hfac']; simp [eval_mul, eval_sub], hy⟩
  refine ⟨w - 1 / 2, ?_, ?_⟩
  · rw [← hshift, eval_comp] at hw
    simpa [eval_sub] using hw
  · simpa using hbound

/-- When the cubic term vanishes, a zero lies in the closed strip of half-width 1/2. -/
theorem cubic_zero_b_half_strip (a : ℂ) :
    ∃ z : ℂ, (family 2 3 a 0).eval z = 0 ∧ |z.im| ≤ 1 / 2 := by
  obtain ⟨z, hz, hbound⟩ := quadratic_half_disk a
  exact ⟨z, hz, by simpa using (Complex.abs_im_le_norm (z+1/2)).trans hbound⟩

end Turan
