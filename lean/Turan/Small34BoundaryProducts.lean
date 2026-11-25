-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Small34EnvelopeDefs
import Turan.Small34SignDefs

noncomputable section
open Polynomial Real Set Filter
open scoped ComplexConjugate Topology

namespace Turan

private theorem boundary_product (a b c d e f y : ℝ) :
    ∃ P : Polynomial ℂ, P.Monic ∧ P.natDegree = 22 ∧ ∀ x : ℝ,
      P.eval (x : ℂ) = small34Z a b x y ^ 5 * conj (small34Z c d x y) ^ 4 *
        small34Z e f x y ^ 2 := by
  let pair (l r t : ℝ) : Polynomial ℂ :=
    (X - C ((r : ℂ) - t * Complex.I)) * (X - C ((l : ℂ) + t * Complex.I))
  have mon (l r t : ℝ) : (pair l r t).Monic := (monic_X_sub_C _).mul (monic_X_sub_C _)
  have deg (l r t : ℝ) : (pair l r t).natDegree = 2 := by
    unfold pair
    rw [(monic_X_sub_C _).natDegree_mul (monic_X_sub_C _), natDegree_X_sub_C, natDegree_X_sub_C]
  have ev (l r t x : ℝ) : (pair l r t).eval (x : ℂ) = small34Z l r x t := by
    simp only [pair, eval_mul, eval_sub, eval_X, eval_C, small34Z, Complex.ofReal_sub]
    ring
  have reflect (l r x : ℝ) : small34Z l r x (-y) = conj (small34Z l r x y) := by
    simp [small34Z, sub_eq_add_neg]
  let A := pair a b y
  let B := pair c d (-y)
  let D := pair e f y
  have hA := (mon a b y).pow 5
  have hB := (mon c d (-y)).pow 4
  have hD := (mon e f y).pow 2
  refine ⟨A^5 * B^4 * D^2, (hA.mul hB).mul hD, ?_, ?_⟩
  · rw [(hA.mul hB).natDegree_mul hD, hA.natDegree_mul hB]
    norm_num [A, B, D, natDegree_pow, deg]
  · intro x
    simp only [A, B, D, eval_mul, eval_pow, ev, reflect]

/-- Evaluation on the entire real boundary line identifies
each complex polynomial with the corresponding existing rounded product. -/
theorem small34_boundary_product_polynomials :
    ∃ P Q : Polynomial ℂ,
      P.Monic ∧ P.natDegree = 22 ∧ (∀ x : ℝ, P.eval (x : ℂ) = small34ZUpper x (5/7)) ∧
      Q.Monic ∧ Q.natDegree = 22 ∧ (∀ x : ℝ, Q.eval (x : ℂ) = small34ZLower x (5/7)) := by
  obtain ⟨P,hP⟩ := boundary_product (-1.311446) (-0.096251) (-1.553002) 1.794300
    (-0.308319) 2.074718 (5/7)
  obtain ⟨Q,hQ⟩ := boundary_product (-1.311445) (-0.096252) (-1.553003) 1.794301
    (-0.308318) 2.074717 (5/7)
  exact ⟨P,Q,hP.1,hP.2.1,hP.2.2,hQ⟩

private lemma upper_phase (x : ℝ) :
    (small34GUpper ⟨x,5/7⟩ : Angle) = ((small34ZUpper x (5/7)).arg : Angle) := by
  let z : ℂ := ⟨x,5/7⟩
  have hy : 0 < z.im := by norm_num [z]
  have ne (t : ℝ) : (t : ℂ)-z ≠ 0 := by
    intro h
    rw [← sub_eq_zero.mp h] at hy
    simp at hy
  have nc (t : ℝ) : conj ((t : ℂ)-z) ≠ 0 :=
    (map_ne_zero_iff _ (starRingEnd ℂ).injective).mpr (ne t)
  have pair (l r : ℝ) : small34Z l r x (5/7) = ((r : ℂ)-z) * conj ((l : ℂ)-z) := by
    have h (t : ℝ) : (((z.re-t : ℝ) : ℂ) + z.im * Complex.I) = -((t : ℂ)-z) := by
      apply Complex.ext <;> simp [Complex.sub_re,Complex.sub_im]
    have j (t : ℝ) : (((z.re-t : ℝ) : ℂ) - z.im * Complex.I) = conj (-((t : ℂ)-z)) := by
      rw [← h t]
      simp [sub_eq_add_neg]
    change small34Z l r z.re z.im = _
    rw [small34Z, h r, j l, map_neg, neg_mul_neg]
  have hn (l r : ℝ) : small34Z l r x (5/7) ≠ 0 := by
    rw [pair]
    exact mul_ne_zero (ne _) (nc _)
  have ha (l r : ℝ) : (small34Angle l r z : Angle) = ((small34Z l r x (5/7)).arg : Angle) := by
    rw [small34Angle_arg_quotient l r z hy.ne', pair, Complex.arg_div_coe_angle (ne _) (ne _),
      Complex.arg_mul_coe_angle (ne _) (nc _), Complex.arg_conj_coe_angle, sub_eq_add_neg]
  have coe_mul (n : ℕ) (t : ℝ) : (((n : ℝ)*t : ℝ) : Angle) = n • (t : Angle) := by
    rw [← nsmul_eq_mul, Angle.coe_nsmul]
  change (small34GUpper z : Angle) = _
  unfold small34GUpper small34ZUpper
  rw [Complex.arg_mul_coe_angle (by simp [hn]) (by simp [hn]),
    Complex.arg_mul_coe_angle (by simp [hn]) (by simp [hn]),
    Complex.arg_pow_coe_angle, Complex.arg_pow_coe_angle, Complex.arg_pow_coe_angle,
    Complex.arg_conj_coe_angle, Angle.coe_add, Angle.coe_sub,
    show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num,
    show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    coe_mul, coe_mul, coe_mul, ha, ha, ha]
  abel

/-- Exact rotation on the boundary, with the printed normalization. -/
theorem small34_upper_sine_prefactor (x : ℝ) :
    let Z := small34ZUpper x (5/7)
    Z.re - 44 * Z.im = -Real.sqrt 1937 * ‖Z‖ *
      Real.sin (small34GUpper ⟨x, 5/7⟩ - arctan (1/44)) := by
  let Z := small34ZUpper x (5/7)
  let g := small34GUpper ⟨x,5/7⟩
  change Z.re - 44 * Z.im = -Real.sqrt 1937 * ‖Z‖ * Real.sin (g - arctan (1/44))
  have hsin : Real.sin g = Real.sin Z.arg := congrArg Angle.sin (upper_phase x)
  have hcos : Real.cos g = Real.cos Z.arg := congrArg Angle.cos (upper_phase x)
  have hr : Real.sqrt (1+(1/44 : ℝ)^2) = Real.sqrt 1937 / 44 := by
    rw [show 1+(1/44 : ℝ)^2 = 1937 / 44^2 by norm_num,
      Real.sqrt_div (by norm_num), Real.sqrt_sq (by norm_num)]
  have hn : Real.sqrt 1937 ≠ 0 := by positivity
  rw [← Complex.norm_mul_cos_arg Z, ← Complex.norm_mul_sin_arg Z, Real.sin_sub, hsin, hcos,
    Real.cos_arctan, Real.sin_arctan, hr]
  field_simp [hn]
  ring

#print axioms small34_boundary_product_polynomials
#print axioms small34_upper_sine_prefactor

end Turan
