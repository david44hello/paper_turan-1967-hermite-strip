-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Constants

noncomputable section
open scoped ComplexConjugate
namespace Turan

/-- Comparing coefficients after the shift gives a cube whenever the
    scale and its proposed triple root satisfy the two scalar equations. -/
private theorem eval_triple_cube (w b z : ℂ)
    (hscale : b * (12 * w ^ 2 - 12 * w + 9) = 1)
    (hroot : 4 * w ^ 3 + 3 * w + 1 = 0) :
    (family 2 3 ((3 - 6 * w) * b) b).eval z = 8 * b * (z + 1/2 - w)^3 := by
  have hexpand (a : ℂ) : (family 2 3 a b).eval z =
      1 + 2 * z + a * (4 * z^2 - 2) + b * (8 * z^3 - 12 * z) := by
    norm_num [family, hermite, nsmul_eq_mul, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_add]
    ring
  rw [hexpand]
  linear_combination -(2 * (z + 1/2)) * hscale + 2 * b * hroot

private theorem cube_zero_iff (w b z : ℂ) (hb : b ≠ 0) :
    8 * b * (z + 1/2 - w)^3 = 0 ↔ z = w - 1/2 := by
  simp [hb, sub_eq_zero, eq_sub_iff_add_eq]

theorem extremal_cubics :
    let p := family 2 3 extremalA extremalB
    let q := family 2 3 (conj extremalA) (conj extremalB)
    p ≠ q ∧ extremalB ≠ 0 ∧
    (∀ z : ℂ, p.eval z = 8 * extremalB * (z + 1/2 - W)^3 ∧
      q.eval z = 8 * conj extremalB * (z + 1/2 - conj W)^3) ∧
    (∀ z : ℂ, (p.eval z = 0 ↔ z = W - 1/2) ∧
              (q.eval z = 0 ↔ z = conj W - 1/2)) ∧
    |(W - 1/2).im| = h ∧ |(conj W - 1/2).im| = h := by
  dsimp only
  obtain ⟨_, _, hu, _, _, hh⟩ := constants_spec
  have hpos : 0 < h := by linarith
  -- The imaginary part of the denominator is 12 (2u - 1) h.
  have hden : 12 * W ^ 2 - 12 * W + 9 ≠ 0 := by
    intro hz
    have him := congrArg Complex.im hz
    norm_num [W, pow_two, Complex.add_im, Complex.sub_im, Complex.mul_im,
      Complex.mul_re] at him
    nlinarith [mul_neg_of_neg_of_pos (show 2 * u - 1 < 0 by linarith) hpos]
  have hb : extremalB ≠ 0 := inv_ne_zero hden
  have hscale : extremalB * (12 * W ^ 2 - 12 * W + 9) = 1 :=
    inv_mul_cancel₀ hden
  have hscaleConj : conj extremalB * (12 * (conj W)^2 - 12 * conj W + 9) = 1 := by
    simpa [map_ofNat] using congrArg (conj : ℂ → ℂ) hscale
  have factors (z : ℂ) :
      (family 2 3 extremalA extremalB).eval z = 8 * extremalB * (z + 1/2 - W)^3 ∧
      (family 2 3 (conj extremalA) (conj extremalB)).eval z =
        8 * conj extremalB * (z + 1/2 - conj W)^3 := by
    constructor
    · exact eval_triple_cube W extremalB z hscale ((lemma_four.1 W).2 (.inr (.inl rfl)))
    · have hroot := (lemma_four.1 (conj W)).2 (.inr (.inr rfl))
      simpa [extremalA, map_ofNat] using eval_triple_cube (conj W) (conj extremalB) z hscaleConj hroot
  have zeros (z : ℂ) :
      ((family 2 3 extremalA extremalB).eval z = 0 ↔ z = W - 1/2) ∧
      ((family 2 3 (conj extremalA) (conj extremalB)).eval z = 0 ↔ z = conj W - 1/2) := by
    rw [(factors z).1, (factors z).2]
    exact ⟨cube_zero_iff W extremalB z hb, cube_zero_iff (conj W) (conj extremalB) z
      (by simpa using hb)⟩
  refine ⟨?_, hb, factors, zeros, ?_, ?_⟩
  · intro heq
    have hz := (zeros (W - 1/2)).1.mpr rfl
    rw [heq] at hz
    have hw : W = conj W := sub_left_inj.mp ((zeros _).2.mp hz)
    have him := congrArg Complex.im hw
    change h = -h at him
    linarith
  · norm_num [Complex.sub_im, W, abs_of_pos hpos]
  · norm_num [Complex.sub_im, W, abs_of_pos hpos]

theorem cubic_sharp (t : ℝ) (ht : t < h) :
    ∃ a b : ℂ, ∀ z : ℂ, (family 2 3 a b).eval z = 0 → t < |z.im| := by
  obtain ⟨_, _, _, zeros, height, _⟩ := extremal_cubics
  refine ⟨extremalA, extremalB, ?_⟩
  intro z hz
  rw [(zeros z).1.mp hz, height]
  exact ht

end Turan
