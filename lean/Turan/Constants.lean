-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs
import Mathlib.Tactic

noncomputable section
open scoped ComplexConjugate
namespace Turan

private theorem u_equation : 32 * u ^ 3 + 6 * u = 1 := by
  have triple := Real.sinh_three_mul (Real.arsinh 1 / 3)
  rw [show 3 * (Real.arsinh 1 / 3) = Real.arsinh 1 by ring, Real.sinh_arsinh] at triple
  unfold u
  linarith only [triple]

private theorem h_square : h ^ 2 = 3/4 + 3 * u ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem constants_spec :
    32 * u ^ 3 + 6 * u = 1 ∧ 0 < u ∧ u < 1/6 ∧
    (∀ r : ℝ, 32 * r ^ 3 + 6 * r = 1 → r = u) ∧
    h ^ 2 = 3/4 + 3 * u ^ 2 ∧ 1/2 < h := by
  have hu : 0 < u := by
    unfold u
    have : 0 < Real.arsinh 1 := Real.arsinh_pos_iff.mpr one_pos
    exact div_pos (Real.sinh_pos_iff.mpr (by positivity)) (by norm_num)
  refine ⟨u_equation, hu, ?_, ?_, h_square, ?_⟩
  · nlinarith [u_equation, pow_pos hu 3]
  · intro r hr
    rcases lt_trichotomy r u with hlt | heq | hgt
    · linarith [u_equation, (Odd.strictMono_pow (by decide : Odd 3)) hlt]
    · exact heq
    · linarith [u_equation, (Odd.strictMono_pow (by decide : Odd 3)) hgt]
  · have hn : 0 ≤ h := Real.sqrt_nonneg _
    nlinarith [h_square, sq_nonneg u]

theorem lemma_four :
    (∀ w : ℂ, 4 * w ^ 3 + 3 * w + 1 = 0 ↔
      w = -2 * (u : ℂ) ∨ w = W ∨ w = conj W) ∧
    0 < u ∧ u < 1/6 ∧ ‖W‖ ^ 2 = 1/(8*u) ∧
    h = Real.sqrt 3 / 2 * Real.cosh (Real.log (1 + Real.sqrt 2) / 3) := by
  obtain ⟨hu, hpos, hsmall, _, hh, hhalf⟩ := constants_spec
  have hsum : W + conj W = 2 * (u : ℂ) := by
    apply Complex.ext <;> simp [W, Complex.add_re, Complex.add_im, two_mul]
  have hprod : W * conj W = (u : ℂ)^2 + (h : ℂ)^2 := by
    apply Complex.ext <;> simp [W, pow_two, Complex.mul_re, Complex.mul_im] <;> ring
  have hu' : 32 * (u : ℂ)^3 + 6 * (u : ℂ) = 1 := by exact_mod_cast hu
  have hh' : (h : ℂ)^2 = 3/4 + 3 * (u : ℂ)^2 := by
    simpa using congrArg Complex.ofReal hh
  refine ⟨?_, hpos, hsmall, ?_, ?_⟩
  · intro w
    have hfac : 4 * w ^ 3 + 3 * w + 1 =
        4 * (w - -2 * (u : ℂ)) * (w - W) * (w - conj W) := by
      linear_combination -hu' + (-8 * (u : ℂ) - 4 * w) * hh' +
        (4*w^2 + 8*(u : ℂ)*w) * hsum + (-4*w - 8*(u : ℂ)) * hprod
    rw [hfac]
    simp only [mul_eq_zero, sub_eq_zero, OfNat.ofNat_ne_zero, false_or, or_assoc]
  · rw [Complex.sq_norm, Complex.normSq_apply, eq_div_iff (by positivity)]
    change (u*u+h*h)*(8*u) = 1
    linear_combination hu + 8*u * hh
  · have has : Real.arsinh 1 = Real.log (1 + Real.sqrt 2) := by norm_num [Real.arsinh]
    rw [← has]
    let t := Real.arsinh 1 / 3
    change h = Real.sqrt 3 / 2 * Real.cosh t
    apply (sq_eq_sq₀ (by linarith : 0 ≤ h) (by positivity)).mp
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.cosh_sq']
    change h ^ 2 = 3 / 2 ^ 2 * (1 + Real.sinh t ^ 2)
    change h ^ 2 = 3/4 + 3 * (Real.sinh t / 2)^2 at hh
    linarith

end Turan
