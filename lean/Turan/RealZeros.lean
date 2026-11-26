module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Oscillator
public import Turan.Hermite

@[expose] public section

noncomputable section
open Polynomial
open scoped ComplexConjugate
namespace Turan

private theorem hermite_eval_step (n : ℕ) (z : ℂ) :
    (hermite (n + 2)).eval z = 2 * z * (hermite (n + 1)).eval z -
      ((2 * (n + 1) : ℕ) : ℂ) * (hermite n).eval z := by
  rw [hermite, eval_sub, eval_mul, eval_mul, eval_X, eval_ofNat, eval_smul, nsmul_eq_mul]

/-- Every consecutive Hermite quotient maps the upper half-plane into itself. -/
theorem hermite_ratio_im_pos (n : ℕ) (z : ℂ) (hz : 0 < z.im) :
    0 < ((hermite (n + 1)).eval z / (hermite n).eval z).im := by
  induction n with
  | zero =>
    simpa [hermite, eval_mul, Complex.mul_im] using (mul_pos (by norm_num : (0 : ℝ) < 2) hz)
  | succ n ih =>
    let t := (hermite (n + 1)).eval z / (hermite n).eval z
    change 0 < t.im at ih
    have ht : t ≠ 0 := fun h => by simp [h] at ih
    have hcur : (hermite (n + 1)).eval z ≠ 0 := fun h => ht (by simp [t, h])
    have hstep : (hermite (n + 2)).eval z / (hermite (n + 1)).eval z =
        2 * z - ((2 * (n + 1) : ℕ) : ℂ) * t⁻¹ := by
      rw [hermite_eval_step, sub_div, mul_div_cancel_right₀ _ hcur, mul_div_assoc]
      simp [t]
    have hinv : t⁻¹.im < 0 := by
      rw [Complex.inv_im]
      exact div_neg_of_neg_of_pos (neg_lt_zero.mpr ih) (Complex.normSq_pos.mpr ht)
    rw [hstep, Complex.sub_im]
    simp only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_re,
      Complex.natCast_im, zero_mul, add_zero]
    exact sub_pos.mpr ((mul_neg_of_pos_of_neg (by positivity) hinv).trans (by positivity))

/-- Consecutive Hermite polynomials have no common zero. -/
theorem hermite_prev_ne_zero (n : ℕ) (z : ℂ) (hz : (hermite (n + 1)).eval z = 0) :
    (hermite n).eval z ≠ 0 := by
  induction n with
  | zero => simp [hermite]
  | succ n ih =>
    intro hcur
    have hstep := hermite_eval_step n z
    rw [hz, hcur, mul_zero, zero_sub, eq_comm, neg_eq_zero] at hstep
    exact (mul_ne_zero (by exact_mod_cast (show 2 * (n + 1) ≠ 0 by omega)) (ih hcur)) hstep

theorem hermite_real_simple (j : ℕ) (z : ℂ) (hz : (hermite j).eval z = 0) :
    z.im = 0 ∧ (hermite j).derivative.eval z ≠ 0 := by
  have no_upper (w : ℂ) (hw : 0 < w.im) : (hermite j).eval w ≠ 0 := by
    intro h
    have hratio := hermite_ratio_im_pos j w hw
    simp [h] at hratio
  constructor
  · rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
    · have hc : (hermite j).eval (conj z) = 0 := by rw [(hermite_symmetry j z).1, hz, map_zero]
      exact (no_upper (conj z) (by simpa using hneg) hc).elim
    · exact hzero
    · exact (no_upper z hpos hz).elim
  · cases j with
    | zero => simp [hermite] at hz
    | succ n =>
      rw [hermite_derivative, eval_smul, nsmul_eq_mul]
      exact mul_ne_zero (by exact_mod_cast (show 2 * (n + 1) ≠ 0 by omega))
        (hermite_prev_ne_zero n z hz)

/-- Dividing by the positive normalization preserves real, simple zeros. -/
theorem psi_real_simple (j : ℕ) (z : ℂ) (hz : psi j z = 0) :
    z.im = 0 ∧ deriv (psi j) z ≠ 0 := by
  let d : ℝ := Real.sqrt (2 ^ j * (j.factorial : ℝ))
  have hd : 0 < d := by
    have := Nat.factorial_pos j
    dsimp [d]
    positivity
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  change (hermite j).eval z / (d : ℂ) = 0 at hz
  have ⟨hreal, hsimple⟩ := hermite_real_simple j z ((div_eq_zero_iff.mp hz).resolve_right hd')
  have hderiv : HasDerivAt (psi j) ((hermite j).derivative.eval z / (d : ℂ)) z :=
    ((hermite j).hasDerivAt z).div_const _
  exact ⟨hreal, hderiv.deriv.symm ▸ div_ne_zero hsimple hd'⟩

private theorem hermite_eval_real_im (j : ℕ) (x : ℝ) : ((hermite j).eval (x : ℂ)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  simpa using (hermite_symmetry j (x : ℂ)).1.symm

/-- Apply the real intermediate value theorem along the real axis in either sign order. -/
private theorem zero_between_of_sign_change (f : ℂ → ℂ) (hc : Continuous f)
    (hreal : ∀ t : ℝ, (f t).im = 0) (a b : ℝ) (hab : a < b)
    (hsign : (f a).re * (f b).re < 0) : ∃ x ∈ Set.Ioo a b, f x = 0 := by
  let g := fun t : ℝ => (f t).re
  have hg : Continuous g := Complex.continuous_re.comp (hc.comp Complex.continuous_ofReal)
  have hzero : 0 ∈ g '' Set.Ioo a b := by
    rcases mul_neg_iff.mp hsign with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact intermediate_value_Ioo' hab.le hg.continuousOn ⟨hb, ha⟩
    · exact intermediate_value_Ioo hab.le hg.continuousOn ⟨ha, hb⟩
  obtain ⟨x, hx, hgx⟩ := hzero
  exact ⟨x, hx, Complex.ext hgx (hreal x)⟩

theorem hermite_zero_of_sign_change (j : ℕ) (a b : ℝ) (hab : a < b)
    (hsign : ((hermite j).eval (a : ℂ)).re * ((hermite j).eval (b : ℂ)).re < 0) :
    ∃ x ∈ Set.Ioo a b, (hermite j).eval (x : ℂ) = 0 :=
  zero_between_of_sign_change _ (hermite j).continuous (hermite_eval_real_im j) a b hab hsign

theorem psi_zero_of_sign_change (j : ℕ) (a b : ℝ) (hab : a < b)
    (hsign : (psi j a).re * (psi j b).re < 0) :
    ∃ x ∈ Set.Ioo a b, psi j x = 0 := by
  refine zero_between_of_sign_change (psi j) ((hermite j).continuous.div_const _) ?_ a b hab hsign
  intro x
  simp only [psi, Complex.div_ofReal_im, hermite_eval_real_im, zero_div]

end Turan
