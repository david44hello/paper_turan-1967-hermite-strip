-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.CircleWeightedSeries
import Turan.Volterra

noncomputable section
open Polynomial
namespace Turan

/-- The Gaussian weight divided by its value at the real center. -/
def normalizedCircleWeight (x : ℝ) (z : ℂ) : ℂ := Complex.exp (((x : ℂ)^2 - z^2) / 2)

/-- Lemma 13 after rescaling the Hermite polynomial and dividing the weight by
its center value. The scalar is arbitrary so the same estimate applies in ratio charts. -/
theorem weighted_normalized_expansion (j : ℕ) (c : ℂ) (x r : ℝ) (hr : 0 < r)
    (hQ : circleQ j x r ≤ 36) (v : ℂ) (hv : ‖v‖ ≤ 1) :
    let p := C c * hermite j
    let d := (r : ℂ) * (p.derivative.eval (x : ℂ) - x * p.eval (x : ℂ))
    ‖normalizedCircleWeight x (x + r*v) * p.eval (x + r*v) - d*v‖ ≤
      seriesUpper (circleQ j x r) 0 * ‖p.eval (x : ℂ)‖ +
      (seriesUpper (circleQ j x r) 1 - 1) * ‖d‖ := by
  let p := C c * hermite j
  let s := Real.sqrt (2^j * (j.factorial : ℝ))
  let K := Complex.exp ((x : ℂ)^2 / 2) * c * (s : ℂ)
  have hs : (s : ℂ) ≠ 0 := by
    have := Nat.factorial_pos j
    exact_mod_cast (show 0 < s by dsimp [s]; positivity).ne'
  have hid (z : ℂ) : normalizedCircleWeight x z * p.eval z = K * phi j z := by
    rw [normalizedCircleWeight, show ((x : ℂ)^2-z^2)/2 = (x:ℂ)^2/2 + (-z^2/2) by ring,
      Complex.exp_add]
    simp only [K, phi, psi, p, eval_mul, eval_C]
    change _ = _ * (Complex.exp (-z^2/2) * ((hermite j).eval z / (s : ℂ)))
    field_simp
  have hx : normalizedCircleWeight x x = 1 := by simp [normalizedCircleWeight]
  have hval : K * phi j x = p.eval (x : ℂ) := by rw [← hid, hx, one_mul]
  have hg : HasDerivAt (normalizedCircleWeight x) (-(x : ℂ)) (x : ℂ) := by
    unfold normalizedCircleWeight
    convert (((((hasDerivAt_id (x : ℂ)).pow 2).const_sub ((x : ℂ)^2)).div_const 2).cexp)
      using 1 <;> simp
    ring
  have hleft : HasDerivAt (fun z => normalizedCircleWeight x z * p.eval z)
      (p.derivative.eval (x : ℂ) - x * p.eval (x : ℂ)) (x : ℂ) := by
    convert hg.mul (p.hasDerivAt (x : ℂ)) using 1
    rw [hx]
    ring
  have hright := ((phi_equation j).1 (x : ℂ)).const_mul K
  rw [funext hid] at hleft
  have hdelta : K * ((r : ℂ) * deriv (phi j) x) =
      (r : ℂ) * (p.derivative.eval (x : ℂ) - x * p.eval (x : ℂ)) := by
    rw [hleft.unique hright]
    ring
  have hpos : 0 < circleQ j x r := by unfold circleQ; positivity
  have h := mul_le_mul_of_nonneg_left (lemma_thirteen j x r hr v hv) (norm_nonneg K)
  dsimp only at h ⊢
  let q := Real.sqrt (circleQ j x r)
  calc
    _ = ‖K‖ * ‖phi j (x + r*v) - ((r:ℂ)*deriv (phi j) x)*v‖ := by
      rw [← norm_mul, mul_sub K, ← mul_assoc K, hdelta, ← hid]
    _ ≤ _ := h
    _ = Real.cosh q * ‖p.eval (x : ℂ)‖ + (Real.sinh q / q - 1) *
        ‖(r : ℂ) * (p.derivative.eval (x : ℂ) - x * p.eval (x : ℂ))‖ := by
      rw [← hdelta, ← hval, norm_mul K, norm_mul K]
      ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right (cosh_sqrt_le_seriesUpper _ hpos hQ) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (sub_le_sub_right (sinh_sqrt_div_le_seriesUpper _ hpos hQ) 1)
        (norm_nonneg _))

private theorem weightedPivot_eq (j : ℕ) (x r : ℝ) :
    (weightedPivot j x r : ℂ) = (r : ℂ) *
      ((scaledMode j).derivative.eval (x : ℂ) - x * (scaledMode j).eval (x : ℂ)) := by
  let p := scaledMode j
  have hreal (t : ℝ) : ((p.eval (t : ℂ)).re : ℂ) = p.eval (t : ℂ) := by
    apply Complex.conj_eq_iff_re.mp
    have hH := (hermite_symmetry j (t : ℂ)).1.symm
    simp [p, scaledMode, eval_mul, hH, map_ofNat]
  have hD := p.hasDerivAt (x : ℂ)
  have hd' : HasDerivAt (fun t : ℝ => p.eval (t : ℂ)) ((p.derivative.eval (x : ℂ)).re : ℂ) x := by
    simpa only [hreal] using hD.real_of_complex.ofReal_comp
  have hd := hd'.unique hD.comp_ofReal
  have hcoeff : (circleJet j x r).coeff 1 = (r : ℂ) * p.derivative.eval (x : ℂ) := by
    have h := (circleJet j x r).coeff_derivative 0
    simp only [zero_add, Nat.cast_zero, mul_one, coeff_zero_eq_eval_zero] at h
    rw [← h]
    simp [circleJet, derivative_comp, eval_comp, eval_mul, eval_add, p]
  simp only [weightedPivot, circlePivot, hcoeff, Complex.re_ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_mul]
  change (r : ℂ) * _ - (x : ℂ) * r * ((p.eval (x : ℂ)).re : ℂ) = _
  rw [hd, hreal]
  ring

/-- The normalized remainder in the certificate's real pivot coordinates. -/
theorem weighted_mode_remainder (j : ℕ) (x r : ℝ) (hr : 0 < r) (hQ : circleQ j x r ≤ 36)
    (v : ℂ) (hv : ‖v‖ ≤ 1) :
    ‖normalizedCircleWeight x (x + r*v) * (scaledMode j).eval (x + r*v) -
        (weightedPivot j x r : ℂ)*v‖ ≤ weightedError j x r := by
  have h := weighted_normalized_expansion j (128^j) x r hr hQ v hv
  dsimp only at h
  rw [show C ((128:ℂ)^j) * hermite j = scaledMode j by rfl] at h
  rw [← weightedPivot_eq, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

end Turan
