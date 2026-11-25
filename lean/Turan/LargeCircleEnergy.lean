-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Sturm
import Turan.Recover

open Set
namespace Turan

/-- The real restrictions of the oscillator and its complex derivative solve the real system. -/
theorem largeCircle_real_ode (m : ℕ) :
    (∀ t : ℝ, HasDerivAt (fun u : ℝ => (phi m u).re) (deriv (phi m) t).re t) ∧
    ∀ t : ℝ, HasDerivAt (fun u : ℝ => (deriv (phi m) u).re)
      (-(2 * (m : ℝ) + 1 - t ^ 2) * (phi m t).re) t := by
  obtain ⟨h₁, h₂⟩ := phi_equation m
  refine ⟨fun t => (h₁ t).real_of_complex, fun t => ?_⟩
  have hc : (t : ℂ)^2 - (2 * (m : ℂ) + 1) = ((-(2 * (m : ℝ) + 1 - t ^ 2) : ℝ) : ℂ) := by
    push_cast
    ring
  simpa only [hc, Complex.re_ofReal_mul] using (h₂ t).real_of_complex

private theorem energy_origin (m : ℕ) (hm : 0 < m) :
    1 ≤ (m : ℝ) * (phi m 0).re ^ 2 + (deriv (phi m) 0).re ^ 2 / 2 := by
  have hreal (t : ℝ) : ((psi m t).re : ℂ) = psi m t := by
    have hi : ((hermite m).eval (t : ℂ)).im = 0 := by
      apply Complex.conj_eq_iff_im.mp
      simpa using (hermite_symmetry m (t : ℂ)).1.symm
    refine Complex.ext ?_ ?_
    · rfl
    simp only [Complex.ofReal_im, psi, Complex.div_ofReal_im, hi, zero_div]
  have hd : HasDerivAt (psi m) (deriv (psi m) 0) 0 :=
    (((hermite m).hasDerivAt (0 : ℂ)).div_const
      (Real.sqrt (2 ^ m * (m.factorial : ℝ)) : ℂ)).differentiableAt.hasDerivAt
  have hdR := (show HasDerivAt (psi m) (deriv (psi m) 0) ((0 : ℝ) : ℂ) from hd).real_of_complex
  have hdC : HasDerivAt (fun t : ℝ => psi m t) ((deriv (psi m) 0).re : ℂ) 0 := by
    simpa only [hreal] using hdR.ofReal_comp
  have hder := hdC.unique (show HasDerivAt (fun t : ℝ => psi m t) (deriv (psi m) 0) 0 from
    hd.comp_ofReal)
  have hg : HasDerivAt (fun z : ℂ => Complex.exp (-z^2 / 2)) 0 0 := by
    convert ((((hasDerivAt_id (0 : ℂ)).pow 2).neg.div_const 2).cexp) using 1 <;> norm_num
  have hdφ : HasDerivAt (phi m) (deriv (psi m) 0) 0 := by
    simpa [phi, Pi.mul_def] using! hg.mul hd
  have hval : ((psi m 0).re : ℂ) = psi m 0 := hreal 0
  have hnorm {z : ℂ} (hz : (z.re : ℂ) = z) : ‖z‖ ^ 2 = z.re ^ 2 := by
    conv_lhs => rw [← hz, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simpa only [hdφ.deriv, phi, ne_eq, zero_pow (by decide : 2 ≠ 0), neg_zero, zero_div,
    Complex.exp_zero, one_mul, hnorm hval, hnorm hder] using recover_energy_at_zero m hm

/-- Monotonicity of the Sonin energy up to a zero in the oscillatory interval. -/
theorem largeCircle_slope_sharp (m : ℕ) (hm : 450 ≤ m) (x : ℝ) (hx : 0 ≤ x)
    (hxQ : (m : ℝ) / 9 < 2 * (m : ℝ) + 1 - x ^ 2) (hz : psi m x = 0) :
    26 / 100 < |(deriv (phi m) x).re| := by
  let y (t : ℝ) := (phi m t).re
  let v (t : ℝ) := (deriv (phi m) t).re
  let q (t : ℝ) := 2 * (m : ℝ) + 1 - t ^ 2
  let E (t : ℝ) := y t ^ 2 + v t ^ 2 / q t
  obtain ⟨hy, hv⟩ := largeCircle_real_ode m
  have hmR : (450 : ℝ) ≤ m := by exact_mod_cast hm
  have hq (t : ℝ) (ht : t ∈ Icc 0 x) : 0 < q t := by
    dsimp [q]
    nlinarith [sq_le_sq₀ ht.1 hx |>.mpr ht.2]
  have hE (t : ℝ) (ht : t ∈ Icc 0 x) :
      HasDerivAt E (2 * t * v t ^ 2 / q t ^ 2) t := by
    have hq' : HasDerivAt q (-2*t) t := by
      convert ((hasDerivAt_id t).pow 2).const_sub (2 * (m : ℝ) + 1) using 1 <;> simp
      ring
    have hv' : HasDerivAt v (-q t * y t) t := hv t
    have hy' : HasDerivAt y (v t) t := hy t
    convert (hy'.pow 2).add ((hv'.pow 2).div hq' (hq t ht).ne') using 1
    simp only [Pi.pow_apply]
    field_simp [(hq t ht).ne']
    ring
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
    (fun t ht => (hE t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hE t (interior_subset ht)).hasDerivWithinAt)
    (fun t ht => by
      have ht0 := (show t ∈ Icc 0 x from interior_subset ht).1
      positivity)
  have he := hmono (left_mem_Icc.mpr hx) (right_mem_Icc.mpr hx) hx
  have hz' : y x = 0 := by simp [y, phi, hz]
  have hstart : 1 ≤ (m : ℝ) * y 0 ^ 2 + v 0 ^ 2 / 2 := by
    simpa [y, v] using energy_origin m (by omega)
  have h0 : 0 < q 0 := hq 0 (left_mem_Icc.mpr hx)
  have hend := hq x (right_mem_Icc.mpr hx)
  have hinit : 2 / q 0 ≤ E 0 := by
    dsimp only [E]
    rw [← sub_le_iff_le_add, ← sub_div, div_le_iff₀ h0]
    simp only [q, zero_pow (by decide : 2 ≠ 0), sub_zero]
    nlinarith [sq_nonneg (y 0)]
  have hbound := hinit.trans he
  simp only [E, hz', zero_pow (by decide : 2 ≠ 0), zero_add] at hbound
  have hprod := (div_le_div_iff₀ h0 hend).mp hbound
  change 26 / 100 < |v x|
  by_contra! h
  have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 26/100)).mpr h
  rw [sq_abs] at hs
  have hsmall := mul_le_mul_of_nonneg_right hs h0.le
  simp only [q, zero_pow (by decide : 2 ≠ 0), sub_zero] at hprod hsmall
  nlinarith

theorem largeCircle_slope (m : ℕ) (hm : 450 ≤ m) (x : ℝ) (hx : 0 ≤ x)
    (hxQ : (m : ℝ) / 9 < 2 * (m : ℝ) + 1 - x ^ 2) (hz : psi m x = 0) :
    1 / 4 < |(deriv (phi m) x).re| := by
  exact lt_trans (by norm_num) (largeCircle_slope_sharp m hm x hx hxQ hz)

end Turan
