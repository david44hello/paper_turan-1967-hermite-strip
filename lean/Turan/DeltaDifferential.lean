-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.DeltaCriterion
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
namespace Turan

private theorem quarticDen_hasDerivAt (w : ℂ) :
    HasDerivAt quarticDen (8*w+4) w := by
  have h := hasDerivAt_id w
  apply (((h.fun_pow 2).const_mul 4 |>.add (h.const_mul 4)).add_const 2).congr_deriv
  dsimp
  ring

theorem quartic_ratio_contact (w : ℂ) (hw : 0 < w.im ∧ 12*w^4+16*w^3+12*w^2-3=0) :
    quarticRatio w=4*w^2 ∧ HasDerivAt quarticRatio (-4*w) w := by
  have hd := quartic_den_ne w (by linarith [(quartic_root_height w hw).1])
  have hval : 4*w^4-4*w^2+3 = 4*w^2*quarticDen w := by
    unfold quarticDen
    linear_combination -hw.2
  refine ⟨(div_eq_iff hd).2 hval, ?_⟩
  have h := hasDerivAt_id w
  have hnum : HasDerivAt (fun z : ℂ => 4*z^4-4*z^2+3) (16*w^3-8*w) w := by
    apply (((h.fun_pow 4).const_mul 4 |>.sub ((h.fun_pow 2).const_mul 4)).add_const 3).congr_deriv
    dsimp
    ring
  apply (hnum.fun_div (quarticDen_hasDerivAt w) hd).congr_deriv
  apply (div_eq_iff (pow_ne_zero 2 hd)).2
  rw [hval]
  unfold quarticDen
  ring

theorem quartic_delta_stationary (w : ℂ) (hw : 0<w.im ∧ 12*w^4+16*w^3+12*w^2-3=0) :
    quarticDelta w.im (w.re+1/2)=0 ∧ HasDerivAt (quarticDelta w.im) 0 (w.re+1/2) := by
  let x := w.re+1/2
  let z (s : ℝ) : ℂ := ⟨s-1/2, w.im⟩
  have hx : z x = w := by apply Complex.ext <;> simp [z, x]
  have hz : HasDerivAt z 1 x := by
    have h := (((hasDerivAt_id x).sub_const (1/2)).ofReal_comp).add_const (⟨0,w.im⟩ : ℂ)
    convert h using 1
    funext s
    apply Complex.ext <;> simp [z]
  obtain ⟨hval, hratio⟩ := quartic_ratio_contact w hw
  have hq : HasDerivAt (quarticRatio ∘ z) (-4*w) x := by
    simpa only [mul_one] using hratio.comp_of_eq x hz hx.symm
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hq
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hq
  let B (s : ℝ) := 16*w.im^2*((quarticRatio (z s)).re+4*w.im^2)-(quarticRatio (z s)).im^2
  have hB : B x = 0 := by
    dsimp only [B]
    rw [hx, hval]
    norm_num [pow_two, Complex.mul_re, Complex.mul_im]
    ring
  have hB' : HasDerivAt B 0 x := by
    apply (((hre.add_const (4*w.im^2)).const_mul (16*w.im^2)).sub (him.fun_pow 2)).congr_deriv
    simp only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply, hx, hval]
    norm_num [pow_two, Complex.mul_re, Complex.mul_im]
    ring
  let A (s : ℝ) := ‖quarticDen (z s)‖^4/(4*w.im^2)
  have hD := (quarticDen_hasDerivAt w).comp_of_eq x hz hx.symm
  have hA : DifferentiableAt ℝ A x := by
    simpa only [A, ← pow_mul, Function.comp_apply] using
      ((hD.norm_sq.fun_pow 2).differentiableAt.div_const (4*w.im^2))
  change A x * B x = 0 ∧ HasDerivAt (fun s => A s * B s) 0 x
  exact ⟨by simp [hB], (hA.hasDerivAt.fun_mul hB').congr_deriv (by simp [hB])⟩

#print axioms quartic_ratio_contact
#print axioms quartic_delta_stationary

end Turan
