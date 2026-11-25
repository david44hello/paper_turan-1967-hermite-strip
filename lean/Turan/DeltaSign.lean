-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.DeltaZero

noncomputable section
namespace Turan

private theorem quartic_barrier_I : quarticBarrier Complex.I = 1039/25 := by
  norm_num [quarticBarrier, quarticRatio, quarticDen, pow_succ, Complex.div_re, Complex.div_im,
    Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]

private theorem quartic_barrier_continuousAt (z : ℂ) (hz : 1/2 < z.im) :
    ContinuousAt quarticBarrier z := by
  have hratio : ContinuousAt quarticRatio z := by
    unfold quarticRatio
    apply ContinuousAt.div
    · fun_prop
    · unfold quarticDen
      fun_prop
    · exact quartic_den_ne z hz
  unfold quarticBarrier
  fun_prop

theorem quartic_delta_positive_off (w : ℂ) (hw : 0<w.im ∧ 12*w^4+16*w^3+12*w^2-3=0)
    (s : ℝ) (hs : s ≠ w.re+1/2) : 0 < quarticDelta w.im s := by
  obtain ⟨hlo, hhi, _⟩ := quartic_root_height w hw
  have hhalf : 1/2 < w.im := by linarith
  have hrise : 0 < 1-w.im := by linarith
  let z : ℂ := ⟨s-1/2, w.im⟩
  let γ (t : ℝ) := z + (t:ℂ) * (Complex.I-z)
  have hstart : γ 0 = z := by simp [γ]
  have hend : γ 1 = Complex.I := by simp [γ]
  have hγ : Continuous γ := by unfold γ; fun_prop
  have him (t : ℝ) : (γ t).im = w.im + t*(1-w.im) := by
    simp [γ, z, Complex.add_im, Complex.mul_im, Complex.sub_im]
  have hheight (t : ℝ) (ht : 0 ≤ t) : w.im ≤ (γ t).im := by
    rw [him]
    exact le_add_of_nonneg_right (mul_nonneg ht hrise.le)
  have hc : ContinuousOn (fun t => quarticBarrier (γ t)) (Set.Icc 0 1) := by
    intro t ht
    exact ((quartic_barrier_continuousAt _ (hhalf.trans_le (hheight t ht.1))).comp
      hγ.continuousAt).continuousWithinAt
  have hpos : 0 < quarticBarrier z := by
    by_contra! hnonpos
    obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hc
      (show 0 ∈ Set.Icc (quarticBarrier (γ 0)) (quarticBarrier (γ 1)) by
        rw [hstart, hend, quartic_barrier_I]
        exact ⟨hnonpos, by norm_num⟩)
    have heq := quartic_barrier_zero w (γ t) hw (hheight t ht.1) hzero
    have htim : t*(1-w.im) = 0 := by linarith only [him t, congrArg Complex.im heq]
    have htzero := (mul_eq_zero.mp htim).resolve_right hrise.ne'
    rw [htzero, hstart] at heq
    have hre := congrArg Complex.re heq
    change s-1/2 = w.re at hre
    exact hs (by linarith)
  have hnorm : 0 < ‖quarticDen z‖ := norm_pos_iff.mpr (quartic_den_ne z hhalf)
  change 0 < (‖quarticDen z‖^4/(4*w.im^2)) * quarticBarrier z
  exact mul_pos (div_pos (pow_pos hnorm _) (mul_pos (by norm_num) (pow_pos hw.1 _))) hpos

end Turan

#print axioms Turan.quartic_delta_positive_off
