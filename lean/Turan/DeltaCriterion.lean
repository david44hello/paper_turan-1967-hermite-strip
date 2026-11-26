module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.DeltaDefs
public import Turan.QuarticRoot

@[expose] public section

noncomputable section
namespace Turan

theorem quartic_den_ne (z : ℂ) (hz : 1/2 < z.im) : quarticDen z ≠ 0 := by
  have hfac : quarticDen z=(2*z+1-Complex.I)*(2*z+1+Complex.I) := by
    unfold quarticDen; linear_combination Complex.I_sq
  rw [hfac]
  apply mul_ne_zero
  · intro he
    have hi := congrArg Complex.im he
    norm_num [Complex.sub_im,Complex.add_im,Complex.mul_im] at hi
    linarith
  · intro he
    have hi := congrArg Complex.im he
    norm_num [Complex.add_im,Complex.mul_im] at hi
    linarith

/-- The sign expression before multiplication by the positive denominator factor. -/
def quarticBarrier (z : ℂ) : ℝ :=
  16*z.im^2*((quarticRatio z).re+4*z.im^2)-(quarticRatio z).im^2

theorem quartic_barrier_criterion (z ρ : ℂ) (hz : 0 < z.im) (hρ : ρ^2=quarticRatio z) :
    quarticBarrier z=0 ↔ ρ.im=2*z.im ∨ ρ.im= -2*z.im := by
  have hf : quarticBarrier z =
      4*(2*z.im-ρ.im)*(2*z.im+ρ.im)*(ρ.re^2+4*z.im^2) := by
    unfold quarticBarrier
    rw [← hρ]
    simp only [pow_two,Complex.mul_re,Complex.mul_im]
    ring
  have hp : 0 < ρ.re^2+4*z.im^2 := by positivity
  rw [hf]
  simp only [mul_eq_zero,OfNat.ofNat_ne_zero,false_or, hp.ne',or_false]
  constructor
  · rintro (h|h)
    · left; linarith
    · right; linarith
  · rintro (h|h)
    · left; linarith
    · right; linarith

theorem quartic_delta_criterion (w : ℂ) (hw : 0 < w.im ∧ 12*w^4+16*w^3+12*w^2-3=0)
    (s : ℝ) (ρ : ℂ) (hρ : ρ^2=quarticRatio ⟨s-1/2,w.im⟩) :
    quarticDelta w.im s = 0 ↔ (ρ.im=2*w.im ∨ ρ.im= -2*w.im) := by
  let z : ℂ := ⟨s-1/2,w.im⟩
  have hz : 1/2 < z.im := by change 1/2<w.im; linarith [(quartic_root_height w hw).1]
  have hnorm := norm_pos_iff.mpr (quartic_den_ne z hz)
  change (‖quarticDen z‖^4/(4*w.im^2))*quarticBarrier z = 0 ↔ _
  have hfactor : 0 < ‖quarticDen z‖^4/(4*w.im^2) := by have := hw.1; positivity
  rw [mul_eq_zero, or_iff_right hfactor.ne']
  exact quartic_barrier_criterion z ρ hw.1 hρ

end Turan
