module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.DeltaCriterion
public import Turan.QuarticPencil

@[expose] public section

noncomputable section
namespace Turan

/-- A zero of the sign expression gives a square root whose imaginary part
is twice that of z and hence a real parameter in the quartic pencil. -/
theorem quartic_barrier_zero (w z : ℂ) (hw : 0<w.im ∧ 12*w^4+16*w^3+12*w^2-3=0)
    (hz : w.im≤z.im) (hB : quarticBarrier z=0) : z=w := by
  have hhalf : 1/2 < z.im := by linarith [(quartic_root_height w hw).1]
  obtain ⟨ρ,hρ⟩ := IsAlgClosed.exists_pow_nat_eq (quarticRatio z) (by decide : 0<2)
  obtain ⟨r,hr,hi⟩ : ∃ r : ℂ, r^2=quarticRatio z ∧ r.im=2*z.im := by
    rcases (quartic_barrier_criterion z ρ (hw.1.trans_le hz) hρ).1 hB with h|h
    · exact ⟨ρ,hρ,h⟩
    · exact ⟨-ρ,by simpa using hρ,by simp [h]⟩
  let d := r.re-2*z.re
  have hrepr : 2*z+(d:ℂ)=r := by
    apply Complex.ext
    · norm_num [Complex.add_re,Complex.mul_re,d]
    · norm_num [Complex.add_im,Complex.mul_im,hi]
  have hmul := (eq_div_iff (quartic_den_ne z hhalf)).mp hr
  have hpen : (2*z+(d:ℂ))^2*(4*z^2+4*z+2)-(4*z^4-4*z^2+3)=0 := by
    rw [hrepr]
    exact sub_eq_zero.mpr hmul
  have hd : d=0 := by
    by_contra hd'
    exact lemma_eighteen w hw d hd' z hz hpen
  rw [hd] at hpen
  simp only [Complex.ofReal_zero,add_zero] at hpen
  apply quartic_upper_root.unique _ hw
  exact ⟨hw.1.trans_le hz,by linear_combination hpen⟩

end Turan
