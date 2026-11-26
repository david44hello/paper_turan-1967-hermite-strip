module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.CubicProofSteps

@[expose] public section
namespace Turan

theorem contact_implies_alignment (k : ℝ) (hk : 0 < k) (U V S : ℂ)
    (hU : k ≤ U.im) (hV : k ≤ V.im) (hs : S^2=U*V) (hc : S.im=k) :
    U.im=k ∧ V.im=k ∧ ‖U‖*‖V‖=U.re*V.re+U.im*V.im := by
  obtain ⟨he, hle⟩ := square_root_imaginary_identity U V S hs
  rw [hc] at he hle
  have hUpos := hk.trans_le hU
  have hVpos := hk.trans_le hV
  have hu : U.im = k := by
    apply le_antisymm _ hU
    by_contra! hbad
    nlinarith only [hle, mul_le_mul_of_nonneg_left hV hUpos.le,
      mul_lt_mul_of_pos_right hbad hk]
  have hv : V.im = k := by
    apply le_antisymm _ hV
    rw [hu, sq] at hle
    exact (mul_le_mul_iff_right₀ hk).mp hle
  refine ⟨hu, hv, ?_⟩
  rw [Complex.mul_re, hu, hv] at he
  rw [hu, hv]
  linarith only [he]

end Turan
