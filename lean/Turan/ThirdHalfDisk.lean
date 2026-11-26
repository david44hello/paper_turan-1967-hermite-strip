module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.HalfDisk
public import Turan.CubicProofSteps
public import Turan.Third

@[expose] public section
namespace Turan

theorem third_half_disks :
    let c := (h:ℂ)*Complex.I
    (∃ R₀ > (0:ℝ), ∀ R ≥ R₀,
      (∀ z : ℂ, h ≤ z.im → ‖z-c‖=R → |(third z).im| < h) ∧
      (∀ z : ℂ, h ≤ z.im → ‖z-c‖≤R → |(third z).im| ≤ h)) ∧
    (∀ z : ℂ, h ≤ z.im → |(third z).im| ≤ h) ∧
    (∀ z : ℂ, h < z.im → |(third z).im| < h)  := by
  apply imaginary_half_disk_maximum third h h (by linarith [constants_spec.2.2.2.2.2])
  · exact fun z hz => (lemma_seven.1 z hz).1
  · exact fun z hz => (lemma_seven.1 z hz.ge).2.1
  · simpa only [Function.comp_def, Complex.zero_im] using Complex.continuous_im.continuousAt.tendsto.comp third_decay

end Turan
