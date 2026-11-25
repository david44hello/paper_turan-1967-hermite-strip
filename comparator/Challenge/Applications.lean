-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Challenge.Small56SourceDefs
open scoped Topology
namespace Turan

theorem third_half_disks :
    let c := (h:ℂ)*Complex.I
    (∃ R₀ > (0:ℝ), ∀ R ≥ R₀,
      (∀ z : ℂ, h ≤ z.im → ‖z-c‖=R → |(third z).im| < h) ∧
      (∀ z : ℂ, h ≤ z.im → ‖z-c‖≤R → |(third z).im| ≤ h)) ∧
    (∀ z : ℂ, h ≤ z.im → |(third z).im| ≤ h) ∧
    (∀ z : ℂ, h < z.im → |(third z).im| < h) := by sorry

theorem small56_strict_exterior (s : List Small56.Entry)
    (hg : s.map Small56.Entry.G = Small56.Certificate.gamma)
    (hd : s.map Small56.Entry.D = Small56.Certificate.delta)
    (w : ℂ) (hw : 43/50 ≤ |w.im|) :
    ‖(s.map (fun e => (w-e.g)/(w-e.d))).prod‖ < (181/100:ℝ) := by sorry

end Turan
