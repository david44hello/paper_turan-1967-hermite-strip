-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs
open Filter Metric
open scoped Topology
namespace Turan

theorem imaginary_half_disk_maximum (f : ℂ → ℂ) (y B : ℝ) (hB : 0 < B)
    (ha : ∀ z : ℂ, y ≤ z.im → AnalyticAt ℂ f z)
    (hline : ∀ z : ℂ, z.im=y → |(f z).im| ≤ B)
    (hinf : Tendsto (fun z => (f z).im) (cocompact ℂ) (𝓝 0)) :
    let c := (y:ℂ)*Complex.I
    (∃ R₀ > (0:ℝ), ∀ R ≥ R₀,
      (∀ z : ℂ, y ≤ z.im → ‖z-c‖=R → |(f z).im| < B) ∧
      (∀ z : ℂ, y ≤ z.im → ‖z-c‖≤R → |(f z).im| ≤ B)) ∧
    (∀ z : ℂ, y ≤ z.im → |(f z).im| ≤ B) ∧
    (∀ z : ℂ, y < z.im → |(f z).im| < B) := by sorry

end Turan
