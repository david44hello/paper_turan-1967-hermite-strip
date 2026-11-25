-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.CaratheodoryBound
import Turan.CaratheodoryCoefficient

open Metric Filter
open scoped Topology
namespace Turan

theorem caratheodory_all_orders (g : ℂ → ℂ) (z : ℂ) (R : ℝ) (hr : 0 < R)
    (hg : DifferentiableOn ℂ g (ball z R)) (hpos : ∀ w ∈ ball z R, 0 ≤ (g w).re)
    (l : ℕ) (hl : 1 ≤ l) :
    ‖iteratedDeriv l g z‖ ≤ 2*(l.factorial:ℝ)*(g z).re/R^l := by
  have hfac : (0:ℝ) < l.factorial := by exact_mod_cast l.factorial_pos
  have ht : ContinuousAt (fun r : ℝ => 2*(l.factorial:ℝ)*(g z).re/r^l) R :=
    continuousAt_const.div (continuousAt_id.pow _) (pow_ne_zero _ hr.ne')
  suffices h : ∀ᶠ r in 𝓝[<] R, ‖iteratedDeriv l g z‖ ≤ 2*(l.factorial:ℝ)*(g z).re/r^l by
    exact ge_of_tendsto ht.continuousWithinAt h
  filter_upwards [Ioo_mem_nhdsLT hr] with r h
  have hb := caratheodory_average_bound g z r R h.1 h.2 hg hpos l hl
  rw [caratheodory_coefficient g z r R h.1 h.2 hg l, norm_div, Complex.norm_natCast, div_le_iff₀ hfac] at hb
  convert hb using 1 <;> ring

end Turan
