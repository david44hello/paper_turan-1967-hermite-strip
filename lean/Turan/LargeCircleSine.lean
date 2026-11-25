-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Sturm
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Set Filter
open scoped Topology
namespace Turan

/-- Sine comparison on the rescaled radius, with unit initial slope. -/
theorem largeCircle_sine {y v q : ℝ → ℝ}
    (hy : ∀ t, HasDerivAt y (v t) t) (hv : ∀ t, HasDerivAt v (-q t * y t) t)
    (hy0 : y 0 = 0) (hv0 : v 0 = 1) (hq : ∀ t ∈ Icc 0 1, q t ≤ 1 / 4) :
    2 * Real.sin (1 / 2) ≤ y 1 := by
  -- Compare against the sine vanishing at the right endpoint T.
  have compare (T : ℝ) (hT : T ∈ Icc 0 1) (hn : ∀ t ∈ Icc 0 T, 0 ≤ y t) :
      2 * Real.sin (T / 2) ≤ y T := by
    let θ (t : ℝ) := (T - t) / 2
    let W (t : ℝ) := 2 * v t * Real.sin (θ t) + y t * Real.cos (θ t)
    have hθ (t : ℝ) : HasDerivAt θ (-(1/2)) t := by
      simpa [θ, neg_div] using ((hasDerivAt_id t).const_sub T).div_const 2
    have hW (t : ℝ) : HasDerivAt W (2 * (1/4 - q t) * y t * Real.sin (θ t)) t := by
      convert (((hv t).const_mul 2).mul (hθ t).sin).add ((hy t).mul (hθ t).cos) using 1
      ring
    have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T)
      (fun t _ => (hW t).continuousAt.continuousWithinAt) (fun t _ => (hW t).hasDerivWithinAt)
      (fun t ht => by
        have ht' : t ∈ Icc 0 T := interior_subset ht
        have hs := Real.sin_nonneg_of_nonneg_of_le_pi
          (show 0 ≤ θ t by dsimp [θ]; linarith [ht'.2])
          (show θ t ≤ Real.pi by dsimp [θ]; linarith [ht'.1, hT.2, Real.pi_gt_three])
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
          (sub_nonneg.mpr (hq t ⟨ht'.1, ht'.2.trans hT.2⟩))) (hn t ht')) hs)
    simpa [W, θ, hy0, hv0] using
      hmono (left_mem_Icc.mpr hT.1) (right_mem_Icc.mpr hT.1) hT.1
  have hc : Continuous y := continuous_iff_continuousAt.mpr fun t => (hy t).continuousAt
  let S := {t : ℝ | 0 ≤ y t}
  have hS : Icc 0 1 ⊆ S := by
    apply IsClosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset
      ((isClosed_le continuous_const hc).inter isClosed_Icc) (show 0 ≤ y 0 by rw [hy0])
    intro t ht hi
    rcases ht.1.eq_or_lt with h | h
    · subst t
      have hsl := ((hasDerivAt_iff_tendsto_slope_left_right.mp (hy 0)).2).eventually
        (Ioi_mem_nhds (show 0 < v 0 by rw [hv0]; norm_num))
      filter_upwards [hsl, self_mem_nhdsWithin] with r hr hp
      change 0 < slope y 0 r at hr
      rw [slope_def_field, hy0, sub_zero, sub_zero] at hr
      exact ((div_pos_iff_of_pos_right (show 0 < r from hp)).mp hr).le
    · have hb := compare t ⟨ht.1, ht.2.le⟩ (fun r hr => hi hr)
      have hp := Real.sin_pos_of_pos_of_lt_pi (show 0 < t / 2 by positivity)
        (by linarith [ht.2, Real.pi_gt_three])
      have hypos : 0 < y t := by linarith
      exact Filter.mem_of_superset
        (nhdsWithin_le_nhds (hc.continuousAt.eventually (Ioi_mem_nhds hypos)))
        (fun r hr => (show 0 < y r from hr).le)
  exact compare 1 (by simp) (fun r hr => hS hr)

end Turan
