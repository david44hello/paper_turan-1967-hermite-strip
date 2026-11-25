-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.StripDetailDefs
import Mathlib.Analysis.Complex.AbsMax
noncomputable section
open Set Metric
namespace Turan.StripDetails

theorem strip_rectangle_maximum (f : ℂ → ℂ) (B : ℝ) (hB : 0 < B)
    (ha : ∀ z : ℂ, |z.im| ≤ height → AnalyticAt ℂ f z)
    (hline : ∀ z : ℂ, |z.im| = height → ‖f z‖ < B)
    (hdecay : ∀ ε > (0:ℝ), ∃ R : ℝ, ∀ z : ℂ, |z.im| ≤ height → R ≤ |z.re| → ‖f z‖ < ε) :
    (∃ R₀ > (0:ℝ), ∀ R ≥ R₀, ∃ M < B, ∀ z : ℂ, |z.re| ≤ R → |z.im| ≤ height → ‖f z‖ ≤ M) ∧
    ∀ z : ℂ, |z.im| ≤ height → ‖f z‖ < B  := by
  obtain ⟨T,hT⟩ := hdecay B hB
  let R₀ := max 1 T
  have hR₀ : 0 < R₀ := zero_lt_one.trans_le (le_max_left ..)
  have hrect (R : ℝ) (hR : R₀ ≤ R) : ∃ M < B, ∀ z : ℂ, |z.re| ≤ R → |z.im| ≤ height → ‖f z‖ ≤ M := by
    let X := {z : ℂ | |z.re| ≤ R}
    let Y := {z : ℂ | |z.im| ≤ height}
    have hX : IsClosed X := isClosed_le Complex.continuous_re.abs continuous_const
    have hY : IsClosed Y := isClosed_le Complex.continuous_im.abs continuous_const
    have hcl := (hX.inter hY).closure_eq
    have hne : (X ∩ Y).Nonempty := ⟨0, by
      change |(0:ℂ).re| ≤ R ∧ |(0:ℂ).im| ≤ height
      simpa using And.intro (hR₀.le.trans hR) (by norm_num : (0:ℝ) ≤ height)⟩
    have hbd : Bornology.IsBounded (X ∩ Y) := Metric.isBounded_closedBall.subset
      (show X ∩ Y ⊆ closedBall 0 (R+height) by
        intro z hz
        rw [mem_closedBall_zero_iff]
        exact (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add hz.1 hz.2))
    obtain ⟨w,hw,hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm hbd hne
      (f := f) (by
        apply DifferentiableOn.diffContOnCl
        rw [hcl]
        exact fun z hz => (ha z hz.2).differentiableAt.differentiableWithinAt)
    have hsmall : ‖f w‖ < B := by
      rcases frontier_inter_subset X Y hw with hl | hr
      · have he := frontier_le_subset_eq Complex.continuous_re.abs continuous_const hl.1
        exact hT w (by change w ∈ Y; exact hY.closure_eq ▸ hl.2) ((le_max_right 1 T).trans (hR.trans_eq he.symm))
      · exact hline w (frontier_le_subset_eq Complex.continuous_im.abs continuous_const hr.2)
    exact (show ∃ M < B, ∀ z : ℂ, |z.re| ≤ R → |z.im| ≤ height → ‖f z‖ ≤ M from
      ⟨‖f w‖,hsmall,fun z hx hy => hmax (subset_closure (show z ∈ X ∩ Y from ⟨hx,hy⟩))⟩)
  refine ⟨⟨R₀,hR₀,hrect⟩, ?_⟩
  intro z hz
  obtain ⟨M,hM,hle⟩ := hrect (max R₀ |z.re|) (le_max_left ..)
  exact (hle z (le_max_right ..) hz).trans_lt hM

end Turan.StripDetails
