-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Small56DetailsBounds
import Mathlib.Analysis.Complex.AbsMax

noncomputable section
open scoped Topology
open Polynomial
namespace Turan.Small56

open Filter Set Metric Certificate

private theorem factor_analytic (cs : List ℤ) (w : ℂ) :
    AnalyticAt ℂ (modelFactorProduct cs) w := by
  induction cs with
  | nil => exact analyticAt_const
  | cons c cs ih => exact (analyticAt_id.sub analyticAt_const).mul ih

private theorem factor_ne (cs : List ℤ) (w : ℂ) :
    modelFactorProduct cs w ≠ 0 ↔ ∀ n ∈ cs, w ≠ (n : ℂ)/1000000 := by
  induction cs with
  | nil => simp [modelFactorProduct]
  | cons c cs ih =>
    change (w - (c : ℂ)/1000000) * modelFactorProduct cs w ≠ 0 ↔ _
    simp [ih, sub_ne_zero]

private theorem eventually_factor_ne (cs : List ℤ) (w : ℂ) :
    ∀ᶠ z in 𝓝[≠] w, modelFactorProduct cs z ≠ 0 := by
  induction cs with
  | nil => simp [modelFactorProduct]
  | cons c cs ih =>
    have hc : ∀ᶠ z in 𝓝[≠] w, z ≠ (c : ℂ)/1000000 := by
      by_cases he : w = (c : ℂ)/1000000
      · rw [← he]
        exact self_mem_nhdsWithin
      · exact eventually_ne_nhdsWithin he
    filter_upwards [hc, ih] with z h₁ h₂ using mul_ne_zero (sub_ne_zero.mpr h₁) h₂

private theorem quotient_analytic (w : ℂ) (hw : ∀ n ∈ delta, w ≠ (n : ℂ)/1000000) :
    AnalyticAt ℂ modelQuotient w :=
  (factor_analytic gamma w).div (factor_analytic delta w) ((factor_ne delta w).2 hw)

private theorem normalized_factor_limit (cs : List ℤ) :
    Tendsto (fun z : ℂ => modelFactorProduct cs z / z^cs.length) (cocompact ℂ) (𝓝 1) := by
  have hz : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 := (eventually_cofinite_ne 0).filter_mono cocompact_le_cofinite
  induction cs with
  | nil => simp [modelFactorProduct]
  | cons c cs ih =>
    have hi : Tendsto (Inv.inv : ℂ → ℂ) (cocompact ℂ) (𝓝 0) := by
      rw [← cobounded_eq_cocompact]
      exact tendsto_inv₀_cobounded
    have hlin : Tendsto (fun z : ℂ => (z - (c : ℂ)/1000000) / z) (cocompact ℂ) (𝓝 1) := by
      have h := (tendsto_const_nhds (x := (1 : ℂ))).sub (hi.const_mul ((c : ℂ)/1000000))
      simp only [mul_zero, sub_zero] at h
      apply h.congr'
      filter_upwards [hz] with z hz'
      field_simp
    convert hlin.mul ih using 1
    · funext z
      change (z - (c : ℂ)/1000000) * modelFactorProduct cs z / z^(cs.length+1) = _
      rw [pow_succ, mul_comm (z ^ cs.length), div_mul_div_comm]
    · simp

theorem model_poles_and_infinity :
    (∀ w : ℂ, (Filter.Tendsto (fun z => ‖modelQuotient z‖) (𝓝[≠] w) Filter.atTop ↔
      ∃ n ∈ Certificate.delta, w = (n : ℂ)/1000000)) ∧
    (∀ w : ℂ, (∀ n ∈ Certificate.delta, w ≠ (n : ℂ)/1000000) →
      AnalyticAt ℂ modelQuotient w) ∧
    Filter.Tendsto modelQuotient (Filter.cocompact ℂ) (𝓝 1) := by
  refine ⟨?_, quotient_analytic, ?_⟩
  · intro w
    constructor
    · intro hp
      by_contra! hall
      exact not_tendsto_atTop_of_tendsto_nhds
        ((quotient_analytic w hall).continuousAt.norm.tendsto.mono_left nhdsWithin_le_nhds) hp
    · rintro ⟨n, hn, rfl⟩
      let w : ℂ := (n : ℂ)/1000000
      have hd : modelFactorProduct delta w = 0 := by
        by_contra h
        exact (factor_ne _ _ |>.1 h n hn) rfl
      have hg : modelFactorProduct gamma w ≠ 0 := by
        apply (factor_ne _ _).2
        intro m hm he
        have heq : (n : ℂ) = m := by simpa [w] using he
        have hnm : n = m := by exact_mod_cast heq
        have dis : Disjoint gamma.toFinset delta.toFinset := by decide
        exact Finset.disjoint_left.mp dis (List.mem_toFinset.mpr hm) (List.mem_toFinset.mpr (hnm ▸ hn))
      have hden : Tendsto (modelFactorProduct delta) (𝓝[≠] w) (𝓝[≠] 0) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_factor_ne _ _⟩
        rw [← hd]
        exact (factor_analytic _ _).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have hnum := (factor_analytic gamma w).continuousAt.norm.tendsto.mono_left
        (nhdsWithin_le_nhds (s := {w}ᶜ))
      simpa only [w, modelQuotient, div_eq_mul_inv, norm_mul, Function.comp_def] using
        hnum.pos_mul_atTop (norm_pos_iff.mpr hg) (tendsto_norm_inv_nhdsNE_zero_atTop.comp hden)
  · have h := (normalized_factor_limit gamma).div (normalized_factor_limit delta) one_ne_zero
    simp only [div_one] at h
    apply h.congr'
    filter_upwards [(eventually_cofinite_ne (0 : ℂ)).filter_mono cocompact_le_cofinite] with z hz
    exact div_div_div_cancel_right₀ (pow_ne_zero 12 hz) _ _

private theorem analytic_above (w : ℂ) (hw : 43/50 ≤ w.im) : AnalyticAt ℂ modelQuotient w := by
  apply quotient_analytic
  intro n _ he
  rw [he] at hw
  norm_num at hw

private theorem far_below (B : ℝ) (hB : 1 < B) :
    ∃ T : ℝ, ∀ w : ℂ, T ≤ ‖w‖ → ‖modelQuotient w‖ < B := by
  have hh := model_poles_and_infinity.2.2.norm
  simp only [norm_one] at hh
  have he := hh.eventually (gt_mem_nhds hB)
  rw [← cobounded_eq_cocompact] at he
  obtain ⟨T, _, ht⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp he
  exact ⟨T, fun w hw => ht hw⟩

theorem model_boundary_margin :
    ∃ B ∈ Set.Ioo (1 : ℝ) (9/5), ∀ w : ℂ, w.im = 43/50 → ‖modelQuotient w‖ ≤ B := by
  obtain ⟨T, ht⟩ := far_below (7/5) (by norm_num)
  let K := closedBall (0 : ℂ) T ∩ {w : ℂ | w.im = 43/50}
  have hk : IsCompact K := (isCompact_closedBall _ _).inter_right
    (isClosed_eq Complex.continuous_im continuous_const)
  by_cases hne : K.Nonempty
  · obtain ⟨z, hz, hmax⟩ := hk.exists_isMaxOn hne
      (f := fun w => ‖modelQuotient w‖)
      (fun w hw => (analytic_above w (le_of_eq hw.2.symm)).continuousAt.norm.continuousWithinAt)
    have hstrict := model_quotient_strict z (by rw [hz.2]; norm_num)
    refine ⟨max (7/5) ‖modelQuotient z‖, ⟨lt_of_lt_of_le (by norm_num) (le_max_left ..),
      max_lt (by norm_num) hstrict⟩, ?_⟩
    intro w hw
    by_cases hb : w ∈ closedBall (0 : ℂ) T
    · exact (hmax (show w ∈ K from ⟨hb, hw⟩)).trans (le_max_right ..)
    · simp [mem_closedBall] at hb
      exact (ht w hb.le).le.trans (le_max_left ..)
  · refine ⟨7/5, by constructor <;> norm_num, fun w hw => (ht w ?_).le⟩
    by_contra! h
    exact hne ⟨w, (by simpa [mem_closedBall] using h.le), hw⟩

private theorem factor_star (cs : List ℤ) (w : ℂ) :
    modelFactorProduct cs (star w) = star (modelFactorProduct cs w) := by
  induction cs with
  | nil => simp [modelFactorProduct]
  | cons c cs ih =>
    change (star w - (c : ℂ)/1000000) * modelFactorProduct cs (star w) =
      star ((w - (c : ℂ)/1000000) * modelFactorProduct cs w)
    rw [ih]
    simp

theorem model_half_disk_extension (B : ℝ) (hB : 1 < B)
    (hline : ∀ w : ℂ, w.im = 43/50 → ‖modelQuotient w‖ ≤ B) :
    let c : ℂ := (43/50) * Complex.I
    (∃ R₀ > (0 : ℝ), ∀ R ≥ R₀,
      (∀ w : ℂ, 43/50 ≤ w.im → ‖w-c‖ = R → ‖modelQuotient w‖ ≤ B) ∧
      (∀ w : ℂ, 43/50 ≤ w.im → ‖w-c‖ ≤ R → ‖modelQuotient w‖ ≤ B)) ∧
    (∀ w : ℂ, modelQuotient (star w) = star (modelQuotient w)) ∧
    (∀ w : ℂ, 43/50 ≤ |w.im| → ‖modelQuotient w‖ ≤ B) := by
  dsimp only
  let c : ℂ := (43/50)*Complex.I
  obtain ⟨T, ht⟩ := far_below B hB
  let R₀ := max 1 (T + ‖c‖)
  have hfar (z : ℂ) (hz : R₀ ≤ ‖z-c‖) : ‖modelQuotient z‖ ≤ B := by
    apply (ht z ?_).le
    linarith only [le_max_right (1:ℝ) (T+‖c‖), hz, norm_sub_le z c]
  let H := {z : ℂ | 43/50 ≤ z.im}
  have hH : IsClosed H := isClosed_le continuous_const Complex.continuous_im
  have hfill (R : ℝ) (hR : R₀ ≤ R) (z : ℂ) (hz : 43/50 ≤ z.im) (hd : ‖z-c‖ ≤ R) :
      ‖modelQuotient z‖ ≤ B := by
    let D := closedBall c R ∩ H
    have hcl : IsClosed D := isClosed_closedBall.inter hH
    apply Complex.norm_le_of_forall_mem_frontier_norm_le
      (U := D) (Metric.isBounded_closedBall.subset inter_subset_left)
    · apply DifferentiableOn.diffContOnCl
      rw [hcl.closure_eq]
      exact fun w hw => (analytic_above w hw.2).differentiableAt.differentiableWithinAt
    · intro w hw
      rcases frontier_inter_subset (closedBall c R) H hw with h | h
      · have hw' := mem_sphere.mp (frontier_closedBall_subset_sphere h.1)
        exact hfar _ (hR.trans_eq (by simpa [dist_eq_norm] using hw'.symm))
      · exact hline _ ((frontier_le_subset_eq continuous_const Complex.continuous_im h.2).symm)
    · exact subset_closure (show z ∈ D from ⟨by simpa [mem_closedBall, dist_eq_norm] using hd, hz⟩)
  have hs (w : ℂ) : modelQuotient (star w) = star (modelQuotient w) := by
    unfold modelQuotient
    rw [factor_star, factor_star]
    exact (map_div₀ (starRingEnd ℂ) _ _).symm
  refine ⟨⟨R₀, lt_of_lt_of_le zero_lt_one (le_max_left ..), fun R hR =>
    ⟨fun z _ hh => hfar z (hR.trans_eq hh.symm), hfill R hR⟩⟩, hs, ?_⟩
  have hup (z : ℂ) (hz : 43/50 ≤ z.im) :=
    hfill (max R₀ ‖z-c‖) (le_max_left ..) z hz (le_max_right ..)
  intro z hz
  rcases le_abs.mp hz with h | h
  · exact hup z h
  · have hc := hup (star z) (by simpa [Complex.star_def] using h)
    rwa [hs, norm_star] at hc

#print axioms model_poles_and_infinity
#print axioms model_boundary_margin
#print axioms model_half_disk_extension

end Turan.Small56

