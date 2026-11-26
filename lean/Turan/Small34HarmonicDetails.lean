module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Small34EnvelopeDefs
public import Turan.Small34AngleBound
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

@[expose] public section

noncomputable section
open Polynomial Real Set Filter Bornology Metric InnerProductSpace
open scoped Topology
namespace Turan

private def endpointRatio (l r : ℝ) (z : ℂ) : ℂ :=
  ((r:ℂ)-z)/((l:ℂ)-z)

/-- Positivity and the strict upper bound π fix the real representative of the angle. -/
private theorem angle_eq_arg {l r : ℝ} (hlr : l < r) {z : ℂ} (hz : 0 < z.im) :
    small34Angle l r z = (endpointRatio l r z).arg := by
  have h := congrArg Real.Angle.toReal (small34Angle_arg_quotient l r z hz.ne')
  obtain ⟨hpos,hpi⟩ := small34Angle_pos hlr hz
  rwa [Real.Angle.toReal_coe_eq_self_iff.mpr ⟨by linarith [pi_pos], hpi.le⟩,
    Complex.arg_coe_angle_toReal_eq_arg] at h

private theorem ratio_log_analytic {l r : ℝ} (hlr : l < r) {z : ℂ} (hz : 0 < z.im) :
    AnalyticAt ℂ (fun w => Complex.log (endpointRatio l r w)) z := by
  have hne : (l:ℂ)-z ≠ 0 := by
    intro h
    rw [← sub_eq_zero.mp h] at hz
    simp at hz
  have hn := Complex.normSq_pos.mpr hne
  have him : (endpointRatio l r z).im =
      z.im*(r-l) / Complex.normSq ((l:ℂ)-z) := by
    simp only [endpointRatio, Complex.div_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_sub, ← sub_div]
    ring
  have hs : endpointRatio l r z ∈ Complex.slitPlane :=
    Or.inr (by rw [him]; exact (div_pos (mul_pos hz (sub_pos.mpr hlr)) hn).ne')
  apply AnalyticAt.clog _ hs
  unfold endpointRatio
  exact (analyticAt_const.sub analyticAt_id).div (analyticAt_const.sub analyticAt_id) hne

/-- The endpoint quotient extends to 1 at infinity in the coordinate w = 1/z. -/
private theorem ratio_at_infty (l r : ℝ) :
    Tendsto (endpointRatio l r) (cobounded ℂ) (𝓝 1) := by
  let h := fun w : ℂ => ((r:ℂ)*w-1)/((l:ℂ)*w-1)
  have hcont : ContinuousAt h 0 := by unfold h; fun_prop (disch := norm_num)
  have hlim : Tendsto (fun z : ℂ => h z⁻¹) (cobounded ℂ) (𝓝 1) := by
    simpa only [Function.comp_def, show h 0 = 1 by simp [h]] using
      hcont.tendsto.comp (Filter.tendsto_inv₀_cobounded (α := ℂ))
  apply hlim.congr'
  filter_upwards [eventually_ne_cobounded (0:ℂ)] with z hz
  dsimp [h, endpointRatio]
  rw [show (r:ℂ)*z⁻¹-1 = ((r:ℂ)-z)*z⁻¹ by rw [sub_mul, mul_inv_cancel₀ hz],
      show (l:ℂ)*z⁻¹-1 = ((l:ℂ)-z)*z⁻¹ by rw [sub_mul, mul_inv_cancel₀ hz],
      mul_div_mul_right _ _ (inv_ne_zero hz)]

theorem small34_angle_harmonic_decay {l r : ℝ} (hlr : l < r) :
    InnerProductSpace.HarmonicOnNhd (small34Angle l r) {z : ℂ | 0 < z.im} ∧
    ContinuousOn (small34Angle l r) {z : ℂ | 5/7 ≤ z.im} ∧
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ,
      0 < z.im → R ≤ ‖z‖ → |small34Angle l r z| < ε := by
  have hh : HarmonicOnNhd (small34Angle l r) {z : ℂ | 0 < z.im} := by
    intro z hz
    apply (harmonicAt_congr_nhds (f₂ := fun w => (Complex.log (endpointRatio l r w)).im) ?_).mpr
      (ratio_log_analytic hlr hz).harmonicAt_im
    filter_upwards [((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)] with w hw
    simpa only [Complex.log_im] using angle_eq_arg hlr hw
  refine ⟨hh, hh.continuousOn.mono (fun z (hz : 5/7 ≤ z.im) => show 0 < z.im by linarith), ?_⟩
  intro ε hε
  have hlim : Tendsto (fun z => (endpointRatio l r z).arg) (cobounded ℂ) (𝓝 0) := by
    simpa only [Function.comp_def, Complex.arg_one] using
      (Complex.continuousAt_arg (x := 1) (Or.inl (by norm_num))).tendsto.comp (ratio_at_infty l r)
  obtain ⟨R, _, hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp ((Metric.tendsto_nhds.mp hlim) ε hε)
  refine ⟨max 1 R, lt_of_lt_of_le zero_lt_one (le_max_left ..), fun z hz hn => ?_⟩
  rw [angle_eq_arg hlr hz]
  simpa [Real.dist_eq] using hR ((le_max_right 1 R).trans hn)

#print axioms small34_angle_harmonic_decay

private theorem angle_boundary_limit {l r : ℝ} (hlr : l < r) :
    Tendsto (fun x : ℝ => small34Angle l r ⟨x, 5/7⟩) (cocompact ℝ) (𝓝 0) := by
  rw [← Metric.cobounded_eq_cocompact]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨R, _, hR⟩ := (small34_angle_harmonic_decay hlr).2.2 ε hε
  filter_upwards [eventually_cobounded_le_norm (E := ℝ) R] with x hx
  have hn : R ≤ ‖(⟨x,5/7⟩ : ℂ)‖ := hx.trans (Complex.abs_re_le_norm ⟨x,5/7⟩)
  simpa [Real.dist_eq] using hR ⟨x,5/7⟩ (by norm_num) hn

/-- Adjoining the limit gives a compact set containing the entire closed range. -/
private theorem extrema_in_insert {f : ℝ → ℝ} {a : ℝ} (hc : Continuous f)
    (hl : Tendsto f (cocompact ℝ) (𝓝 a)) :
    sSup (range f) ∈ insert a (range f) ∧ sInf (range f) ∈ insert a (range f) := by
  have hk := hl.isCompact_insert_range_of_cocompact hc
  have sub := subset_insert a (range f)
  have hcl := closure_minimal sub hk.isClosed
  exact ⟨hcl (csSup_mem_closure (range_nonempty _) (hk.bddAbove.mono sub)),
    hcl (csInf_mem_closure (range_nonempty _) (hk.bddBelow.mono sub))⟩

theorem small34_boundary_extrema :
    let u := fun x : ℝ => small34GUpper ⟨x, 5/7⟩
    let v := fun x : ℝ => small34GLower ⟨x, 5/7⟩
    Tendsto (fun x => (u x, v x)) (atBot ⊔ atTop) (𝓝 (0, 0)) ∧
    sSup (range fun x => u x - arctan (1/44)) ∈ Ioo (-π) 0 ∧
    arctan (1/14) - π < sInf (range v) := by
  let u := fun x : ℝ => small34GUpper ⟨x, 5/7⟩
  let v := fun x : ℝ => small34GLower ⟨x, 5/7⟩
  have cu : Continuous u := by unfold u small34GUpper small34Angle; dsimp; fun_prop
  have cv : Continuous v := by unfold v small34GLower small34Angle; dsimp; fun_prop
  have weighted {a b c d e f : ℝ} (hab : a < b) (hcd : c < d) (hef : e < f) :
      Tendsto (fun x : ℝ => 5 * small34Angle a b ⟨x,5/7⟩ - 4 * small34Angle c d ⟨x,5/7⟩ +
        2 * small34Angle e f ⟨x,5/7⟩) (cocompact ℝ) (𝓝 0) := by
    simpa only [mul_zero, sub_zero, add_zero] using
      ((((angle_boundary_limit hab).const_mul 5).sub ((angle_boundary_limit hcd).const_mul 4)).add
        ((angle_boundary_limit hef).const_mul 2))
  have hu : Tendsto u (cocompact ℝ) (𝓝 0) :=
    weighted (by norm_num : (-1.311446:ℝ) < -0.096251) (by norm_num : (-1.553002:ℝ) < 1.794300)
      (by norm_num : (-0.308319:ℝ) < 2.074718)
  have hv : Tendsto v (cocompact ℝ) (𝓝 0) :=
    weighted (by norm_num : (-1.311445:ℝ) < -0.096252) (by norm_num : (-1.553003:ℝ) < 1.794301)
      (by norm_num : (-0.308318:ℝ) < 2.074717)
  have bu (x : ℝ) : -π + arctan (1/14) < u x ∧ u x < arctan (1/44) := by
    apply small34_weighted_bound (-1.311446) (-0.096251) (-1.553002) 1.794300 (-0.308319) 2.074718
      (z := ⟨x,5/7⟩) <;> norm_num [mem_Icc]
  have bv (x : ℝ) : -π + arctan (1/14) < v x ∧ v x < arctan (1/44) := by
    apply small34_weighted_bound (-1.311445) (-0.096252) (-1.553003) 1.794301 (-0.308318) 2.074717
      (z := ⟨x,5/7⟩) <;> norm_num [mem_Icc]
  have hA : 0 < arctan (1/44) := arctan_pos.mpr (by norm_num)
  have hAB : arctan (1/44) < arctan (1/14) := arctan_strictMono (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [← cocompact_eq_atBot_atTop]
    exact hu.prodMk_nhds hv
  · have h := (extrema_in_insert (f := fun x => u x - arctan (1/44))
        (cu.sub continuous_const) (hu.sub_const (arctan (1/44)))).1
    rcases mem_insert_iff.mp h with h | ⟨x,h⟩
    · change sSup (range fun x => u x - arctan (1/44)) ∈ Ioo (-π) 0
      rw [h]
      exact ⟨by linarith [arctan_lt_pi_div_two (1/44), pi_pos], by linarith⟩
    · change sSup (range fun x => u x - arctan (1/44)) ∈ Ioo (-π) 0
      rw [← h]
      exact ⟨by linarith [(bu x).1], by linarith [(bu x).2]⟩
  · have h := (extrema_in_insert cv hv).2
    rcases mem_insert_iff.mp h with h | ⟨x,h⟩
    · change arctan (1/14) - π < sInf (range v)
      rw [h]
      linarith [arctan_lt_pi_div_two (1/14), pi_pos]
    · change arctan (1/14) - π < sInf (range v)
      rw [← h]
      linarith [(bv x).1]

#print axioms small34_boundary_extrema

end Turan
