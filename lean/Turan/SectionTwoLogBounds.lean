module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.SectionTwoLimitsDefs
public import Turan.SectionTwoGrowth

@[expose] public section

noncomputable section
open Polynomial Filter Metric InnerProductSpace
open scoped Topology BigOperators Classical
namespace Turan.SectionTwo
variable {s : ℕ}

theorem scaledLog_harmonic (p : Polynomial ℂ) (ω : ℝ) (z : ℂ) (hz : p.eval z ≠ 0) :
    HarmonicAt (scaledLog ω p) z := by
  have h := (p.differentiable.analyticAt z).harmonicAt_log_norm hz
  unfold scaledLog
  simpa [div_eq_inv_mul, Pi.smul_def, smul_eq_mul] using h.const_smul (c := ω⁻¹)

theorem normalized_log_bounds (hs : s ∈ Set.Icc 2 4) (k : ℕ → Fin s → ℕ)
    (a : ℕ → Fin s → ℂ) (hω : Tendsto (fun j => frequency (k j)) atTop atTop)
    (hjet : ∀ᶠ j in atTop, unitInitialJet (k j) (slotSum (k j) (a j)))
    (he : escapesDisks (fun j => slotSum (k j) (a j))) :
    let u := fun j => scaledLog (frequency (k j)) (slotSum (k j) (a j))
    let b := fun j => -Real.log (((2*s-1).factorial : ℕ) : ℝ) / frequency (k j)
    Tendsto b atTop (𝓝 0) ∧ ∀ R : ℝ, 0 < R → ∃ C₀ : ℝ, ∀ᶠ j in atTop,
      HarmonicOnNhd (u j) (ball 0 R) ∧ (∀ z ∈ closedBall 0 R, u j z ≤ C₀) ∧
      ∃ z ∈ closedBall (0 : ℂ) 1, b j ≤ u j z := by
  dsimp only
  constructor
  · exact tendsto_const_nhds.div_atTop hω
  intro R hR
  obtain ⟨C₀, _, hg⟩ := normalized_growth s hs R hR.le
  refine ⟨C₀, ?_⟩
  filter_upwards [hjet, hω.eventually_ge_atTop 1, he R hR] with j hj hfreq hnon
  have hpos : 0 < frequency (k j) := zero_lt_one.trans_le hfreq
  have hL : 1 ≤ topLambda (k j) := by nlinarith only [frequency_sq (k j), hfreq, sq_nonneg (frequency (k j)-1)]
  obtain ⟨hupper, z, hz, hlower⟩ := hg (k j) (a j) hL hj
  refine ⟨fun t ht => scaledLog_harmonic _ _ _ (hnon t (by simpa using (mem_ball.mp ht).le)), ?_,
    z, by simpa using hz, ?_⟩
  · intro w hw
    have hw' : ‖w‖ ≤ R := by simpa using mem_closedBall.mp hw
    apply (div_le_iff₀ hpos).mpr
    exact (Real.log_le_iff_le_exp (norm_pos_iff.mpr (hnon w hw'))).mpr (hupper w hw')
  · apply (div_le_div_iff_of_pos_right hpos).mpr
    have hf : 0 < (((2*s-1).factorial : ℕ) : ℝ) := by positivity
    rw [one_div] at hlower
    simpa only [Real.log_inv] using Real.log_le_log (inv_pos.mpr hf) hlower

end Turan.SectionTwo
