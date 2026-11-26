module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Real Set Filter
open scoped Topology
namespace Turan

/-- Choose the interval between two consecutive zeros of the sine by following
the continuous angle to infinity, where it tends to zero. -/
theorem small34_branch_between (g : ℝ → ℝ) (A : ℝ) (hA : 0<A) (hπ : A<π)
    (hg : Continuous g) (hinf : Tendsto g atTop (𝓝 0))
    (hs : ∀ x, sin (g x-A)<0) (x : ℝ) : A-π<g x ∧ g x<A := by
  have h0 : 0 ∈ Ioo (A-π) A := ⟨by linarith,hA⟩
  obtain ⟨t,ht⟩ := (hinf.eventually (isOpen_Ioo.mem_nhds h0)).exists
  constructor
  · by_contra! hx
    obtain ⟨v,hv⟩ := intermediate_value_univ x t hg (show A-π ∈ Icc (g x) (g t) from ⟨hx,ht.1.le⟩)
    have hb := hs v
    rw [hv,show A-π-A = -π by ring] at hb
    simpa using hb
  · by_contra! hx
    obtain ⟨v,hv⟩ := intermediate_value_univ t x hg (show A ∈ Icc (g t) (g x) from ⟨ht.2.le,hx⟩)
    have hb := hs v
    simpa [hv] using hb

theorem small34_sin_sign (Z : ℂ) (θ q : ℝ) (hq : 0<q)
    (ha : (θ : Real.Angle)=(Z.arg : Real.Angle))
    (h : 0 < Z.re-q*Z.im) : Real.sin (θ-Real.arctan (1/q)) < 0 := by
  have hn : Z≠0 := by rintro rfl; simp at h
  have hnrm := norm_pos_iff.mpr hn
  have hc := Real.cos_arctan_pos (1/q)
  have hs := Real.tan_arctan (1/q)
  rw [Real.tan_eq_sin_div_cos,div_eq_iff hc.ne'] at hs
  have ht : Real.sin θ = Z.im/‖Z‖ := (congrArg Real.Angle.sin ha).trans (Complex.sin_arg Z)
  have hut : Real.cos θ = Z.re/‖Z‖ := (congrArg Real.Angle.cos ha).trans (Complex.cos_arg hn)
  rw [Real.sin_sub,ht,hut,hs]
  apply (mul_lt_mul_iff_left₀ (mul_pos hnrm hq)).mp
  field_simp [hnrm.ne',hq.ne']
  <;> nlinarith only [mul_pos h hc]

end Turan
