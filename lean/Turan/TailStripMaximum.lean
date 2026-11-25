-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.TailStripFactors

noncomputable section
namespace Turan.TailStrip
open Complex Set Filter
open scoped Topology

private theorem strip_maximum {f : ℂ → ℂ} {C : ℝ}
    (hd : DifferentiableOn ℂ f strip) (hg : farBound f)
    (hline : ∀ z : ℂ, |z.im| = height → ‖f z‖ ≤ C) {w : ℂ} (hw : w ∈ strip) :
    ‖f w‖ ≤ C := by
  have hs : closure (Complex.im ⁻¹' Ioo (-height) height) = strip := by
    rw [Complex.closure_preimage_im, closure_Ioo (by norm_num : -height ≠ height)]
    ext; exact abs_le.symm
  apply PhragmenLindelof.horizontal_strip (a := -height) (b := height)
  · apply DifferentiableOn.diffContOnCl; rwa [hs]
  · obtain ⟨K,R,h⟩ := hg
    refine ⟨0, div_pos Real.pi_pos (by norm_num), 0, Asymptotics.isBigO_iff.mpr ⟨K, ?_⟩⟩
    have hR : ∀ᶠ z : ℂ in comap (abs ∘ Complex.re) atTop, R ≤ |z.re| :=
      tendsto_comap.eventually (eventually_ge_atTop R)
    rw [eventually_inf_principal]
    filter_upwards [hR] with z hz hi
    have hy : -height < z.im ∧ z.im < height := hi
    simpa using h z hz (abs_le.mpr ⟨hy.1.le, hy.2.le⟩)
  · exact fun z hz => hline z (by simp [hz, abs_of_nonneg (by norm_num : 0 ≤ height)])
  · exact fun z hz => hline z (by simp [hz, abs_of_nonneg (by norm_num : 0 ≤ height)])
  · exact (abs_le.mp hw).1
  · exact (abs_le.mp hw).2

/-- Each distinct real zero on the strip contributes its own strip Schwarz factor. -/
theorem maximum_with_zeros (t : Finset ℂ) (f : ℂ → ℂ) (C : ℝ)
    (hd : DifferentiableOn ℂ f strip) (hg : farBound f)
    (hline : ∀ z : ℂ, |z.im| = height → ‖f z‖ ≤ C)
    (hnodes : ∀ s ∈ t, s.im = 0 ∧ f s = 0) (w : ℂ) (hw : w ∈ strip) :
    ‖f w‖ ≤ C * ∏ s ∈ t, ‖factor s.re w‖ := by
  classical
  induction t using Finset.induction_on generalizing f with
  | empty => simpa using strip_maximum hd hg hline hw
  | @insert s t hst ih =>
    obtain ⟨him,hzero⟩ := hnodes s (Finset.mem_insert_self ..)
    have hreal : (s.re : ℂ) = s := Complex.ext (by simp) (by simp [him])
    obtain ⟨g,hgd,he⟩ := remove_factor hd s.re (hreal.symm ▸ hzero)
    have hgl (z : ℂ) (hz : |z.im| = height) : ‖g z‖ ≤ C := by
      simpa only [he z hz.le, norm_mul, factor_line s.re hz, mul_one] using hline z hz
    have hgn (x : ℂ) (hx : x ∈ t) : x.im = 0 ∧ g x = 0 := by
      obtain ⟨hxi,hxf⟩ := hnodes x (Finset.mem_insert_of_mem hx)
      have hxs : x ∈ strip := by change |x.im| ≤ height; rw [hxi]; norm_num
      rw [he x hxs] at hxf
      exact ⟨hxi, (mul_eq_zero.mp hxf).resolve_right
        (factor_ne _ hxs (by rw [hreal]; exact ne_of_mem_of_not_mem hx hst))⟩
    have hb := ih g hgd (farBound_remove hg s.re he) hgl hgn
    rw [he w hw, norm_mul, Finset.prod_insert hst]
    calc
      _ ≤ (C * ∏ x ∈ t, ‖factor x.re w‖) * ‖factor s.re w‖ :=
        mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = _ := by ring

end Turan.TailStrip
