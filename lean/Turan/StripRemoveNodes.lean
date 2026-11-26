module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.StripDivisor
public import Turan.StripFactorDetails
public import Mathlib.Analysis.Complex.AbsMax

@[expose] public section
noncomputable section
open Set Metric
namespace Turan.StripDetails

theorem strip_remove_nodes (S : Finset ℝ) (f : ℂ → ℂ)
    (ha : ∀ z : ℂ, |z.im| < 87/100 → AnalyticAt ℂ f z)
    (hzero : ∀ s ∈ S, f (s:ℂ)=0) :
    ∃ V : ℂ → ℂ, (∀ z : ℂ, |z.im| < 87/100 → AnalyticAt ℂ V z) ∧
      (∀ z : ℂ, |z.im| < 87/100 → f z = V z * ∏ s ∈ S, factor s z) ∧
      ∀ z : ℂ, |z.im| = height → ‖V z‖ = ‖f z‖  := by
  classical
  let D := {z : ℂ | |z.im| < 87/100}
  have hopen : IsOpen D := isOpen_lt Complex.continuous_im.abs continuous_const
  have hremove (s : ℝ) (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g D) (hgz : g s=0) :
      ∃ q : ℂ → ℂ, DifferentiableOn ℂ q D ∧ ∀ z ∈ D, g z=q z*factor s z := by
    have hs : D ∈ nhds (s:ℂ) := hopen.mem_nhds (by change |(s:ℂ).im| < _; norm_num)
    obtain ⟨_,_,hzero,hd⟩ := strip_factor_divisor s
    have h0 : factor s (s:ℂ)=0 := (hzero s (by norm_num)).2.mpr rfl
    let a := dslope (factor s) (s:ℂ)
    have ha (z : ℂ) (hz : z ∈ D) : a z ≠ 0 := by
      rcases eq_or_ne z (s:ℂ) with rfl | h
      · dsimp only [a]; rw [dslope_same,hd.deriv]; exact_mod_cast (div_ne_zero Real.pi_ne_zero (by norm_num : (4:ℝ)*height ≠ 0))
      · dsimp only [a]
        rw [dslope_of_ne _ h,slope_def_module,smul_eq_mul,h0,sub_zero]
        exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr h)) (fun hh => h ((hzero z hz).2.mp hh))
    let q := fun z => dslope g (s:ℂ) z / a z
    refine ⟨q, ((Complex.differentiableOn_dslope hs).2 hg).div
      ((Complex.differentiableOn_dslope hs).2 (fun z hz => (hzero z hz).1.differentiableAt.differentiableWithinAt)) ha, ?_⟩
    intro z hz
    have hg' := sub_smul_dslope g (s:ℂ) z
    have hf' := sub_smul_dslope (factor s) (s:ℂ) z
    simp only [smul_eq_mul,hgz,h0,sub_zero] at hg' hf'
    dsimp only [q]
    rw [← hf',← hg']
    change _ = _ / a z * (_*a z)
    field_simp [ha z hz]
  have hfac (t : Finset ℝ) (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g D)
      (ht : ∀ s ∈ t, g s=0) : ∃ V : ℂ → ℂ, DifferentiableOn ℂ V D ∧
        ∀ z ∈ D, g z = V z * ∏ s ∈ t, factor s z := by
    induction t using Finset.induction_on generalizing g with
    | empty => exact ⟨g,hg,by simp⟩
    | @insert s t hs ih =>
      obtain ⟨q,hq,hgq⟩ := hremove s g hg (ht _ (Finset.mem_insert_self ..))
      have hqt (v : ℝ) (hv : v ∈ t) : q v = 0 := by
        have hD : (v:ℂ) ∈ D := by change |(v:ℂ).im| < _; norm_num
        have he := hgq v hD
        rw [ht v (Finset.mem_insert_of_mem hv)] at he
        refine (mul_eq_zero.mp he.symm).resolve_right (fun hh => ?_)
        have hx := ((strip_factor_divisor s).2.2.1 v hD).2.mp hh
        exact hs ((Complex.ofReal_injective hx) ▸ hv)
      obtain ⟨V,hV,he⟩ := ih q hq hqt
      refine ⟨V,hV,fun z hz => ?_⟩
      rw [hgq z hz,he z hz,Finset.prod_insert hs]
      ring
  obtain ⟨V,hV,he⟩ := hfac S f (fun z hz => (ha z hz).differentiableAt.differentiableWithinAt) hzero
  refine ⟨V, fun z hz => hV.analyticAt (hopen.mem_nhds hz), he, ?_⟩
  intro z hz
  have hD : z ∈ D := by change |z.im| < _; rw [hz]; norm_num
  rw [he z hD, norm_mul, norm_prod]
  simp [fun s => ((strip_factor_modulus s z hz.le).2.2.2.2).mpr hz]

end Turan.StripDetails
