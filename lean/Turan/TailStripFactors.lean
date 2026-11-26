module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

@[expose] public section

noncomputable section
namespace Turan
namespace TailStrip

open Complex Set Filter
open scoped Topology

abbrev height : ℝ := 7/11
def strip : Set ℂ := {z | |z.im| ≤ height}
def farBound (f : ℂ → ℂ) : Prop :=
  ∃ C R : ℝ, ∀ z : ℂ, R ≤ |z.re| → z ∈ strip → ‖f z‖ ≤ C

def k : ℝ := 11 * Real.pi / 14
private theorem k_pos : 0 < k := by unfold k; positivity
private theorem k_height : k * height = Real.pi / 2 := by unfold k height; ring
def E (s : ℝ) (z : ℂ) := Complex.exp ((k : ℂ) * (z - s))
def factor (s : ℝ) (z : ℂ) : ℂ := (E s z - 1) / (E s z + 1)

private theorem E_diff (s : ℝ) : Differentiable ℂ (E s) := by unfold E; fun_prop
private theorem E_self (s : ℝ) : E s s = 1 := by simp [E]
private theorem arg_im (s : ℝ) (z : ℂ) :
    ((k : ℂ) * (z - s)).im = k * z.im := by simp
private theorem arg_re (s : ℝ) (z : ℂ) :
    ((k : ℂ) * (z - s)).re = k * (z.re - s) := by simp

private theorem E_re_nonneg (s : ℝ) {z : ℂ} (hz : z ∈ strip) : 0 ≤ (E s z).re := by
  rw [E, Complex.exp_re, arg_im]
  apply mul_nonneg (Real.exp_pos _).le
  apply Real.cos_nonneg_of_mem_Icc
  have h := abs_le.mp (show |z.im| ≤ height from hz)
  constructor
  · rw [← k_height, ← mul_neg]
    exact mul_le_mul_of_nonneg_left h.1 k_pos.le
  · rw [← k_height]
    exact mul_le_mul_of_nonneg_left h.2 k_pos.le

private theorem E_add_ne (s : ℝ) {z : ℂ} (hz : z ∈ strip) : E s z + 1 ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
  linarith [E_re_nonneg s hz]

private theorem E_ne_one (s : ℝ) {z : ℂ} (hz : z ∈ strip) (hne : z ≠ s) : E s z ≠ 1 := by
  intro h
  have hb : |k * z.im| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos k_pos, ← k_height]
    exact mul_le_mul_of_nonneg_left hz k_pos.le
  have hp := Real.pi_pos
  have hinj := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (x := (k : ℂ) * (z-s)) (y := 0)
    (by rw [arg_im]; linarith [(abs_le.mp hb).1])
    (by rw [arg_im]; linarith [(abs_le.mp hb).2])
    (by simp [hp]) (by simp [hp.le])
  have harg : (k : ℂ) * (z-s) = 0 := hinj (by simpa [E] using h)
  exact hne (sub_eq_zero.mp ((mul_eq_zero.mp harg).resolve_left (by exact_mod_cast k_pos.ne')))

theorem factor_ne (s : ℝ) {z : ℂ} (hz : z ∈ strip) (hne : z ≠ s) : factor s z ≠ 0 :=
  div_ne_zero (sub_ne_zero.mpr (E_ne_one s hz hne)) (E_add_ne s hz)

theorem factor_line (s : ℝ) {z : ℂ} (hz : |z.im| = height) : ‖factor s z‖ = 1 := by
  have hcos : Real.cos (k*z.im) = 0 := by
    rcases (abs_eq (by norm_num : 0 ≤ height)).mp hz with h | h
    · rw [h, k_height, Real.cos_pi_div_two]
    · rw [h, mul_neg, Real.cos_neg, k_height, Real.cos_pi_div_two]
  have hre : (E s z).re = 0 := by simp [E, Complex.exp_re, hcos]
  have heq : ‖E s z - 1‖ = ‖E s z + 1‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply, hre]
  rw [factor, norm_div, heq, div_self (norm_ne_zero_iff.mpr (E_add_ne s hz.le))]

theorem factor_real (s x : ℝ) :
    factor s x = (Real.tanh (Real.pi * (x-s)/(4*height)) : ℝ) := by
  let t := Real.pi * (x-s)/(4*height)
  have hk : k * (x-s) = t+t := by unfold k t height; ring
  have hE : E s x = (Real.exp (t+t) : ℝ) := by
    rw [Complex.ofReal_exp, ← hk]; simp [E]
  change (E s x - 1)/(E s x + 1) = ((Real.tanh t : ℝ) : ℂ)
  rw [hE]
  push_cast
  norm_cast
  rw [Real.tanh_eq, Real.exp_neg, Real.exp_add]
  field_simp [Real.exp_ne_zero, (by positivity : Real.exp t * Real.exp t + 1 ≠ 0)]

private theorem E_slope_ne (s : ℝ) {z : ℂ} (hz : z ∈ strip) : dslope (E s) s z ≠ 0 := by
  by_cases h : z = s
  · subst z
    rw [dslope_same]
    have hd := ((hasDerivAt_id (s : ℂ)).sub_const (s : ℂ)).const_mul (k : ℂ)
    have he := hd.cexp
    unfold E
    rw [show deriv (fun z : ℂ => Complex.exp ((k : ℂ)*(z-s))) s = _ from he.deriv]
    simp [k_pos.ne']
  · rw [dslope_of_ne _ h, slope_def_module, smul_eq_mul, E_self]
    exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr h)) (sub_ne_zero.mpr (E_ne_one s hz h))

private theorem strip_nhds (s : ℝ) : strip ∈ 𝓝 (s : ℂ) :=
  Filter.mem_of_superset (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
    |>.mem_nhds (show |(s : ℂ).im| < height by norm_num)) (fun z (h : |z.im| < height) => (show z ∈ strip from h.le))

theorem remove_factor {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f strip) (s : ℝ) (hs : f s = 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g strip ∧ ∀ z ∈ strip, f z = g z * factor s z := by
  let g := fun z => dslope f (s : ℂ) z / dslope (E s) (s : ℂ) z * (E s z + 1)
  refine ⟨g, ((Complex.differentiableOn_dslope (strip_nhds s)).2 hd |>.div
    ((Complex.differentiableOn_dslope (strip_nhds s)).2 (E_diff s).differentiableOn)
    (fun z hz => E_slope_ne s hz) |>.mul ((E_diff s).differentiableOn.add_const 1)), ?_⟩
  intro z hz
  have hf := sub_smul_dslope f (s : ℂ) z
  have he := sub_smul_dslope (E s) (s : ℂ) z
  simp only [smul_eq_mul, hs, sub_zero, E_self] at hf he
  dsimp [g, factor]
  rw [← he, ← hf]
  field_simp [E_slope_ne s hz, E_add_ne s hz]

theorem far_factor (s : ℝ) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ |z.re| → 1/3 ≤ ‖factor s z‖ := by
  refine ⟨|s| + 1/k, fun z hz => ?_⟩
  have hdist : 1/k ≤ |z.re-s| := by
    have h := abs_add_le (z.re-s) s
    rw [sub_add_cancel] at h
    linarith
  have harg : 1 ≤ |k*(z.re-s)| := by
    rw [abs_mul, abs_of_pos k_pos]
    calc
      1 = k*(1/k) := by field_simp [k_pos.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hdist k_pos.le
  have hnorm : ‖E s z‖ = Real.exp (k*(z.re-s)) := by rw [E, Complex.norm_exp, arg_re]
  have hlarge : 2 ≤ ‖E s z‖ ∨ ‖E s z‖ ≤ 1/2 := by
    rcases le_abs.mp harg with h | h
    · left; rw [hnorm]; linarith [Real.add_one_le_exp (k*(z.re-s))]
    · right
      have h2 : 2 ≤ Real.exp (-(k*(z.re-s))) := by linarith [Real.add_one_le_exp (-(k*(z.re-s)))]
      rw [← neg_neg (k*(z.re-s)), Real.exp_neg] at hnorm
      rw [hnorm, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) h2
  have hp := norm_add_le (E s z) 1
  have hm := norm_sub_norm_le (E s z) 1
  have hn := norm_sub_norm_le (1:ℂ) (E s z)
  rw [norm_sub_rev] at hn
  simp only [norm_one] at hp hm hn
  have hden : E s z + 1 ≠ 0 := by
    intro h
    have he : E s z = -1 := eq_neg_of_add_eq_zero_left h
    rw [he, norm_neg, norm_one] at hlarge
    rcases hlarge with h | h <;> norm_num at h
  rw [factor, norm_div, le_div_iff₀ (norm_pos_iff.mpr hden)]
  rcases hlarge with h | h <;> linarith

theorem farBound_remove {f g : ℂ → ℂ} (hf : farBound f) (s : ℝ)
    (hg : ∀ z ∈ strip, f z = g z * factor s z) : farBound g := by
  obtain ⟨C, R, h⟩ := hf
  obtain ⟨S, hS⟩ := far_factor s
  refine ⟨3*C, max R S, fun z hz hstrip => ?_⟩
  have hb := h z ((le_max_left _ _).trans hz) hstrip
  rw [hg z hstrip, norm_mul] at hb
  nlinarith [mul_le_mul_of_nonneg_left (hS z ((le_max_right _ _).trans hz)) (norm_nonneg (g z))]

end TailStrip
end Turan
