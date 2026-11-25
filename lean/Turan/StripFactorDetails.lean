-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.StripDetailDefs
noncomputable section
open Set
namespace Turan.StripDetails

private def α : ℝ := Real.pi/(4*height)
private theorem alpha_pos : 0 < α := by unfold α height; positivity
private theorem coord (s : ℝ) (z : ℂ) : coordinate s z = (α:ℂ)*(z-s) := by
  unfold coordinate α
  push_cast
  ring
private theorem coord_im (s : ℝ) (z : ℂ) : (coordinate s z).im=α*z.im := by
  simp [coord,Complex.mul_im]
private theorem coord_re (s : ℝ) (z : ℂ) : (coordinate s z).re=α*(z.re-s) := by
  simp [coord,Complex.mul_re]
private theorem alpha_height : α*height=Real.pi/4 := by unfold α height; ring
private theorem factor_exp (s : ℝ) (z : ℂ) :
    factor s z=(Complex.exp (2*coordinate s z)-1)/(Complex.exp (2*coordinate s z)+1) := by
  let q := coordinate s z
  change Complex.tanh q = _
  rw [Complex.tanh_eq_sinh_div_cosh, Complex.sinh, Complex.cosh, div_div_div_cancel_right₀ two_ne_zero]
  change _ = (Complex.exp (2*q)-1)/(Complex.exp (2*q)+1)
  rw [two_mul, Complex.exp_add, Complex.exp_neg,
    ← mul_div_mul_right _ _ (Complex.exp_ne_zero q)]
  congr 1 <;> field_simp [Complex.exp_ne_zero q]
private theorem exp_re (s : ℝ) (z : ℂ) :
    (Complex.exp (2*coordinate s z)).re =
      Real.exp (2*(coordinate s z).re)*Real.cos (2*(coordinate s z).im) := by
  simp [Complex.exp_re, two_mul, Complex.add_re, Complex.add_im]

theorem strip_factor_modulus (s : ℝ) (z : ℂ) (hy : |z.im| ≤ height) :
    let ζ := coordinate s z
    |ζ.im| ≤ Real.pi/4 ∧ 0 ≤ (Complex.exp (2*ζ)).re ∧
    factor s z=(Complex.exp (2*ζ)-1)/(Complex.exp (2*ζ)+1) ∧
    ‖factor s z‖ ≤ 1 ∧ (‖factor s z‖=1 ↔ |z.im|=height)  := by
  dsimp only
  let E := Complex.exp (2*coordinate s z)
  have hi : |(coordinate s z).im| ≤ Real.pi/4 := by
    rw [coord_im,abs_mul,abs_of_pos alpha_pos, ← alpha_height]
    exact mul_le_mul_of_nonneg_left hy alpha_pos.le
  have hc : 0 ≤ Real.cos (2*(coordinate s z).im) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> linarith [(abs_le.mp hi).1,(abs_le.mp hi).2]
  have hE : 0 ≤ E.re := by rw [show E.re = _ from exp_re s z]; positivity
  have den : E+1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp [Complex.add_re] at he
    linarith
  have hid : ‖E+1‖^2-‖E-1‖^2=4*E.re := by
    simp [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
    <;> ring
  have hn : ‖factor s z‖ ≤ 1 := by
    rw [factor_exp, norm_div, div_le_one (norm_pos_iff.mpr den)]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith)
  refine ⟨hi, hE, factor_exp s z, hn, ?_⟩
  have hiff : ‖factor s z‖=1 ↔ E.re=0 := by
    rw [factor_exp, norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr den)]
    constructor
    · intro he
      change ‖E-1‖ = ‖E+1‖ at he
      rw [he] at hid
      linarith
    · intro he
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      linarith
  rw [hiff, show E.re = _ from exp_re s z, mul_eq_zero,
    or_iff_right (Real.exp_pos _).ne', coord_im]
  constructor
  · intro he
    apply le_antisymm hy
    by_contra! hh
    have hlt : |2*(α*z.im)| < Real.pi/2 := by
      rw [abs_mul, abs_mul, abs_of_pos alpha_pos, abs_of_pos (by norm_num : (0:ℝ)<2)]
      calc
        2*(α*|z.im|) < 2*(α*height) := mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hh alpha_pos) (by norm_num)
        _ = Real.pi/2 := by rw [alpha_height]; ring
    exact (Real.cos_pos_of_mem_Ioo (abs_lt.mp hlt)).ne' he
  · intro he
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ height)).mp he with he | he
    · rw [he,alpha_height, show 2*(Real.pi/4)=Real.pi/2 by ring,Real.cos_pi_div_two]
    · rw [he,mul_neg,alpha_height,mul_neg,Real.cos_neg,show 2*(Real.pi/4)=Real.pi/2 by ring,Real.cos_pi_div_two]

theorem strip_factor_uniform_limit (s ε : ℝ) (hε : 0 < ε) :
    ∃ R > (0:ℝ), ∀ z : ℂ, |z.im| ≤ height → R ≤ |z.re| → |‖factor s z‖-1| < ε  := by
  let D := (2+2/ε)/(2*α)
  have hD : 0 < D := by have := alpha_pos; dsimp [D]; positivity
  refine ⟨|s|+D, by linarith [abs_nonneg s], fun z _ hz => ?_⟩
  have hd : D ≤ |z.re-s| := by
    have h := abs_add_le (z.re-s) s
    rw [sub_add_cancel] at h
    linarith
  have right (v : ℂ) (hv : D ≤ v.re-s) : |‖factor s v‖-1| < ε := by
    let E := Complex.exp (2*coordinate s v)
    have hE : 1+2/ε < ‖E‖ := by
      rw [show ‖E‖ = _ from Complex.norm_exp _, show (2*coordinate s v).re =
        2*(coordinate s v).re by simp [two_mul, Complex.add_re], coord_re]
      have hh := (div_le_iff₀ (show 0 < 2*α by first | positivity | exact mul_pos (by norm_num) alpha_pos)).mp hv
      linarith [Real.add_one_le_exp (2*(α*(v.re-s)))]
    have hd' : 2/ε < ‖E+1‖ := by
      have h := norm_sub_norm_le E (-1)
      simp only [norm_neg,norm_one,sub_neg_eq_add] at h
      linarith
    have hdn : E+1 ≠ 0 := norm_pos_iff.mp ((by positivity : 0 < 2/ε).trans hd')
    have he : factor s v-1= -2/(E+1) := by rw [factor_exp]; change (E-1)/(E+1)-1=_; field_simp [hdn]; ring
    have h := abs_norm_sub_norm_le (factor s v) (1:ℂ)
    rw [norm_one,he,norm_div, norm_neg, Complex.norm_ofNat] at h
    apply h.trans_lt
    exact (div_lt_iff₀ (norm_pos_iff.mpr hdn)).mpr (by
      have := (div_lt_iff₀ hε).mp hd'; linarith)
  rcases le_abs.mp hd with hr | hl
  · exact right z hr
  · let v := 2*(s:ℂ)-z
    have hv : D ≤ v.re-s := by change D ≤ (2*(s:ℂ)-z).re-s; rw [two_mul]; simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re]; linarith
    have hf : factor s v= -factor s z := by
      unfold factor; rw [← Complex.tanh_neg]; congr 1; rw [coord,coord]; dsimp [v]; ring
    simpa only [hf, norm_neg] using right v hv

end Turan.StripDetails
