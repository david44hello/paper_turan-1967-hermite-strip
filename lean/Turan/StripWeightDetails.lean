-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.StripDetailDefs
import Turan.UpperTailStripWeight
noncomputable section
namespace Turan.StripDetails

theorem boundary_weighted_quotient (m j n : ℕ) (hm : 450 ≤ m) (hj : 0 < j) (hnm : n < m)
    (z U : ℂ) (hy : |z.im|=height)
    (hb : ‖U‖ ≤ 4200*(omega m z)^4/((j:ℝ)*(m-n:ℝ))) :
    let S := (m:ℝ)^2/((j:ℝ)*(m-n:ℝ))
    ‖U/weight m z‖ ≤ 4*4200*(165/151:ℝ)^4*S ∧ 4*4200*(165/151:ℝ)^4*S < 23952*S  := by
  dsimp only
  let W := omega m z
  let M : ℝ := m
  let d : ℝ := (j:ℝ)*((m:ℝ)-(n:ℝ))
  have hM : 0 < M := by dsimp [M]; exact_mod_cast (show 0 < m by omega)
  have hd : 0 < d := mul_pos (by exact_mod_cast hj) (sub_pos.mpr (by exact_mod_cast hnm))
  have hW : 0 < W := by unfold W omega; positivity
  let A := Real.sqrt (2*(m:ℝ))
  have hA : 30 ≤ A := by
    have hm' : (450:ℝ) ≤ m := by exact_mod_cast hm
    exact Real.le_sqrt_of_sq_le (by linarith)
  have hApos : 0 < A := by linarith
  have hγ : 4*TailStrip.height/A ≤ 14/165 := (div_le_iff₀ hApos).mpr (by unfold TailStrip.height; linarith)
  have hr : (151/165:ℝ) ≤ 1-4*TailStrip.height/A := by linarith
  have hl : (151/165:ℝ)^4*W^4/(4*M^2) ≤ ‖weight m z‖ := by
    refine le_trans ?_ (UpperTailStrip.variable_weight_lower m hm z hy.le).2.2
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hr 4)
      (by positivity)) (by positivity)
  have hpos : 0 < (151/165:ℝ)^4*W^4/(4*M^2) := by positivity
  change ‖U‖ ≤ 4200*W^4/d at hb
  change ‖U/weight m z‖ ≤ 4*4200*(165/151:ℝ)^4*(M^2/d) ∧ _
  constructor
  · rw [norm_div]
    calc
      _ ≤ (4200*W^4/d)/((151/165:ℝ)^4*W^4/(4*M^2)) := div_le_div₀ (by positivity) hb hpos hl
      _ = _ := by field_simp [hW.ne',hM.ne',hd.ne'] <;> ring
  · exact mul_lt_mul_of_pos_right (by norm_num : 4*4200*(165/151:ℝ)^4 < 23952) (by change 0 < M^2/d; positivity)

theorem strip_center_weight (m : ℕ) (hm : 450 ≤ m) :
    ‖weight m (-1/2)‖ = (1+2/(m:ℝ))^2 ∧ (1+2/(m:ℝ))^2 ≤ (226/225:ℝ)^2 ∧
    23952*(226/225:ℝ)^2 < 24166 ∧ (24166:ℝ) < 25000  := by
  let S := Real.sqrt (2*(m:ℝ))
  have hm' : (450:ℝ) ≤ m := by exact_mod_cast hm
  have hS : 0 < S := by dsimp [S]; positivity
  have hSq : S^2 = 2*(m:ℝ) := Real.sq_sqrt (by positivity)
  have hb : 1-4*Complex.I*(-1/2)/(S:ℂ) = 1+(2/S:ℝ)*Complex.I := by
    push_cast; ring
  have hs : ‖(1+(2/S:ℝ)*Complex.I:ℂ)‖^2 = 1+2/(m:ℝ) := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp only [Complex.add_re,Complex.one_re,Complex.mul_I_re,Complex.ofReal_im,neg_zero,
      add_zero,Complex.add_im,Complex.one_im,Complex.mul_I_im,Complex.ofReal_re,zero_add,one_mul]
    field_simp [hS.ne',show (m:ℝ)≠0 by linarith] <;> nlinarith only [hSq]
  refine ⟨?_,?_,by norm_num,by norm_num⟩
  · rw [weight,norm_pow]
    change ‖1-4*Complex.I*(-1/2)/(S:ℂ)‖^4=_
    rw [hb,show ‖(1+(2/S:ℝ)*Complex.I:ℂ)‖^4=(‖(1+(2/S:ℝ)*Complex.I:ℂ)‖^2)^2 by ring,hs]
  · apply pow_le_pow_left₀ (by positivity)
    have ht : 2/(m:ℝ) ≤ 2/450 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm'
    linarith

end Turan.StripDetails
