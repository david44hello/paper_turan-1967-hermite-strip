module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open scoped ComplexConjugate
namespace Turan

private def defining (t : ℝ) := 12*t^4+16*t^3+12*t^2-3

private theorem quartic_root_data :
    ∃ W : ℂ, (8286/10000 < W.im ∧ W.im < 8287/10000 ∧ W.im < Real.sqrt 3/2) ∧
    ∀ w : ℂ, (0<w.im ∧ 12*w^4+16*w^3+12*w^2-3=0) ↔ w=W := by
  obtain ⟨L,hL,hfL⟩ := intermediate_value_Icc' (by norm_num : (-0.670811:ℝ) ≤ -0.670810)
    (f := defining) (by unfold defining; fun_prop)
    (show (0:ℝ) ∈ Set.Icc (defining (-0.670810)) (defining (-0.670811)) by norm_num [defining])
  obtain ⟨R,hR,hfR⟩ := intermediate_value_Icc (by norm_num : (0.387323:ℝ) ≤ 0.387324)
    (f := defining) (by unfold defining; fun_prop)
    (show (0:ℝ) ∈ Set.Icc (defining 0.387323) (defining 0.387324) by norm_num [defining])
  obtain ⟨hL₀,hL₁⟩ := hL
  obtain ⟨hR₀,hR₁⟩ := hR
  let P := 1/(4*((-L)*R))
  let X := (-4/3-L-R)/2
  let Y := Real.sqrt (P-X^2)
  have hlo : (0.670810:ℝ)*0.387323 ≤ (-L)*R :=
    mul_le_mul (by linarith) hR₀ (by norm_num) (by linarith)
  have hhi : (-L)*R ≤ (0.670811:ℝ)*0.387324 :=
    mul_le_mul (by linarith) hR₁ (by linarith) (by norm_num)
  have hden : 0 < 4*((-L)*R) := by linarith
  have hPlo : 0.96219 < P := by apply (lt_div_iff₀ hden).2; linarith
  have hPhi : P < 0.96221 := by apply (div_lt_iff₀ hden).2; linarith
  have hXlo : -0.52493 < X := by dsimp [X]; linarith
  have hXhi : X < -0.52492 := by dsimp [X]; linarith
  have hXslo : (0.52492:ℝ)^2 < X^2 := by nlinarith [mul_pos (sub_pos.mpr hXhi) (show 0<0.52492-X by linarith)]
  have hXshi : X^2 < (0.52493:ℝ)^2 := sq_lt_sq' hXlo (by linarith)
  have hYsq : Y^2 = P-X^2 := Real.sq_sqrt (by linarith)
  have hYn : 0 ≤ Y := Real.sqrt_nonneg _
  have hYlo : 8286/10000 < Y := by nlinarith
  have hYhi : Y < 8287/10000 := by nlinarith
  have hYpos : 0 < Y := by linarith
  have hY3 : Y < Real.sqrt 3/2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),Real.sqrt_nonneg (3:ℝ)]
  have hP : 4*L*R*P = -1 := by dsimp [P]; field_simp [show L ≠ 0 by linarith, show R ≠ 0 by linarith]
  have hX : 2*X+L+R = -4/3 := by dsimp [X]; ring
  let E := 12*(1-(L*R+2*X*(L+R)+P))
  let G := 12*(2*X*L*R+(L+R)*P)
  have expand (t : ℝ) : defining t-12*(t-L)*(t-R)*(t^2-2*X*t+P)
      = t*(E*t+G) := by
    dsimp [defining,E,G]
    linear_combination 12*t^3*hX-3*hP
  have hEL : E*L+G = 0 := by
    apply (mul_eq_zero.mp (show L*(E*L+G) = 0 by rw [← expand, hfL]; ring)).resolve_left
    linarith
  have hER : E*R+G = 0 := by
    apply (mul_eq_zero.mp (show R*(E*R+G) = 0 by rw [← expand,hfR]; ring)).resolve_left
    linarith
  have hE : E=0 := (mul_eq_zero.mp (show E*(L-R)=0 by linear_combination hEL-hER)).resolve_right (by linarith)
  have hG : G=0 := by simpa [hE] using hEL
  let W : ℂ := ⟨X,Y⟩
  have hquad (w : ℂ) : (w-W)*(w-conj W) = w^2-2*(X:ℂ)*w+(P:ℂ) := by
    apply Complex.ext <;> simp [W, pow_two, Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im]
      <;> nlinarith
  have hX' : 2*(X:ℂ)+L+R= -4/3 := by exact_mod_cast hX
  have hP' : 4*(L:ℂ)*R*P= -1 := by exact_mod_cast hP
  have hE' : 12*(1-((L:ℂ)*R+2*X*(L+R)+P))=0 := by exact_mod_cast hE
  have hG' : 12*(2*(X:ℂ)*L*R+(L+R)*P)=0 := by exact_mod_cast hG
  have hfac (w : ℂ) : 12*w^4+16*w^3+12*w^2-3 =
      12*(w-L)*(w-R)*((w-W)*(w-conj W)) := by
    rw [hquad]
    linear_combination 12*w^3*hX' - 3*hP' + w^2*hE' + w*hG'
  refine ⟨W,⟨hYlo,hYhi,hY3⟩,?_⟩
  intro w
  constructor
  · rintro ⟨him,hroot⟩
    rw [hfac] at hroot
    simp only [mul_eq_zero,sub_eq_zero,OfNat.ofNat_ne_zero,false_or] at hroot
    rcases hroot with (h|h) | h | h
    · simpa [h] using him
    · simpa [h] using him
    · exact h
    · rw [h] at him; change 0 < -Y at him; linarith
  · rintro rfl
    exact ⟨hYpos,by rw [hfac]; simp⟩

theorem quartic_upper_root :
    ∃! w : ℂ, 0 < w.im ∧ 12*w^4 + 16*w^3 + 12*w^2 - 3 = 0 := by
  obtain ⟨W,_,hW⟩ := quartic_root_data
  exact ⟨W,(hW W).2 rfl,fun w hw => (hW w).1 hw⟩

theorem quartic_root_height (w : ℂ) (hw : 0<w.im ∧ 12*w^4+16*w^3+12*w^2-3=0) :
    8286/10000 < w.im ∧ w.im < 8287/10000 ∧ w.im < Real.sqrt 3/2 := by
  obtain ⟨W,h,hW⟩ := quartic_root_data
  exact (hW w).1 hw ▸ h

end Turan
