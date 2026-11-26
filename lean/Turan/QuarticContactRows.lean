module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.GeneralNodes
public import Turan.Hermite
public import Mathlib.Tactic

@[expose] public section

noncomputable section
namespace Turan
open Polynomial Filter
open scoped Topology

private theorem contact_shift_ne_zero {z : ℂ} (hz : z.im ≠ 0) : z + 1/2 ≠ 0 := by
  intro h
  apply hz
  simpa using congrArg Complex.im h

private theorem shifted_quotient_deriv (P : Polynomial ℂ) {w : ℂ} (hw : w ≠ 0) :
    HasDerivAt (fun x => P.eval (x - 1/2) / x)
      ((P.derivative.eval (w - 1/2)*w - P.eval (w - 1/2))/w^2) w := by
  simpa [Function.comp_def] using
    (((P.hasDerivAt (w - 1/2)).comp w ((hasDerivAt_id w).sub_const (1/2))).fun_div
      (hasDerivAt_id w) hw)

private theorem contact_hermite_four : hermite 4 = 16*X^4 - 48*X^2 + 12 := by
  norm_num [hermite, nsmul_eq_mul]
  ring

private theorem contact_mode_values {w : ℂ} (hw : w ≠ 0) :
    nodeMode 2 w = 4*w - 4 - 1/w ∧
    nodeMode 4 w = 16*w^3 - 32*w^2 - 24*w + 40 + 1/w := by
  constructor <;> simp [nodeMode, hermite_low.1, contact_hermite_four, eval_sub, eval_mul,
    eval_add, eval_pow] <;> field_simp [hw] <;> ring

theorem quartic_contact_mode_derivatives {w : ℂ} (hw : w ≠ 0) :
    HasDerivAt (nodeMode 2) (4 + 1/w^2) w ∧
    HasDerivAt (nodeMode 4) (48*w^2 - 64*w - 24 - 1/w^2) w := by
  constructor
  · apply (shifted_quotient_deriv (hermite 2) hw).congr_deriv
    rw [hermite_low.1]
    norm_num [derivative_sub, derivative_mul, derivative_pow, eval_sub, eval_mul, eval_pow]
    field_simp [hw]
    ring
  · apply (shifted_quotient_deriv (hermite 4) hw).congr_deriv
    rw [contact_hermite_four]
    norm_num [derivative_add, derivative_sub, derivative_mul, derivative_pow, eval_add,
      eval_sub, eval_mul, eval_pow]
    field_simp [hw]
    ring

theorem quartic_contact_equations {a b z : ℂ} (hz : z.im ≠ 0)
    (hroot : (family 2 4 a b).eval z = 0) :
    let w := z + 1/2
    a * nodeMode 2 w + b * nodeMode 4 w = -2 ∧
      (2 ≤ (family 2 4 a b).rootMultiplicity z →
        a * deriv (nodeMode 2) w + b * deriv (nodeMode 4) w = 0) := by
  let w := z + 1/2
  let F := family 2 4 a b
  have hw : w ≠ 0 := contact_shift_ne_zero hz
  have hshift : w - 1/2 = z := add_sub_cancel_right _ _
  have hform (x : ℂ) (hx : x ≠ 0) :
      a * nodeMode 2 x + b * nodeMode 4 x = F.eval (x - 1/2)/x - 2 := by
    rw [family_node_form 2 4 a b x hx]
    field_simp [hx]
    ring
  constructor
  · simpa only [hshift, F, hroot, zero_div, zero_sub] using hform w hw
  · intro hm
    have hder : F.derivative.eval z = 0 := by
      simpa [IsRoot] using isRoot_iterate_derivative_of_lt_rootMultiplicity (p := F) (n := 1) hm
    have hquot : HasDerivAt (fun x => F.eval (x - 1/2)/x - 2) 0 w := by
      simpa only [hshift, hder, show F.eval z = 0 from hroot, zero_mul, sub_zero, zero_div] using
        (shifted_quotient_deriv F hw).sub_const 2
    have hrows : HasDerivAt (fun x => a * nodeMode 2 x + b * nodeMode 4 x) 0 w :=
      hquot.congr_of_eventuallyEq ((eventually_ne_nhds hw).mono hform)
    obtain ⟨h₂,h₄⟩ := quartic_contact_mode_derivatives hw
    rw [h₂.deriv, h₄.deriv]
    exact ((h₂.const_mul a).add (h₄.const_mul b)).unique hrows

theorem quartic_single_contact_row {a b z : ℂ} (hz : z.im ≠ 0)
    (hroot : (family 2 4 a b).eval z = 0) :
    let w := z + 1/2
    nodeMode 2 w ≠ 0 ∨ nodeMode 4 w ≠ 0 := by
  dsimp only
  by_contra! h
  have he := (quartic_contact_equations hz hroot).1
  rw [h.1, h.2] at he
  norm_num at he

theorem quartic_dependent_tangent_row {a b w t₂ t₄ : ℂ}
    (hval : a * nodeMode 2 w + b * nodeMode 4 w = -2)
    (htan : a*t₂ + b*t₄ = 0)
    (hdet : nodeMode 2 w * t₄ - nodeMode 4 w * t₂ = 0) :
    t₂ = 0 ∧ t₄ = 0 := by
  constructor
  · linear_combination (t₂/2)*hval - (nodeMode 2 w/2)*htan + (b/2)*hdet
  · linear_combination (t₄/2)*hval - (nodeMode 4 w/2)*htan - (a/2)*hdet

theorem quartic_contact_critical_arithmetic {w : ℂ} (hw : w ≠ 0)
    (h₂ : deriv (nodeMode 2) w = 0) :
    w^2 = -1/4 ∧ deriv (nodeMode 4) w = -32 - 64*w ∧
      (deriv (nodeMode 4) w = 0 → w = -1/2) ∧ deriv (nodeMode 4) w ≠ 0 := by
  obtain ⟨d₂,d₄⟩ := quartic_contact_mode_derivatives hw
  rw [d₂.deriv] at h₂
  have hsq : w^2 = -1/4 := by
    field_simp [hw] at h₂
    linear_combination h₂/4
  have hfour : deriv (nodeMode 4) w = -32 - 64*w := by
    rw [d₄.deriv, hsq]
    ring
  have hcrit (h : deriv (nodeMode 4) w = 0) : w = -1/2 := by
    rw [hfour] at h
    linear_combination -h/64
  refine ⟨hsq,hfour,hcrit,?_⟩
  intro h
  rw [hcrit h] at hsq
  norm_num at hsq

theorem quartic_double_contact_rows {a b z : ℂ} (hz : z.im ≠ 0)
    (hm : 2 ≤ (family 2 4 a b).rootMultiplicity z) :
    let w := z + 1/2
    nodeMode 2 w * deriv (nodeMode 4) w - nodeMode 4 w * deriv (nodeMode 2) w ≠ 0 := by
  have hr : (family 2 4 a b).eval z = 0 := by
    simpa [IsRoot] using
      isRoot_iterate_derivative_of_lt_rootMultiplicity (p := family 2 4 a b) (n := 0)
        (by omega : 0 < (family 2 4 a b).rootMultiplicity z)
  obtain ⟨hval,htan⟩ := quartic_contact_equations hz hr
  dsimp only
  intro hdet
  obtain ⟨h₂,h₄⟩ := quartic_dependent_tangent_row hval (htan hm) hdet
  exact (quartic_contact_critical_arithmetic (contact_shift_ne_zero hz) h₂).2.2.2 h₄

theorem quartic_dependent_value_rows {a b u v : ℂ}
    (hu : a * nodeMode 2 u + b * nodeMode 4 u = -2)
    (hv : a * nodeMode 2 v + b * nodeMode 4 v = -2)
    (hdet : nodeMode 2 u * nodeMode 4 v - nodeMode 4 u * nodeMode 2 v = 0) :
    nodeMode 2 u = nodeMode 2 v ∧ nodeMode 4 u = nodeMode 4 v := by
  constructor
  · linear_combination (nodeMode 2 u/2)*hv - (nodeMode 2 v/2)*hu - (b/2)*hdet
  · linear_combination (nodeMode 4 u/2)*hv - (nodeMode 4 v/2)*hu + (a/2)*hdet

private theorem im_zero_of_nonneg_square {x : ℂ}
    (hi : (x^2).im = 0) (hr : 0 ≤ (x^2).re) : x.im = 0 := by
  simp only [pow_two, Complex.mul_re, Complex.mul_im] at hi hr
  have hp : x.re * x.im = 0 := by linarith
  rcases mul_eq_zero.mp hp with h | h
  · rw [h] at hr
    nlinarith [sq_nonneg x.im]
  · exact h

theorem quartic_equal_row_nodes_real {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (h₂ : nodeMode 2 u = nodeMode 2 v) (h₄ : nodeMode 4 u = nodeMode 4 v) :
    let S := u + v
    divided (nodeMode 2) u v = 0 ∧ divided (nodeMode 4) u v = 0 ∧
      u*v = -1/4 ∧ S^2 - 2*S - 1 = 0 ∧ S.im = 0 ∧ u.im = 0 ∧ v.im = 0 := by
  have hd₂ : divided (nodeMode 2) u v = 0 := by simp [divided,h₂]
  have hd₄ : divided (nodeMode 4) u v = 0 := by simp [divided,h₄]
  obtain ⟨eu₂,eu₄⟩ := contact_mode_values hu
  obtain ⟨ev₂,ev₄⟩ := contact_mode_values hv
  rw [eu₂,ev₂] at h₂
  rw [eu₄,ev₄] at h₄
  have hf : (u-v)*(4*(u*v)+1) = 0 := by
    field_simp [hu,hv] at h₂
    linear_combination h₂
  have hp' := (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr huv)
  have hp : u*v = -1/4 := by linear_combination hp'/4
  have hg : (u-v)*(16*((u+v)^2-u*v)-32*(u+v)-20) = 0 := by
    linear_combination h₄ + h₂
  have hg' := (mul_eq_zero.mp hg).resolve_left (sub_ne_zero.mpr huv)
  rw [hp] at hg'
  have hs : (u+v)^2 - 2*(u+v) - 1 = 0 := by linear_combination hg'/16
  have hs₂ : (u+v-1)^2 = 2 := by linear_combination hs
  have hsi : (u+v).im = 0 := by
    simpa using (im_zero_of_nonneg_square (x := u+v-1)
      (by rw [hs₂]; norm_num) (by rw [hs₂]; norm_num))
  have hdif : (u-v)^2 = (u+v)^2+1 := by linear_combination -4*hp
  have hdi := im_zero_of_nonneg_square (x := u-v)
    (by rw [hdif]; simp [pow_two,Complex.mul_im,hsi])
    (by
      rw [hdif, Complex.add_re, pow_two, Complex.mul_re, hsi]
      simpa only [zero_mul, sub_zero, Complex.one_re] using
        (add_nonneg (mul_self_nonneg (u+v).re) (by norm_num : (0 : ℝ) ≤ 1)))
  rw [Complex.add_im] at hsi
  rw [Complex.sub_im] at hdi
  exact ⟨hd₂,hd₄,hp,hs,hsi,by linarith,by linarith⟩

theorem quartic_distinct_contact_rows {a b z₁ z₂ : ℂ} (hne : z₁ ≠ z₂)
    (h₁ : z₁.im ≠ 0) (h₂ : z₂.im ≠ 0)
    (hr₁ : (family 2 4 a b).eval z₁ = 0) (hr₂ : (family 2 4 a b).eval z₂ = 0) :
    let u := z₁ + 1/2
    let v := z₂ + 1/2
    nodeMode 2 u * nodeMode 4 v - nodeMode 4 u * nodeMode 2 v ≠ 0 := by
  dsimp only
  intro hdet
  obtain ⟨he₂,he₄⟩ := quartic_dependent_value_rows
    (quartic_contact_equations h₁ hr₁).1 (quartic_contact_equations h₂ hr₂).1 hdet
  have hreal := quartic_equal_row_nodes_real (contact_shift_ne_zero h₁)
    (contact_shift_ne_zero h₂) (fun h => hne (add_right_cancel h)) he₂ he₄
  exact h₁ (by simpa using hreal.2.2.2.2.2.1)

#print axioms quartic_contact_mode_derivatives
#print axioms quartic_contact_equations
#print axioms quartic_single_contact_row
#print axioms quartic_dependent_tangent_row
#print axioms quartic_contact_critical_arithmetic
#print axioms quartic_double_contact_rows
#print axioms quartic_dependent_value_rows
#print axioms quartic_equal_row_nodes_real
#print axioms quartic_distinct_contact_rows

end Turan
