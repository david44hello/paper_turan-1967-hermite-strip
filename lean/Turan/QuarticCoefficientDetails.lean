-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs
import Mathlib.Tactic

noncomputable section
namespace Turan

-- X = 4x², Y = 4y² in case (A).
theorem quartic_balanced_intermediate_bound {X Y β : ℝ} (hY : 2 < Y)
    (hX : (X - 2) * (β^2 - 2*β + 2 + Y) = 2 - β^2) :
    X ≤ 2 + 2/(1 + Y) ∧ 2 + 2/(1 + Y) < Y + 2 := by
  have hden : 0 < 1+Y := by linarith
  have hcoef : 1+Y ≤ β^2-2*β+2+Y := by nlinarith [sq_nonneg (β-1)]
  have hd := lt_of_lt_of_le hden hcoef
  have hx : X-2 = (2-β^2)/(β^2-2*β+2+Y) := (eq_div_iff hd.ne').mpr hX
  constructor
  · have hb : X-2 ≤ 2/(1+Y) := by
      rw [hx]
      calc
        _ ≤ 2/(β^2-2*β+2+Y) := by gcongr; nlinarith [sq_nonneg β]
        _ ≤ 2/(1+Y) := by gcongr
    linarith
  · have : 2/(1+Y) < Y := (div_lt_iff₀ hden).mpr (by nlinarith [sq_nonneg Y])
    linarith

theorem quartic_upper_divided_coefficient {α : ℂ} (hα : 0 < α.im) :
    let H := 12*α - 2
    let c := α + 1/2 - 1/H
    H ≠ 0 ∧ (12*α^2 + 4*α - 2)/H = c ∧
      c.im = α.im + 12*α.im/‖H‖^2 ∧ 0 < c.im := by
  let H := 12*α-2
  have hi : H.im = 12*α.im := by norm_num [H, Complex.sub_im, Complex.mul_im]
  have hn : H ≠ 0 := by
    intro he
    rw [he, Complex.zero_im] at hi
    linarith
  have hratio : (12*α^2+4*α-2)/H = α+1/2-1/H := by
    field_simp [hn]
    dsimp [H]; ring
  have him : (α+1/2-1/H).im = α.im+12*α.im/‖H‖^2 := by
    simp [Complex.sub_im, Complex.normSq_eq_norm_sq, hi, neg_div]
  refine ⟨hn,hratio,him,?_⟩
  rw [him]
  positivity

theorem quartic_upper_divided_recovery {α : ℂ} (hα : 0 < α.im) {l₁ l₀ : ℝ}
    (heq : (12*α - 2) * (l₀ : ℂ) =
      -(12*α^4 + 16*α^3 + 12*α^2 - 3) + (12*α^2 + 4*α - 2) * (l₁ : ℂ)) :
    let H := 12*α - 2
    let g := (12*α^4 + 16*α^3 + 12*α^2 - 3)/H
    let c := α + 1/2 - 1/H
    (l₀ : ℂ) = -g + c * (l₁ : ℂ) ∧
      l₁ = g.im/c.im ∧ l₀ = -g.re + c.re*l₁ := by
  let H := 12*α-2
  let g := (12*α^4+16*α^3+12*α^2-3)/H
  let c := α+1/2-1/H
  obtain ⟨hn,hq,_,hp⟩ := quartic_upper_divided_coefficient hα
  have he : (l₀:ℂ) = -g+c*(l₁:ℂ) := by
    dsimp only [g,c,H]
    rw [← hq]
    field_simp [hn]
    linear_combination heq
  have hi := congrArg Complex.im he
  simp only [Complex.ofReal_im, Complex.add_im, Complex.neg_im, Complex.mul_im,
    Complex.ofReal_re, mul_zero, zero_add] at hi
  have hr := congrArg Complex.re he
  simp only [Complex.ofReal_re, Complex.add_re, Complex.neg_re, Complex.mul_re,
    Complex.ofReal_im, mul_zero, sub_zero] at hr
  exact ⟨he,(eq_div_iff (show c.im ≠ 0 from hp.ne')).mpr (by linarith),hr⟩

-- The multiset allows any repeated pair and t = 0.
theorem quartic_repeated_upper_offsets {p q r : ℂ}
    (hq : q.im = p.im) (hr : r.im = p.im) (hrep : p = q ∨ p = r ∨ q = r) :
    let α := (p + q + r)/3
    ∃ t : ℝ, let z₀ := α + (t : ℂ)
             let v := α - 2*(t : ℂ)
             ({p, q, r} : Multiset ℂ) = {z₀, z₀, v} ∧ v.re - z₀.re = -3*t := by
  have offset (u v : ℂ) (hi : v.im = u.im) :
      let A := (u+u+v)/3
      ∃ t : ℝ, A + (t:ℂ) = u ∧ A - 2*(t:ℂ) = v ∧ v.re-u.re = -3*t := by
    dsimp only
    refine ⟨(u.re-v.re)/3, ?_, ?_, by ring⟩
    all_goals apply Complex.ext <;> norm_num [Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, hi] <;> ring
  rcases hrep with rfl | rfl | rfl
  · obtain ⟨t,h₁,h₂,h₃⟩ := offset p r hr
    exact ⟨t,by rw [h₁,h₂],by rw [h₁,h₂]; exact h₃⟩
  · obtain ⟨t,h₁,h₂,h₃⟩ := offset p q hq
    rw [show p+q+p = p+p+q by ring]
    refine ⟨t, ?_, ?_⟩
    · rw [h₁,h₂]
      simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]
      ac_rfl
    · rw [h₁,h₂]; exact h₃
  · obtain ⟨t,h₁,h₂,h₃⟩ := offset q p hq.symm
    rw [show p+q+q = q+q+p by ring]
    refine ⟨t, ?_, ?_⟩
    · rw [h₁,h₂]
      simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]
      ac_rfl
    · rw [h₁,h₂]; exact h₃

#print axioms quartic_balanced_intermediate_bound
#print axioms quartic_upper_divided_coefficient
#print axioms quartic_upper_divided_recovery
#print axioms quartic_repeated_upper_offsets

end Turan
