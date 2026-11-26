module
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs
public import Mathlib.Tactic
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

@[expose] public section

noncomputable section
open Polynomial Set
namespace Turan

private def nc (t : ℝ) := 5*t^3+9*t^2-45*t-25
private def nq (t x : ℝ) := 4*t*x^2-2*t*(t+1)*x+5-t^2-2*t

private theorem bracket {f : ℝ → ℝ} {l r : ℝ} (hd : Continuous f) (hlr : l ≤ r)
    (hs : f l * f r ≤ 0) : ∃ t ∈ Icc l r, f t = 0 := by
  rcases mul_nonpos_iff.mp hs with h | h
  · exact intermediate_value_Icc' hlr hd.continuousOn ⟨h.2,h.1⟩
  · exact intermediate_value_Icc hlr hd.continuousOn ⟨h.1,h.2⟩

def Small34Node (l r : ℝ) : Prop := ∀ a b : ℂ,
    (family 3 4 a b).eval (l:ℂ) * (2*(r:ℂ)+1) = (family 3 4 a b).eval (r:ℂ) * (2*(l:ℂ)+1)

private theorem node_of_quad {t l r : ℝ} (ht : nc t = 0)
    (hl : nq t l = 0) (hr : nq t r = 0) : Small34Node l r := by
  have ht0 : t ≠ 0 := by rintro rfl; norm_num [nc] at ht
  let T : ℂ := t
  have ht' : 5*T^3+9*T^2-45*T-25 = 0 := by dsimp [T]; unfold nc at ht; exact_mod_cast ht
  have hn : T ≠ 0 := Complex.ofReal_ne_zero.mpr ht0
  let A := (T+1)*(T^2+2*T-5)/T
  let B := (T^5+5*T^4-8*T^3-26*T^2+35*T+25)/T^2
  have vals (x : ℝ) (hx : nq t x = 0) :
      (hermite 3).eval (x:ℂ) = A*(2*(x:ℂ)+1) ∧ (hermite 4).eval (x:ℂ) = B*(2*(x:ℂ)+1) := by
    have hq : 4*T*(x:ℂ)^2-2*T*(T+1)*x+5-T^2-2*T = 0 := by dsimp [T]; unfold nq at hx; exact_mod_cast hx
    constructor
    · norm_num [hermite, eval_mul, eval_sub, nsmul_eq_mul, A]
      field_simp [hn]
      linear_combination (T+2*(x:ℂ)+1)*hq
    · norm_num [hermite, eval_mul, eval_sub, nsmul_eq_mul, B]
      field_simp [hn]
      linear_combination (T^3+2*T^2*(x:ℂ)+3*T^2+4*T*(x:ℂ)^2+2*T*(x:ℂ)-9*T-5)*hq +
        2*(x:ℂ)*ht'
  intro a b
  simp only [family, eval_add, eval_one, eval_mul, eval_C, eval_ofNat, eval_X,
    (vals l hl).1, (vals l hl).2, (vals r hr).1, (vals r hr).2]
  ring

theorem small34_node1 : ∃ l r : ℝ,
    l ∈ Icc (-1.311446) (-1.311445) ∧ r ∈ Icc (-0.096252) (-0.096251) ∧ Small34Node l r := by
  obtain ⟨t, ht, hz⟩ := bracket (f := nc) (l := -3.81539348557) (r := -3.815393485569)
    (by unfold nc; fun_prop) (by norm_num) (by norm_num [nc])
  obtain ⟨htl, htr⟩ := ht
  obtain ⟨l, hl, hzl⟩ := bracket (f := nq t) (l := -1.311446) (r := -1.311445)
    (by unfold nq; fun_prop) (by norm_num) (by unfold nq; dyadic_interval [prec := 80])
  obtain ⟨r, hr, hzr⟩ := bracket (f := nq t) (l := -0.096252) (r := -0.096251)
    (by unfold nq; fun_prop) (by norm_num) (by unfold nq; dyadic_interval [prec := 80])
  exact ⟨l, r, hl, hr, node_of_quad hz hzl hzr⟩

theorem small34_node2 : ∃ l r : ℝ,
    l ∈ Icc (-1.553003) (-1.553002) ∧ r ∈ Icc (1.7943) (1.794301) ∧ Small34Node l r := by
  obtain ⟨t, ht, hz⟩ := bracket (f := nc) (l := -0.517404417703) (r := -0.517404417702)
    (by unfold nc; fun_prop) (by norm_num) (by norm_num [nc])
  obtain ⟨htl, htr⟩ := ht
  obtain ⟨l, hl, hzl⟩ := bracket (f := nq t) (l := -1.553003) (r := -1.553002)
    (by unfold nq; fun_prop) (by norm_num) (by unfold nq; dyadic_interval [prec := 80])
  obtain ⟨r, hr, hzr⟩ := bracket (f := nq t) (l := 1.7943) (r := 1.794301)
    (by unfold nq; fun_prop) (by norm_num) (by unfold nq; dyadic_interval [prec := 80])
  exact ⟨l, r, hl, hr, node_of_quad hz hzl hzr⟩

theorem small34_node3 : ∃ l r : ℝ,
    l ∈ Icc (-0.308319) (-0.308318) ∧ r ∈ Icc (2.074717) (2.074718) ∧ Small34Node l r := by
  obtain ⟨t, ht, hz⟩ := bracket (f := nc) (l := 2.532797903271) (r := 2.532797903272)
    (by unfold nc; fun_prop) (by norm_num) (by norm_num [nc])
  obtain ⟨htl, htr⟩ := ht
  obtain ⟨l, hl, hzl⟩ := bracket (f := nq t) (l := -0.308319) (r := -0.308318)
    (by unfold nq; fun_prop) (by norm_num) (by unfold nq; dyadic_interval [prec := 80])
  obtain ⟨r, hr, hzr⟩ := bracket (f := nq t) (l := 2.074717) (r := 2.074718)
    (by unfold nq; fun_prop) (by norm_num) (by unfold nq; dyadic_interval [prec := 80])
  exact ⟨l, r, hl, hr, node_of_quad hz hzl hzr⟩

end Turan
