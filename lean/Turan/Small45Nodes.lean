module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs
public import Mathlib.Tactic

@[expose] public section

open Polynomial Set
namespace Turan.Small45

private def sextic (s : ℝ) := s^6+14*s^5-111*s^4+228*s^3-143*s^2-6*s+41
private def num (s : ℝ) := 2*s^3+36*s^2-87*s-49
private def den (s : ℝ) := 4*s+36
private def Q (s w : ℝ) := den s*(w^2-s*w)+num s

/-- The equality of values at two shifted nodes, with denominators cleared. -/
def Node (l r : ℝ) : Prop := ∀ a b : ℂ,
    (family 4 5 a b).eval ((l:ℂ)-1/2)*r = (family 4 5 a b).eval ((r:ℂ)-1/2)*l

private theorem node_of_root (l r s : ℝ) (hs : sextic s = 0) (hd : den s ≠ 0)
    (hsum : l+r=s) (hprod : den s*(l*r)=num s) : Node l r := by
  let p := l*r
  let c₄ := (16*(s^2-p)-32*s-24)*p-1
  let c₅ := (32*(s^3-2*p*s)-80*(s^2-p)-80*s+200)*p+41
  have h₄ : c₄ = 0 := by
    apply (mul_eq_zero.mp (show den s^2*c₄ = 0 by
      dsimp only [c₄]
      linear_combination (norm := (unfold den num sextic; dsimp [p]; ring))
        64*hs + ((16*s^2-32*s-24)*den s-16*(den s*p+num s))*hprod)).resolve_left
      (pow_ne_zero 2 hd)
  have h₅ : c₅ = 0 := by
    dsimp only [c₅]
    linear_combination (norm := (dsimp [c₄,p,den,num]; ring)) -16*p*hprod - 41*h₄
  subst s
  dsimp [c₄,c₅,p] at h₄ h₅
  have hc₄ : (16*(((l:ℂ)+r)^2-l*r)-32*(l+r)-24)*(l*r)-1=0 := by exact_mod_cast h₄
  have hc₅ : (32*(((l:ℂ)+r)^3-2*(l*r)*(l+r))-80*((l+r)^2-l*r)-80*(l+r)+200)*(l*r)+41=0 := by
    exact_mod_cast h₅
  intro a b
  norm_num [family,hermite,eval_sub,eval_add,eval_mul,nsmul_eq_mul]
  linear_combination a*((l:ℂ)-r)*hc₄ + b*((l:ℂ)-r)*hc₅

/-- Signs of the quadratic at its two trial points need only be checked at
the endpoints of the isolating interval for s. -/
private theorem Q_mono (s t w : ℝ) (hst : s ≤ t)
    (h : (t ≤ -20 ∧ (w = -1/125000 ∨ w = 0)) ∨
         (2.9 ≤ s ∧ (w = 0.441 ∨ w = 0.443))) : Q s w ≤ Q t w := by
  let d := 2*(s^2+s*t+t^2)+(36-4*w)*(s+t)+4*w^2-36*w-87
  have hd : 0 ≤ d := by
    dsimp [d]
    rcases h with ⟨ht, hw⟩ | ⟨hs, hw⟩
    · have hst' : 0 ≤ (s+20)*(t+20) := mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      rcases hw with rfl | rfl <;>
        nlinarith only [ht,hst,hst',sq_nonneg (s+20),sq_nonneg (t+20)]
    · have hst' : 0 ≤ s*t := mul_nonneg (by linarith) (by linarith)
      rcases hw with rfl | rfl <;> nlinarith only [hs,hst,hst',sq_nonneg s,sq_nonneg t]
  have he : Q t w-Q s w=(t-s)*d := by dsimp [Q,num,den,d]; ring
  linarith only [he, mul_nonneg (sub_nonneg.mpr hst) hd]

theorem nodes_one : ∃ l r : ℝ, -20.11 < l ∧ l < -20.09 ∧
    -1/125000 < r ∧ r < 0 ∧ Node l r := by
  obtain ⟨s, ⟨hs₀,hs₁⟩,hs⟩ := intermediate_value_Ioo' (by norm_num : (-20.1032178007:ℝ) ≤ -20.1032178006)
    (f := sextic) (by unfold sextic; fun_prop)
    (show (0:ℝ) ∈ Ioo (sextic (-20.1032178006)) (sextic (-20.1032178007)) by norm_num [sextic])
  have h₀ : 0 < Q s (-1/125000) :=
    lt_of_lt_of_le (by norm_num [Q,num,den] : 0 < Q (-20.1032178007) (-1/125000))
      (Q_mono _ _ _ hs₀.le (Or.inl ⟨by linarith, Or.inl rfl⟩))
  have h₁ : Q s 0 < 0 :=
    lt_of_le_of_lt (Q_mono _ _ _ hs₁.le (Or.inl ⟨by norm_num, Or.inr rfl⟩))
      (by norm_num [Q,num,den] : Q (-20.1032178006) 0 < 0)
  obtain ⟨r, ⟨hr₀,hr₁⟩,hr⟩ := intermediate_value_Ioo' (by norm_num : (-1/125000:ℝ) ≤ 0)
    (f := Q s) (by unfold Q; fun_prop) (show (0:ℝ) ∈ Ioo (Q s 0) (Q s (-1/125000)) from ⟨h₁,h₀⟩)
  refine ⟨s-r,r,by linarith,by linarith,hr₀,hr₁,node_of_root _ _ s hs ?_ (by ring) ?_⟩
  · unfold den; linarith
  · linear_combination (norm := (unfold Q; ring)) -hr

theorem nodes_two : ∃ l r : ℝ, 0.43 < l ∧ l < 0.45 ∧
    2.46 < r ∧ r < 2.48 ∧ Node l r := by
  obtain ⟨s, ⟨hs₀,hs₁⟩,hs⟩ := intermediate_value_Ioo (by norm_num : (2.910004:ℝ) ≤ 2.910005)
    (f := sextic) (by unfold sextic; fun_prop)
    (show (0:ℝ) ∈ Ioo (sextic 2.910004) (sextic 2.910005) by norm_num [sextic])
  have h₀ : 0 < Q s 0.441 :=
    lt_of_lt_of_le (by norm_num [Q,num,den] : 0 < Q 2.910004 0.441)
      (Q_mono _ _ _ hs₀.le (Or.inr ⟨by norm_num, Or.inl rfl⟩))
  have h₁ : Q s 0.443 < 0 :=
    lt_of_le_of_lt (Q_mono _ _ _ hs₁.le (Or.inr ⟨by linarith, Or.inr rfl⟩))
      (by norm_num [Q,num,den] : Q 2.910005 0.443 < 0)
  obtain ⟨l, ⟨hl₀,hl₁⟩,hl⟩ := intermediate_value_Ioo' (by norm_num : (0.441:ℝ) ≤ 0.443)
    (f := Q s) (by unfold Q; fun_prop) (show (0:ℝ) ∈ Ioo (Q s 0.443) (Q s 0.441) from ⟨h₁,h₀⟩)
  refine ⟨l,s-l,by linarith,by linarith,by linarith,by linarith,node_of_root _ _ s hs ?_ (by ring) ?_⟩
  · unfold den; linarith
  · linear_combination (norm := (unfold Q; ring)) -hl

end Turan.Small45
