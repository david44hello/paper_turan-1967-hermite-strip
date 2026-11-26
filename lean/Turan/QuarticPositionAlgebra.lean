module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Degree
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Polynomial
open scoped ComplexConjugate
namespace Turan.QuarticPosition

def model (a b z : ℂ) : ℂ :=
  16*b*z^4 + (4*a-48*b)*z^2 + 2*z + 1-2*a+12*b

theorem eval_model (a b z : ℂ) : (family 2 4 a b).eval z = model a b z := by
  norm_num [model, family, hermite, eval_add, eval_sub, eval_mul, eval_smul, nsmul_eq_mul]
  ring

def Factors (a b p q r s : ℂ) : Prop :=
  ∀ z, model a b z = 16*b*((z-p)*(z-q)*(z-r)*(z-s))

theorem factors_conj {a b p q r s : ℂ} (hf : Factors a b p q r s) :
    Factors (conj a) (conj b) (conj p) (conj q) (conj r) (conj s) := by
  intro z
  simpa [model, map_ofNat] using congrArg conj (hf (conj z))

/-- Reading off coefficients by interpolation at 0, 1, -1 and 2. -/
theorem coefficients {a b c₃ c₂ c₁ c₀ : ℂ}
    (hf : ∀ z, model a b z = 16*b*(z^4+c₃*z^3+c₂*z^2+c₁*z+c₀)) :
    16*b*c₃ = 0 ∧ 16*b*c₂ = 4*a-48*b ∧ 16*b*c₁ = 2 ∧ 16*b*c₀ = 1-2*a+12*b := by
  have h0 := hf 0
  have hp := hf 1
  have hm := hf (-1)
  have ht := hf 2
  unfold model at h0 hp hm ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-ht+3*hp-3*h0+hm)/6
  · linear_combination -(hp+hm-2*h0)/2
  · linear_combination (ht-6*hp+3*h0+2*hm)/6
  · linear_combination -h0

theorem constraint {a b c₂ c₁ c₀ : ℂ} (hb : b ≠ 0)
    (hf : ∀ z, model a b z = 16*b*(z^4+0*z^3+c₂*z^2+c₁*z+c₀)) :
    4*c₀+2*c₂-2*c₁+3=0 ∧ c₁ ≠ 0 := by
  obtain ⟨_,h2,h1,h0⟩ := coefficients hf
  constructor
  · apply (mul_eq_zero.mp (show b*(4*c₀+2*c₂-2*c₁+3)=0 by
      linear_combination (4*h0+2*h2-2*h1)/16)).resolve_left hb
  · intro e
    simp [e] at h1

theorem roots_sum {a b p q r s : ℂ} (hb : b ≠ 0) (hf : Factors a b p q r s) :
    p+q+r+s=0 := by
  have h := (coefficients (c₃ := -(p+q+r+s))
    (c₂ := p*q+p*r+p*s+q*r+q*s+r*s)
    (c₁ := -(p*q*r+p*q*s+p*r*s+q*r*s)) (c₀ := p*q*r*s)
    (fun z => by rw [hf]; ring)).1
  exact neg_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (mul_ne_zero (by norm_num) hb))

theorem realize {c₂ c₁ c₀ : ℂ} (h : 4*c₀+2*c₂-2*c₁+3=0) (hn : c₁ ≠ 0) :
    ∃ a b : ℂ, b ≠ 0 ∧ ∀ z, model a b z = 16*b*(z^4+c₂*z^2+c₁*z+c₀) := by
  refine ⟨4*(8*c₁)⁻¹*(c₂+3), (8*c₁)⁻¹, by simp [hn], ?_⟩
  intro z
  unfold model
  field_simp
  linear_combination -4*h

theorem three_contacts (a b : ℂ) (hb : b ≠ 0) (y : ℝ)
    (hcnt : 3 ≤ ((family 2 4 a b).roots.filter (fun z => |z.im|=y)).card) :
    ∃ p q r s : ℂ, Factors a b p q r s ∧ |p.im|=y ∧ |q.im|=y ∧ |r.im|=y := by
  classical
  let f := family 2 4 a b
  let t := f.roots.filter (fun z => |z.im|=y)
  have hd : f.natDegree = 4 := by simp [f, family_degree 2 4 (by decide) (by decide), hb]
  have hcard := (IsAlgClosed.splits f).natDegree_eq_card_roots.symm.trans hd
  have hpos : 0 < (t.powersetCard 3).card := by
    rw [Multiset.card_powersetCard]
    exact Nat.choose_pos hcnt
  obtain ⟨u,hu⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
  obtain ⟨hle,hu3⟩ := Multiset.mem_powersetCard.mp hu
  obtain ⟨p,q,r,hr⟩ := Multiset.card_eq_three.mp hu3
  obtain ⟨v,hv⟩ := Multiset.le_iff_exists_add.mp (hle.trans (Multiset.filter_le _ _))
  have hv1 : v.card = 1 := by rw [hv, Multiset.card_add, hu3] at hcard; omega
  obtain ⟨s,hs⟩ := Multiset.card_eq_one.mp hv1
  have hrt : f.roots = p ::ₘ q ::ₘ r ::ₘ {s} := by simp [hv,hr,hs]
  have hc (z : ℂ) (hz : z ∈ u) : |z.im|=y := (Multiset.mem_filter.mp (Multiset.mem_of_le hle hz)).2
  refine ⟨p,q,r,s,?_,hc _ (by simp [hr]),hc _ (by simp [hr]),hc _ (by simp [hr])⟩
  have h4 : hermite 4 = 16*X^4-48*X^2+12 := by norm_num [hermite, nsmul_eq_mul]; ring
  have h2 : hermite 2 = 4*X^2-2 := by norm_num [hermite, nsmul_eq_mul]; ring
  have hl : f.leadingCoeff = 16*b := by
    rw [leadingCoeff, hd]
    norm_num [f,family,h4,h2,coeff_add,coeff_sub,coeff_C_mul,coeff_ofNat_mul,coeff_X_pow,coeff_one,coeff_X]
    ring
  intro z
  rw [← eval_model]
  have hfac := (IsAlgClosed.splits f).eq_prod_roots
  rw [hl,hrt] at hfac
  simpa [f,eval_mul,eval_sub,mul_assoc] using congrArg (eval z) hfac

end Turan.QuarticPosition
