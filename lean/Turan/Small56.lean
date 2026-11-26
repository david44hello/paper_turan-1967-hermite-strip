module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Small56Exterior
public import Turan.Small56Transfer
public import Turan.Degree

@[expose] public section

noncomputable section
namespace Turan.Small56
open Certificate

private theorem scaled_distance (w : ℂ) (n : ℤ) :
    (1000000*w.re-n*1)^2 + (1000000*w.im)^2*1^2 = 1000000^2*(nominal w n)^2 := by
  rw [nominal,distAt,← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  simp only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

private theorem squared_product (w : ℂ) (cs : List ℤ) :
    product cs (1000000*w.re) 1 ((1000000*w.im)^2) =
      (1000000^2)^cs.length * (listProd cs (nominal w))^2 := by
  induction cs with
  | nil => simp [product,listProd]
  | cons c cs ih =>
    simp only [product,List.map_cons,List.prod_cons] at ih ⊢
    rw [scaled_distance,ih]
    simp only [listProd,List.map_cons,List.prod_cons,List.length_cons,pow_succ]
    ring

private theorem nominal_ratio (w : ℂ) (hw : 43/50 ≤ |w.im|) :
    listProd gamma (nominal w) / listProd delta (nominal w) ≤ 9/5 := by
  have hs : 860000^2 ≤ (1000000*w.im)^2 := by
    have hh := (sq_le_sq₀ (by norm_num : (0:ℝ) ≤ 43/50) (abs_nonneg w.im)).2 hw
    rw [sq_abs] at hh
    nlinarith only [hh]
  have h := (exterior (1000000*w.re) ((1000000*w.im)^2) hs).le
  rw [squared_product,squared_product] at h
  change 25*((1000000^2)^12 * _) ≤ 81*((1000000^2)^12 * _) at h
  have hg := listProd_pos gamma (nominal w) (fun n => dist_pos w hw _)
  have hd := listProd_pos delta (nominal w) (fun n => dist_pos w hw _)
  apply (div_le_iff₀ hd).2
  have hh : (5*listProd gamma (nominal w))^2 ≤ (9*listProd delta (nominal w))^2 := by
    linarith only [h]
  have := (sq_le_sq₀ (by positivity) (by positivity)).1 hh
  linarith

private theorem table : ∃ s : List Entry, s.map Entry.G = gamma ∧ s.map Entry.D = delta ∧
    s.length = 12 ∧ (181/100:ℝ)^6 < listProd s lower := by
  obtain ⟨g₁,d₁,h₁⟩ := nodes1
  obtain ⟨g₂,d₂,h₂⟩ := nodes2
  obtain ⟨g₃,d₃,h₃⟩ := nodes3
  obtain ⟨g₄,d₄,h₄⟩ := nodes4
  obtain ⟨g₅,d₅,h₅⟩ := nodes5
  let e₁ : Entry := ⟨_,_,g₁,d₁,h₁,by norm_num,by norm_num⟩
  let e₂ : Entry := ⟨_,_,g₂,d₂,h₂,by norm_num,by norm_num⟩
  let e₃ : Entry := ⟨_,_,g₃,d₃,h₃,by norm_num,by norm_num⟩
  let e₄ : Entry := ⟨_,_,g₄,d₄,h₄,by norm_num,by norm_num⟩
  let e₅ : Entry := ⟨_,_,g₅,d₅,h₅,by norm_num,by norm_num⟩
  refine ⟨[e₁,e₁,e₂,e₂,e₃,e₃,e₃,e₄,e₄,e₄,e₄,e₅], rfl,rfl,rfl,?_⟩
  norm_num [listProd, lower, e₁,e₂,e₃,e₄,e₅]

end Turan.Small56

namespace Turan
open Small56 Polynomial

theorem lemma_twenty_two (a b : ℂ) :
    ∃ z : ℂ, (family 5 6 a b).eval z = 0 ∧ |z.im| < 43/50 := by
  by_contra! h
  obtain ⟨s,hg,hd,hlen,hlarge⟩ := Small56.table
  have hreal (d : ℝ) : (family 5 6 a b).eval ((d:ℂ)-1/2) ≠ 0 := by
    intro hzero
    have := h _ hzero
    norm_num at this
  have hnode := root_product s a b hreal
  have hlower := List.prod_map_le_prod_map₀ (s := s) lower (fun e => |e.g|/|e.d|)
    (fun e _ => div_nonneg (sub_nonneg.mpr e.Gsize.le) (by positivity)) (fun e _ => lower_bound e)
  have hupper (z : ℂ) (hz : z ∈ (family 5 6 a b).roots) :
      listProd s (ratio (z+1/2)) ≤ 181/100 := by
    have hw : 43/50 ≤ |(z+1/2).im| := by simpa using h z (isRoot_of_mem_roots hz)
    have hh := list_ratio_bound s (z+1/2) hw
    rw [hlen,hg,hd] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (Small56.nominal_ratio _ hw) (by positivity)).trans
      (by norm_num [stretch]))
  have hu := Multiset.prod_map_le_prod_map₀ (s := (family 5 6 a b).roots)
    (fun z : ℂ => listProd s (ratio (z+1/2))) (fun _ => (181/100:ℝ))
    (fun z _ => listProd_nonneg _ _ (fun e => div_nonneg (norm_nonneg _) (norm_nonneg _))) hupper
  rw [hnode,Multiset.map_const',Multiset.prod_replicate] at hu
  have hc : (family 5 6 a b).roots.card ≤ 6 := (card_roots' _).trans (by
    rw [family_degree 5 6 (by decide) (by decide)]; split_ifs <;> decide)
  exact (not_lt_of_ge (hlower.trans (hu.trans (pow_le_pow_right₀ (by norm_num) hc)))) hlarge

#print axioms lemma_twenty_two

theorem small56_strict_exterior (s : List Small56.Entry)
    (hg : s.map Small56.Entry.G = Small56.Certificate.gamma)
    (hd : s.map Small56.Entry.D = Small56.Certificate.delta)
    (w : ℂ) (hw : 43/50 ≤ |w.im|) :
    ‖(s.map (fun e => (w-e.g)/(w-e.d))).prod‖ < (181/100:ℝ)  := by
  have hnorm (t : List Entry) : ‖(t.map (fun e => (w-e.g)/(w-e.d))).prod‖ = listProd t (ratio w) := by
    induction t with
    | nil => simp [listProd]
    | cons e t ih => simp only [List.map_cons,List.prod_cons,norm_mul,norm_div,ih, listProd, ratio, distAt]
  have hb := list_ratio_bound s w hw
  have hlen : s.length = 12 := by simpa [Certificate.gamma] using congrArg List.length hg
  rw [hg,hd,hlen] at hb
  rw [hnorm]
  refine hb.trans_lt ((mul_le_mul_of_nonneg_left (Small56.nominal_ratio w hw)
    (by positivity : 0 ≤ (stretch^2)^12)).trans_lt ?_)
  norm_num [stretch]

end Turan
