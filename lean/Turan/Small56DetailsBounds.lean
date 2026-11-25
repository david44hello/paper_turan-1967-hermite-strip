-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Small56Exterior
import Turan.Small56Transfer

noncomputable section
open scoped Topology
open Polynomial
namespace Turan.Small56

open Certificate

def nodeQuotient (s : List Entry) (w : ℂ) : ℂ :=
  (s.map (fun e => (w - e.g) / (w - e.d))).prod

def modelFactorProduct (cs : List ℤ) (w : ℂ) : ℂ :=
  (cs.map (fun n => w - (n : ℂ)/1000000)).prod

def modelQuotient (w : ℂ) : ℂ :=
  modelFactorProduct Certificate.gamma w / modelFactorProduct Certificate.delta w

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

private theorem model_product_norm (cs : List ℤ) (w : ℂ) :
    ‖modelFactorProduct cs w‖ = listProd cs (nominal w) := by
  induction cs with
  | nil => simp [modelFactorProduct, listProd]
  | cons c cs ih =>
    change ‖(w - (c : ℂ)/1000000) * modelFactorProduct cs w‖ = nominal w c * listProd cs (nominal w)
    rw [norm_mul, ih]
    simp [nominal, distAt]

private theorem model_norm_ratio (w : ℂ) :
    ‖modelQuotient w‖ = listProd gamma (nominal w) / listProd delta (nominal w) := by
  simp only [modelQuotient, norm_div, model_product_norm]

theorem model_quotient_strict (w : ℂ) (hw : 43/50 ≤ |w.im|) :
    ‖modelQuotient w‖ < 9/5 := by
  rw [model_norm_ratio]
  have hs : 860000^2 ≤ (1000000*w.im)^2 := by
    have hh := (sq_le_sq₀ (by norm_num : (0:ℝ) ≤ 43/50) (abs_nonneg w.im)).2 hw
    rw [sq_abs] at hh
    nlinarith only [hh]
  have h := exterior (1000000*w.re) ((1000000*w.im)^2) hs
  rw [squared_product,squared_product] at h
  change 25*((1000000^2)^12 * _) < 81*((1000000^2)^12 * _) at h
  have hg := listProd_pos gamma (nominal w) (fun n => dist_pos w hw _)
  have hd := listProd_pos delta (nominal w) (fun n => dist_pos w hw _)
  apply (div_lt_iff₀ hd).2
  have hh : (5*listProd gamma (nominal w))^2 < (9*listProd delta (nominal w))^2 := by
    linarith only [h]
  have := (sq_lt_sq₀ (by positivity) (by positivity)).1 hh
  linarith

private theorem node_quotient_norm (s : List Entry) (w : ℂ) :
    ‖nodeQuotient s w‖ = listProd s (ratio w) := by
  induction s with
  | nil => simp [nodeQuotient, listProd]
  | cons e s ih =>
    simp only [nodeQuotient, listProd, List.map_cons, List.prod_cons, norm_mul, norm_div] at ih ⊢
    rw [ih]
    rfl

theorem node_quotient_strict_transfer (s : List Entry)
    (hg : s.map Entry.G = Certificate.gamma) (hd : s.map Entry.D = Certificate.delta)
    (w : ℂ) (hw : 43/50 ≤ |w.im|) :
    let B : ℝ := (9/5) * (1 + 1/430000)^24
    ‖nodeQuotient s w‖ < B ∧ B < 181/100 := by
  dsimp only
  have hlen : s.length = 12 := by simpa [Certificate.gamma] using congrArg List.length hg
  have hu := list_ratio_bound s w hw
  rw [hg, hd, hlen, ← model_norm_ratio] at hu
  rw [node_quotient_norm]
  constructor
  · calc
      _ ≤ _ := hu
      _ < (stretch ^ 2) ^ 12 * (9/5) :=
        mul_lt_mul_of_pos_left (model_quotient_strict w hw) (by norm_num [stretch])
      _ = _ := by norm_num [stretch]
  · norm_num

#print axioms nodeQuotient
#print axioms modelFactorProduct
#print axioms modelQuotient
#print axioms model_quotient_strict
#print axioms node_quotient_strict_transfer

end Turan.Small56

