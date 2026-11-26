module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Polynomial
namespace Turan

private def nodePoly (S : ℝ) := 2*S^3 - 5*S^2 - 4*S + 1

private theorem node_decreases : StrictAntiOn nodePoly (Set.Icc 0 (1/4)) := by
  intro x hx y hy hxy
  have hb : 2*(x^2+x*y+y^2)-5*(x+y)-4 < 0 := by
    nlinarith [hx.1, hy.1, mul_nonneg hx.1 (sub_nonneg.mpr hx.2),
      mul_nonneg hy.1 (sub_nonneg.mpr hy.2),mul_nonneg hx.1 (sub_nonneg.mpr hy.2)]
  unfold nodePoly
  nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr hxy) hb]

theorem quintic_node_exists :
    ∃! S : ℝ, 0 < S ∧ S < 1/4 ∧ 2*S^3 - 5*S^2 - 4*S + 1 = 0 := by
  obtain ⟨S, hS, hzero⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1/4)
    (f := nodePoly) (by unfold nodePoly; fun_prop)
    (show (0:ℝ) ∈ Set.Icc (nodePoly (1/4)) (nodePoly 0) by norm_num [nodePoly])
  refine ⟨S, ⟨lt_of_le_of_ne hS.1 ?_, lt_of_le_of_ne hS.2 ?_, hzero⟩, ?_⟩
  · rintro rfl; norm_num [nodePoly] at hzero
  · rintro rfl; norm_num [nodePoly] at hzero
  · rintro r ⟨hr₀,hr₁,hr⟩
    exact node_decreases.injOn ⟨hr₀.le,hr₁.le⟩ hS (hr.trans hzero.symm)

theorem lemma_twenty_three_nodes (S : ℝ) (hS : 0 < S ∧ S < 1/4 ∧ 2*S^3 - 5*S^2 - 4*S + 1 = 0) :
    let X := (S-1)/2
    let s := Real.sqrt (1+S^2)/2
    let left := X-s
    let right := X+s
    S < 21/100 ∧ -1/2 < X ∧ X < 0 ∧ |X| < 1/2 ∧
    1/2 < s ∧ s < 511/1000 ∧ left + 1/2 < 0 ∧ 0 < right + 1/2 ∧
    ∀ j ∈ ({2,5} : Finset ℕ),
      (hermite j).eval (left:ℂ) / (2*(left:ℂ)+1) =
      (hermite j).eval (right:ℂ) / (2*(right:ℂ)+1) := by
  rcases hS with ⟨hpos,hsmall,hroot⟩
  have h₂ : S < 21/100 := by
    by_contra! h
    have hbad := node_decreases.antitoneOn (show (21/100:ℝ) ∈ Set.Icc 0 (1/4) by norm_num)
      ⟨hpos.le,hsmall.le⟩ h
    norm_num [nodePoly,hroot] at hbad
  set T := Real.sqrt (1+S^2) with hT
  have hT2 : T^2 = 1+S^2 := Real.sq_sqrt (by positivity)
  have hTpos : 0 ≤ T := Real.sqrt_nonneg _
  have hTlo : 1 < T := by nlinarith [sq_pos_of_pos hpos]
  have hThi : T/2 < 511/1000 := by
    nlinarith [mul_pos (sub_pos.mpr h₂) (show 0 < 21/100+S by linarith)]
  dsimp only
  refine ⟨h₂, by linarith, by linarith, abs_lt.mpr ⟨by linarith,by linarith⟩,
    by linarith, hThi, by linarith, by linarith, ?_⟩
  intro j hj
  have hL : (2:ℂ)*(((S-1)/2-T/2:ℝ):ℂ)+1 ≠ 0 := by
    exact_mod_cast (show 2*((S-1)/2-T/2)+1 ≠ 0 by linarith)
  have hR : (2:ℂ)*(((S-1)/2+T/2:ℝ):ℂ)+1 ≠ 0 := by
    exact_mod_cast (show 2*((S-1)/2+T/2)+1 ≠ 0 by linarith)
  apply (div_eq_div_iff hL hR).2
  have ht : (T:ℂ)^2 = 1+(S:ℂ)^2 := by exact_mod_cast hT2
  have hs : 2*(S:ℂ)^3-5*(S:ℂ)^2-4*(S:ℂ)+1=0 := by exact_mod_cast hroot
  simp only [Finset.mem_insert,Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · norm_num [hermite,eval_sub,eval_add,eval_mul,nsmul_eq_mul]
    linear_combination 2*(T:ℂ)*ht
  · norm_num [hermite,eval_sub,eval_add,eval_mul,nsmul_eq_mul]
    linear_combination 2*(T:ℂ)*(4*(S:ℂ)^3-15*(S:ℂ)^2+4*(S:ℂ)*(T:ℂ)^2-16*(S:ℂ)-5*(T:ℂ)^2+45)*ht +
      8*(T:ℂ)*hs

end Turan
