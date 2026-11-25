-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.UpperTailNodesWeight
import Turan.UpperTailNodesOrder

noncomputable section
open Real
namespace Turan.UpperTailNodes

private theorem reciprocal_sinh (t : ℝ) (ht : 0 < t) : 1/t-t/6 ≤ 1/sinh t := by
  rcases lt_or_ge (t^2) 6 with h | h
  · exact (small_sinh_series t ht h).2.2.2
  · obtain ⟨h₁,h₂⟩ := large_sinh_sign t ht h
    exact h₁.trans h₂.le

theorem five_term_linear (j : ℕ) (hj : 225 ≤ j) (h0 : psi j (-1/2) ≠ 0) :
    let slope := 2*0.998*sigmaFive/(alpha*Real.pi)
    let penalty := 5*alpha*eta j/3
    let retained := 2*0.998*(sigmaFive/(alpha*eta j)-5*alpha*eta j/6)
    slope*Real.sqrt (2*(j:ℝ)-11.25)-penalty ≤ retained ∧
    retained ≤ -Real.log (nodeProduct j) ∧
    sigmaFive = 117469/99225 ∧ 1.18386 < sigmaFive ∧
    alpha < 1.2342 ∧ alpha*Real.pi < 3.8774 ∧
    0.6094 < (2.36299/3.8774 : ℝ) ∧ (2.36299/3.8774 : ℝ) < slope ∧
    penalty < 5*1.2342*0.151/3 ∧ (5*1.2342*0.151/3 : ℝ) < 0.3107 := by
  dsimp only
  let h := eta j
  let N := nodeCount j
  obtain ⟨hh,hhu⟩ := eta_bounds j hj
  have hp : 0 < h := hh
  have ha := alpha_pos
  have hσ : sigmaFive = 117469/99225 := by norm_num [sigmaFive, Finset.sum_range_succ, oddFreq]
  have hα : alpha < 1.2342 := by unfold alpha; linarith only [pi_lt_d6]
  have hαπ : alpha*Real.pi < 3.8774 := by
    unfold alpha
    nlinarith only [mul_pos (sub_pos.mpr pi_lt_d6) (show 0 < 3.141593+Real.pi by positivity)]
  have hcoef : 2*0.998*sigmaFive/(alpha*Real.pi)*sqrt (2*(j:ℝ)-11.25) = 2*0.998*sigmaFive/(alpha*h) := by
    have hj' : (225:ℝ) ≤ j := by exact_mod_cast hj
    have hs := sqrt_pos.mpr (show 0 < 2*(j:ℝ)-11.25 by linarith)
    dsimp [h,eta]
    field_simp [ha.ne', pi_ne_zero, hs.ne']
  have hret (i : ℕ) (hi : i < 5) :
      2*0.998*((1/(oddFreq i)^2)/(alpha*h)-alpha*h/6) ≤ oddContribution N h i := by
    let l := oddFreq i
    let t := alpha*l*h
    have hl : 0 < l := by dsimp [l,oddFreq]; positivity
    have ht : 0 < t := mul_pos (mul_pos ha hl) hh
    obtain ⟨_,_,_,hlo,hrem⟩ := numerator_chain j hj ⟨i,hi⟩
    have hnum : 0.998 ≤ 1-exp (-2*alpha*l*(N:ℝ)*h) := hlo.le.trans hrem
    calc
      _ = (2*0.998/l)*(1/t-t/6) := by
        change 2*0.998*(1/l^2/(alpha*h)-alpha*h/6) = (2*0.998/l)*(1/(alpha*l*h)-(alpha*l*h)/6)
        field_simp [hl.ne', ha.ne', hp.ne']
        <;> ring
      _ ≤ (2*0.998/l)*(1/sinh t) := mul_le_mul_of_nonneg_left (reciprocal_sinh t ht) (by positivity)
      _ ≤ (2*(1-exp (-2*alpha*l*(N:ℝ)*h))/l)*(1/sinh t) := by gcongr
      _ = _ := by unfold oddContribution; dsimp [l,t]; ring
  have hsum := Finset.sum_le_sum (s := Finset.range 5) (fun i hi => hret i (Finset.mem_range.mp hi))
  have hsum_eq : (∑ i ∈ Finset.range 5, 2*0.998*((1/(oddFreq i)^2)/(alpha*h)-alpha*h/6)) =
      2*0.998*(sigmaFive/(alpha*h)-5*alpha*h/6) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div]
    simp only [sigmaFive, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat]
    ring
  rw [hsum_eq] at hsum
  have hnon (i : ℕ) : 0 ≤ oddContribution N h i := by
    have hl : 0 < oddFreq i := by unfold oddFreq; positivity
    have hz : -2*alpha*oddFreq i*(N:ℝ)*h ≤ 0 := by
      have hh' : 0 < h := hh
      have hp : 0 ≤ 2*alpha*oddFreq i*(N:ℝ)*h := by positivity
      linarith only [hp]
    unfold oddContribution
    exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (exp_le_one_iff.mpr hz)))
      (mul_pos hl (sinh_pos_iff.mpr (mul_pos (mul_pos ha hl) hh))).le
  have hts := (full_midpoint_series N h hh).summable.sum_le_tsum (Finset.range 5) (fun i _ => hnon i)
  refine ⟨?_, (hsum.trans hts).trans (full_node_lower_bound j hj h0).2, hσ, by rw [hσ]; norm_num,
    hα, hαπ, by norm_num, ?_, ?_, by norm_num⟩
  · rw [hcoef]
    change _ - 5*alpha*h/3 ≤ _
    calc
      _ = 2*0.998*(sigmaFive/(alpha*h)) - 2*(5*alpha*h/6) := by ring
      _ ≤ 2*0.998*(sigmaFive/(alpha*h)) - (2*0.998)*(5*alpha*h/6) :=
        sub_le_sub_left (mul_le_mul_of_nonneg_right (by norm_num) (by positivity)) _
      _ = _ := by ring
  · rw [hσ, lt_div_iff₀ (mul_pos ha pi_pos)]
    linarith only [hαπ]
  · have := mul_lt_mul_of_pos_right hα hh
    linarith only [this, hhu]

end Turan.UpperTailNodes
