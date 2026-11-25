-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Small56Transfer
import Turan.Small56Certificate

noncomputable section
open scoped Topology
open Polynomial
namespace Turan.Small56

theorem table_entry_strict_lower (e : Entry)
    (hrow : (e.G, e.D) ∈ Certificate.gamma.zip Certificate.delta) :
    lower e < |e.g / e.d| := by
  have rows : (e.G = -2048845 ∧ e.D = -75660) ∨ (e.G = 2907699 ∧ e.D = -1805569) ∨
      (e.G = 2222962 ∧ e.D = -626158) ∨ (e.G = -555650 ∧ e.D = 2384521) ∨
      (e.G = 360845 ∧ e.D = 2327565) := by
    simpa [Certificate.gamma, Certificate.delta, List.zip, List.zipWith, or_assoc] using hrow
  by_contra! hf
  rw [abs_div, div_le_iff₀ (abs_pos.mpr (entry_d_ne e))] at hf
  have hg := abs_le.mp e.cert.1
  have hd := abs_le.mp e.cert.2.1
  have hn := e.cert.2.2 1 0
  rcases rows with h | h | h | h | h
  all_goals
    rcases h with ⟨hG,hD⟩
    norm_num [hG, hD, lower] at hg hd hf
    first | rw [abs_of_pos (by linarith only [hg] : 0 < e.g)] at hf
          | rw [abs_of_neg (by linarith only [hg] : e.g < 0)] at hf
    first | rw [abs_of_pos (by linarith only [hd] : 0 < e.d)] at hf
          | rw [abs_of_neg (by linarith only [hd] : e.d < 0)] at hf
  · have hgc : e.g = -2048843 / 1000000 := by linarith only [hg.1, hg.2, hd.1, hd.2, hf]
    have hdc : e.d = -75662 / 1000000 := by linarith only [hg.1, hg.2, hd.1, hd.2, hf]
    norm_num [hgc, hdc, family, hermite, nsmul_eq_mul, eval_mul, eval_sub] at hn
  · have hgc : e.g = 2907697 / 1000000 := by linarith only [hg.1, hg.2, hd.1, hd.2, hf]
    have hdc : e.d = -1805571 / 1000000 := by linarith only [hg.1, hg.2, hd.1, hd.2, hf]
    norm_num [hgc, hdc, family, hermite, nsmul_eq_mul, eval_mul, eval_sub] at hn
  · have hgc : e.g = 2222960 / 1000000 := by linarith only [hg.1, hg.2, hd.1, hd.2, hf]
    have hdc : e.d = -626160 / 1000000 := by linarith only [hg.1, hg.2, hd.1, hd.2, hf]
    norm_num [hgc, hdc, family, hermite, nsmul_eq_mul, eval_mul, eval_sub] at hn
  · have hgc : e.g = -555648 / 1000000 := by linarith only [hg.1, hg.2, hd.1, hd.2, hf]
    have hdc : e.d = 2384523 / 1000000 := by linarith only [hg.1, hg.2, hd.1, hd.2, hf]
    norm_num [hgc, hdc, family, hermite, nsmul_eq_mul, eval_mul, eval_sub] at hn
  · have hgc : e.g = 360843 / 1000000 := by linarith only [hg.1, hg.2, hd.1, hd.2, hf]
    have hdc : e.d = 2327567 / 1000000 := by linarith only [hg.1, hg.2, hd.1, hd.2, hf]
    norm_num [hgc, hdc, family, hermite, nsmul_eq_mul, eval_mul, eval_sub] at hn

#print axioms table_entry_strict_lower

end Turan.Small56

