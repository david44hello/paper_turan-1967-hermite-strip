-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.TailStripMaximum
import Turan.TailStripRational
import Turan.TailStripWeight

noncomputable section
namespace Turan

open TailStrip

theorem lemma_sixteen_of_line_bound (n m : ℕ) (hm : 450 ≤ m) (hhalf : m ≤ 2*n) (hnm : n < m)
    (a b : ℂ) (hs : emptyStrip (normalizedFamily n m a b) (87/100)) (j : ℕ) (hj : j=n ∨ j=m)
    (hline : ∀ z : ℂ, |z.im| = 7/11 →
      ‖modeQuotient n m j a b z‖ ≤ 4200*(omega m z)^4 / ((j:ℝ)*(m-n:ℝ))) :
    ‖modeQuotient n m j a b (-1/2)‖ ≤ 25000*(m:ℝ)^2/((j:ℝ)*(m-n:ℝ))*nodeProduct j := by
  classical
  let w : ℂ := -1/2
  let t := (hermite j).roots.toFinset.filter
      (fun s => s.im = 0 ∧ -(7:ℝ)/2 ≤ s.re ∧ s.re ≤ 5/2)
  let u := modeQuotient n m j a b
  let v := fun z => u z / weightBase m z ^ 4
  let D := (j:ℝ)*(m-n:ℝ)
  let K : ℝ := 4200*(11/10)^4
  have hD : 0 < D := by
    have hjpos : 0 < j := by rcases hj with rfl | rfl <;> omega
    exact mul_pos (by exact_mod_cast hjpos) (sub_pos.mpr (by exact_mod_cast hnm))
  obtain ⟨hud,hug⟩ := mode_regular (by omega : 2 ≤ n) hnm hj a b hs
  have hw1 (z : ℂ) (hz : z ∈ strip) : 1 ≤ ‖weightBase m z‖^4 :=
    one_le_pow₀ (one_le_weight hm hz)
  have hvd : DifferentiableOn ℂ v strip := by
    apply hud.div
    · unfold weightBase; fun_prop
    · intro z hz
      exact pow_ne_zero _ (norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (one_le_weight hm hz)))
  have hvg : farBound v := by
    obtain ⟨C,R,h⟩ := hug
    refine ⟨C,R, fun z hz hstrip => ?_⟩
    rw [show v z = u z / weightBase m z ^ 4 from rfl, norm_div, norm_pow]
    exact (div_le_self (norm_nonneg _) (hw1 z hstrip)).trans (h z hz hstrip)
  have hvl (z : ℂ) (hz : |z.im| = height) : ‖v z‖ ≤ K / D :=
    weighted_line_bound hm hD hline hz
  have hvn (s : ℂ) (hs' : s ∈ t) : s.im = 0 ∧ v s = 0 := by
    obtain ⟨hr,hc⟩ := Finset.mem_filter.mp hs'
    have he : (hermite j).eval s = 0 := Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr)
    exact ⟨hc.1, by simp [v, u, modeQuotient, psi, he]⟩
  have hw : w ∈ strip := by change |(-1/2 : ℂ).im| ≤ height; norm_num
  have hp : (∏ s ∈ t, ‖factor s.re w‖) = nodeProduct j := by
    unfold nodeProduct
    apply Finset.prod_congr rfl
    intro s _
    have hwreal : w = ((-(1:ℝ)/2 : ℝ) : ℂ) := by push_cast; rfl
    rw [hwreal, factor_real, Complex.norm_real, Real.norm_eq_abs]
  have hprod : 0 ≤ nodeProduct j := by
    unfold nodeProduct
    exact Finset.prod_nonneg (fun _ _ => abs_nonneg _)
  have hb := maximum_with_zeros t v (K / D) hvd hvg hvl hvn w hw
  rw [hp] at hb
  change ‖u w / weightBase m w ^ 4‖ ≤ _ at hb
  rw [norm_div, norm_pow, div_le_iff₀ (lt_of_lt_of_le zero_lt_one (hw1 w hw))] at hb
  calc
    ‖u w‖ ≤ K / D * nodeProduct j * ‖weightBase m w‖^4 := hb
    _ = (K * ‖weightBase m w‖^4) / D * nodeProduct j := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (center_weight hm) hD.le) hprod

end Turan
