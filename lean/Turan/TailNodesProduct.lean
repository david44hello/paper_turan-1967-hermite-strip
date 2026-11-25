-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.TailDefs
import Mathlib.Tactic

noncomputable section
namespace Turan

/-- The two disjoint families of selected roots contribute at most the entire
negative logarithm; every other factor has modulus strictly between zero and one. -/
theorem tail_node_pair_sum_le (j N : ℕ) (h0 : psi j (-1/2) ≠ 0)
    (d e : Fin N → ℝ) (hd : Function.Injective d) (he : Function.Injective e)
    (hmem : ∀ i, 0 < d i ∧ 0 < e i ∧
      (((-(1:ℝ)/2+d i : ℝ) : ℂ) ∈ (hermite j).roots.toFinset.filter
        (fun s => s.im = 0 ∧ -(7:ℝ)/2 ≤ s.re ∧ s.re ≤ 5/2)) ∧
      (((-(1:ℝ)/2-e i : ℝ) : ℂ) ∈ (hermite j).roots.toFinset.filter
        (fun s => s.im = 0 ∧ -(7:ℝ)/2 ≤ s.re ∧ s.re ≤ 5/2))) :
    (∑ i, (-Real.log (Real.tanh ((11*Real.pi/28)*d i)) -
            Real.log (Real.tanh ((11*Real.pi/28)*e i)))) ≤ -Real.log (nodeProduct j) := by
  classical
  let w : ℝ := -1/2
  let α := 11*Real.pi/28
  let S := (hermite j).roots.toFinset.filter
    (fun s => s.im = 0 ∧ -(7:ℝ)/2 ≤ s.re ∧ s.re ≤ 5/2)
  let f (s : ℂ) := |Real.tanh (Real.pi * (w-s.re)/(4*(7/11)))|
  let F (s : ℂ) := -Real.log (f s)
  let r (i : Fin N) : ℂ := (w+d i : ℝ)
  let l (i : Fin N) : ℂ := (w-e i : ℝ)
  let R := Finset.univ.image r
  let L := Finset.univ.image l
  have r_inj : Function.Injective r := by
    intro i k h
    exact hd (add_left_cancel (Complex.ofReal_inj.mp h : w+d i = w+d k))
  have l_inj : Function.Injective l := by
    intro i k h
    exact he (sub_right_inj.mp (Complex.ofReal_inj.mp h : w-e i = w-e k))
  have disj : Disjoint R L := by
    apply Finset.disjoint_left.mpr
    intro z hz hl
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hl
    have : w-e k = w+d i := Complex.ofReal_inj.mp hk
    linarith only [this, (hmem i).1, (hmem k).2.1]
  have hsub : R ∪ L ⊆ S := by
    intro z hz
    rcases Finset.mem_union.mp hz with hr | hl
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
      exact (hmem i).2.2.1
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hl
      exact (hmem i).2.2.2
  have all_pos (s : ℂ) (hs : s ∈ S) : 0 < f s := by
    have hs' := Finset.mem_filter.mp hs
    have hsw : w ≠ s.re := by
      intro h
      have heq : s = (w:ℂ) := Complex.ext h.symm hs'.2.1
      have hev := Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hs'.1)
      rw [heq] at hev
      apply h0
      have hw : (w:ℂ) = -1/2 := by norm_num [w]
      rw [← hw]
      exact div_eq_zero_iff.mpr (Or.inl hev)
    apply abs_pos.mpr
    rw [Real.tanh_eq_sinh_div_cosh]
    apply div_ne_zero _ (Real.cosh_pos _).ne'
    apply Real.sinh_ne_zero.mpr
    exact div_ne_zero (mul_ne_zero Real.pi_pos.ne' (sub_ne_zero.mpr hsw)) (by norm_num)
  have all_nonneg (s : ℂ) : 0 ≤ F s :=
    neg_nonneg.mpr (Real.log_nonpos (abs_nonneg _) (Real.abs_tanh_lt_one _).le)
  have total : -Real.log (nodeProduct j) = ∑ s ∈ S, F s := by
    change -Real.log (∏ s ∈ S, f s) = _
    rw [Real.log_prod (fun s hs => (all_pos s hs).ne'), ← Finset.sum_neg_distrib]
  have fr (i : Fin N) : F (r i) = -Real.log (Real.tanh (α*d i)) := by
    change -Real.log |Real.tanh (Real.pi*(w-(w+d i))/(4*(7/11)))| = _
    rw [show Real.pi*(w-(w+d i))/(4*(7/11)) = -(α*d i) by dsimp [α]; ring,
      Real.tanh_neg, abs_neg, Real.log_abs]
  have fl (i : Fin N) : F (l i) = -Real.log (Real.tanh (α*e i)) := by
    change -Real.log |Real.tanh (Real.pi*(w-(w-e i))/(4*(7/11)))| = _
    rw [show Real.pi*(w-(w-e i))/(4*(7/11)) = α*e i by dsimp [α]; ring,
      Real.log_abs]
  rw [total]
  calc
    _ = (∑ i, F (r i)) + ∑ i, F (l i) := by
      simp only [fr, fl, α, sub_eq_add_neg, Finset.sum_add_distrib]
    _ = ∑ s ∈ R ∪ L, F s := by
      rw [Finset.sum_union disj, Finset.sum_image r_inj.injOn, Finset.sum_image l_inj.injOn]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun s _ _ => all_nonneg s)

end Turan
