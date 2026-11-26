module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Degree
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Polynomial
namespace Turan

private theorem esymm_one_sum (r : Multiset ℂ) : r.esymm 1 = r.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]

/-- The second Newton identity, with multiplicities retained in the multiset. -/
private theorem root_square_sum (r : Multiset ℂ) :
    (r.map (· ^ 2)).sum = r.sum ^ 2 - 2 * r.esymm 2 := by
  induction r using Multiset.induction_on with
  | empty => simp [Multiset.esymm_of_card_lt (show (0 : Multiset ℂ).card < 2 by decide)]
  | cons x r ih =>
    have h : (x ::ₘ r).esymm 2 = r.esymm 2 + x * r.sum := by
      simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.powersetCard_one,
        Multiset.map_map]
      simpa using (Multiset.sum_map_mul_left (f := id) (a := x) (s := r))
    simp only [Multiset.map_cons, Multiset.sum_cons, ih, h]
    ring

/-- A multiplicity-indexed factorization and the two power sums of the quintic. -/
theorem quintic_factorization (a b : ℂ) (hb : b ≠ 0) :
    ∃ z : Fin 5 → ℂ,
      family 2 5 a b = C (32 * b) * ∏ i, (X - C (z i)) ∧
      (∑ i, z i) = 0 ∧ (∑ i, z i ^ 2) = 10 := by
  let p := family 2 5 a b
  have hd : p.natDegree = 5 := by simp [p, family_degree 2 5 (by decide) (by decide), hb]
  have h₂ : hermite 2 = 4 * X ^ 2 - 2 := by
    norm_num [hermite, nsmul_eq_mul]
    ring
  have h₅ : hermite 5 = 32 * X ^ 5 - 160 * X ^ 3 + 120 * X := by
    norm_num [hermite, nsmul_eq_mul]
    ring
  have hc : p.coeff 5 = 32 * b ∧ p.coeff 4 = 0 ∧ p.coeff 3 = -160 * b := by
    refine ⟨?_, ?_, ?_⟩ <;>
      norm_num [p, family, h₂, h₅, coeff_add, coeff_sub, coeff_C_mul, coeff_ofNat_mul,
        coeff_X_pow, coeff_X, coeff_one] <;> ring
  have hl : p.leadingCoeff = 32 * b := by rw [leadingCoeff, hd, hc.1]
  have hne : 32 * b ≠ 0 := mul_ne_zero (by norm_num) hb
  have split := IsAlgClosed.splits p
  have hcard := split.natDegree_eq_card_roots.symm.trans hd
  have h₄ := coeff_eq_esymm_roots_of_splits split (k := 4) (by omega)
  have h₃ := coeff_eq_esymm_roots_of_splits split (k := 3) (by omega)
  norm_num [hd, hl, hc.2.1, hc.2.2, esymm_one_sum] at h₄ h₃
  have hsum : p.roots.sum = 0 := h₄.resolve_left hb
  have hsecond : p.roots.esymm 2 = -5 := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show (32 * b) * (p.roots.esymm 2 - -5) = 0 by
      linear_combination -h₃)).resolve_left hne
  obtain ⟨n, z, hz⟩ := List.exists_iff_exists_tuple.mp
    (show ∃ l : List ℂ, (l : Multiset ℂ) = p.roots from ⟨_, p.roots.coe_toList⟩)
  have hn : n = 5 := by simpa [← hz] using hcard
  subst n
  refine ⟨z, ?_, ?_, ?_⟩
  · calc
      p = _ := split.eq_prod_roots
      _ = _ := by
        simp only [hl, ← hz, Multiset.map_coe, Multiset.prod_coe, List.map_ofFn,
          List.prod_ofFn, Function.comp_apply]
  · simpa only [← hz, Multiset.sum_coe, List.sum_ofFn] using hsum
  · have hsq := root_square_sum p.roots
    rw [hsum, hsecond] at hsq
    norm_num only [← hz, Multiset.map_coe, Multiset.sum_coe, List.map_ofFn,
      List.sum_ofFn, Function.comp_apply] at hsq
    exact hsq

end Turan
