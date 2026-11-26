module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs

@[expose] public section

noncomputable section
open Polynomial
namespace Turan

/-- A nonconstant complex polynomial attains the minimum height of its zeros. -/
theorem polynomial_has_lowest_zero (p : Polynomial ℂ) (hp : 0 < p.natDegree) :
    ∃ z : ℂ, p.eval z = 0 ∧ ∀ w : ℂ, p.eval w = 0 → |z.im| ≤ |w.im| := by
  have hfinite := finite_setOfPred_isRoot (ne_zero_of_natDegree_gt hp)
  have hroot := Complex.exists_root (natDegree_pos_iff_degree_pos.mp hp)
  exact Set.exists_min_image {z | p.IsRoot z} (fun z => |z.im|) hfinite hroot

private theorem degree_two_X : (2 * X : Polynomial ℂ).natDegree = 1 := by
  simp

private theorem leadingCoeff_two_X : (2 * X : Polynomial ℂ).leadingCoeff = 2 := by
  simpa only [map_ofNat] using leadingCoeff_C_mul_X (2 : ℂ)

/-- The recurrence raises the degree by one and doubles the leading coefficient. -/
theorem hermite_degree (j : ℕ) :
    (hermite j).natDegree = j ∧ (hermite j).leadingCoeff = 2 ^ j := by
  induction j using Nat.twoStepInduction with
  | zero => simp [hermite]
  | one => simpa [hermite] using And.intro degree_two_X leadingCoeff_two_X
  | more k hk hnext =>
    have hnext_ne : hermite (k + 1) ≠ 0 := by
      apply ne_zero_of_natDegree_gt (n := 0)
      rw [hnext.1]
      omega
    have htop : (2 * X * hermite (k + 1)).natDegree = k + 2 := by
      rw [natDegree_mul (mul_ne_zero (by norm_num) X_ne_zero) hnext_ne,
        degree_two_X, hnext.1]
      omega
    have hlower : ((2 * (k + 1)) • hermite k).natDegree <
        (2 * X * hermite (k + 1)).natDegree := by
      rw [htop]
      exact (natDegree_smul_le _ _).trans_lt (by rw [hk.1]; omega)
    rw [hermite, natDegree_sub_eq_left_of_natDegree_lt hlower,
      leadingCoeff_sub_of_degree_lt (degree_lt_degree hlower)]
    refine ⟨htop, ?_⟩
    rw [leadingCoeff_mul, leadingCoeff_two_X, hnext.2, pow_succ (2 : ℂ) (k + 1), mul_comm]

/-- The last nonzero term determines the degree since 1 < n < m. -/
theorem family_degree (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m) (a b : ℂ) :
    (family n m a b).natDegree = if b ≠ 0 then m else if a ≠ 0 then n else 1 := by
  have hlinear : (1 + 2 * X : Polynomial ℂ).natDegree = 1 := by
    rw [natDegree_add_eq_right_of_natDegree_lt, degree_two_X]
    simp
  have hlower : (1 + 2 * X + C a * hermite n).natDegree = if a ≠ 0 then n else 1 := by
    by_cases ha : a ≠ 0
    · rw [ite_eq_left ha, natDegree_add_eq_right_of_natDegree_lt, natDegree_C_mul ha,
        (hermite_degree n).1]
      rw [hlinear, natDegree_C_mul ha, (hermite_degree n).1]
      omega
    · simp [not_ne_iff.mp ha, hlinear]
  unfold family
  by_cases hb : b ≠ 0
  · rw [ite_eq_left hb, natDegree_add_eq_right_of_natDegree_lt, natDegree_C_mul hb,
      (hermite_degree m).1]
    rw [hlower, natDegree_C_mul hb, (hermite_degree m).1]
    split <;> omega
  · simp [not_ne_iff.mp hb, hlower]

theorem family_has_lowest_zero (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m) (a b : ℂ) :
    ∃ z : ℂ, (family n m a b).eval z = 0 ∧
      ∀ w : ℂ, (family n m a b).eval w = 0 → |z.im| ≤ |w.im| := by
  apply polynomial_has_lowest_zero
  rw [family_degree n m hn hnm a b]
  split_ifs <;> omega

end Turan
