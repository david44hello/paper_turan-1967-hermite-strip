-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Small56Transfer

noncomputable section
open scoped Topology
open Polynomial
namespace Turan.Small56

def shiftedNodeValue (l : ℕ) (w : ℝ) : ℂ := (hermite l).eval ((w : ℂ) - 1/2) / w

def nodeDividedDifference (l : ℕ) (g d : ℝ) : ℂ :=
  (shiftedNodeValue l g - shiftedNodeValue l d) / ((g : ℂ) - d)

def quadraticRemainder (l : ℕ) (S p : ℝ) : Polynomial ℂ :=
  ((hermite l).comp (X - C (1/2))) %ₘ (X^2 - C (S : ℂ) * X + C (p : ℂ))

private theorem node_sum_product {S p g d : ℝ} (hg : g^2 - S*g + p = 0)
    (hd : d^2 - S*d + p = 0) (hne : g ≠ d) : S = g+d ∧ p = g*d := by
  have h : (g-d)*(g+d-S) = 0 := by linear_combination hg - hd
  have hs : S = g + d := by linarith only [(mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)]
  refine ⟨hs, ?_⟩
  rw [hs] at hg
  nlinarith only [hg]

theorem divided_difference_of_remainder (l : ℕ) (S p g d : ℝ)
    (hg : g^2 - S*g + p = 0) (hd : d^2 - S*d + p = 0)
    (hne : g ≠ d) (hg0 : g ≠ 0) (hd0 : d ≠ 0) :
    let rem := quadraticRemainder l S p
    (∀ w ∈ ({g, d} : Set ℝ), shiftedNodeValue l w = rem.coeff 0 / w + rem.coeff 1) ∧
    nodeDividedDifference l g d = -(rem.coeff 0) / p := by
  let q : Polynomial ℂ := X^2 - C (S : ℂ) * X + C (p : ℂ)
  let f := (hermite l).comp (X - C (1/2))
  let r := f %ₘ q
  have hq : q = C (1 : ℂ) * X^2 + C (-(S : ℂ)) * X + C (p : ℂ) := by simp [q, sub_eq_add_neg]
  have hmon : q.Monic := by rw [Monic, hq, leadingCoeff_quadratic one_ne_zero]
  have hdeg : q.natDegree = 2 := by rw [hq, natDegree_quadratic one_ne_zero]
  have hne1 : q ≠ 1 := by intro h; simp [h] at hdeg
  have hrdeg := natDegree_modByMonic_lt f hmon hne1
  rw [hdeg] at hrdeg
  have hr : r = C (r.coeff 1) * X + C (r.coeff 0) :=
    eq_X_add_C_of_natDegree_le_one (Nat.le_of_lt_succ hrdeg)
  have val (w : ℝ) (hw : w^2-S*w+p=0) (hw0 : w ≠ 0) :
      shiftedNodeValue l w = r.coeff 0 / w + r.coeff 1 := by
    have hw' : q.eval (w : ℂ) = 0 := by
      simp only [q, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
      exact_mod_cast hw
    have he : r.eval (w : ℂ) = f.eval (w : ℂ) := by
      simp [r, modByMonic_eq_sub_mul_div, eval_sub, eval_mul, hw']
    rw [hr] at he
    simp only [eval_add, eval_mul, eval_C, eval_X, f, eval_comp, eval_sub] at he
    unfold shiftedNodeValue
    rw [← he]
    have hc0 : (w : ℂ) ≠ 0 := by exact_mod_cast hw0
    field_simp
    ring
  have vg := val g hg hg0
  have vd := val d hd hd0
  constructor
  · intro w hw
    rcases (show w = g ∨ w = d by simpa using hw) with rfl | rfl <;> assumption
  · change (shiftedNodeValue l g - shiftedNodeValue l d) / ((g : ℂ)-d) = -(r.coeff 0) / p
    rw [vg, vd, (node_sum_product hg hd hne).2]
    push_cast
    have hc : (g : ℂ) - d ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
    have hu : (g : ℂ) ≠ 0 := by exact_mod_cast hg0
    have hv : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
    field_simp
    ring

theorem nodes_iff_zero_remainders (S p g d : ℝ)
    (hg : g^2 - S*g + p = 0) (hd : d^2 - S*d + p = 0)
    (hne : g ≠ d) (hg0 : g ≠ 0) (hd0 : d ≠ 0) :
    (nodeDividedDifference 5 g d = 0 ∧ nodeDividedDifference 6 g d = 0) ↔
      remainder5 S p = 0 ∧ remainder6 S p = 0 := by
  obtain ⟨rfl, rfl⟩ := node_sum_product hg hd hne
  have hc : (g : ℂ) - d ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  have hu : (g : ℂ) ≠ 0 := by exact_mod_cast hg0
  have hv : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
  have hdif5 : nodeDividedDifference 5 g d = -(remainder5 (g+d) (g*d) : ℂ) / (g*d : ℝ) := by
    norm_num [nodeDividedDifference, shiftedNodeValue, hermite, eval_mul, eval_sub, nsmul_eq_mul, remainder5]
    field_simp
    ring
  have hdif6 : nodeDividedDifference 6 g d = -(remainder6 (g+d) (g*d) : ℂ) / (g*d : ℝ) := by
    norm_num [nodeDividedDifference, shiftedNodeValue, hermite, eval_mul, eval_sub, nsmul_eq_mul, remainder6]
    field_simp
    ring
  rw [hdif5, hdif6]
  simp [hg0, hd0]

#print axioms shiftedNodeValue
#print axioms nodeDividedDifference
#print axioms quadraticRemainder
#print axioms divided_difference_of_remainder
#print axioms nodes_iff_zero_remainders

end Turan.Small56

