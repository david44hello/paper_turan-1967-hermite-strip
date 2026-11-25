-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.TailDefs
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

noncomputable section
open Set
namespace Turan.UpperTailNodes

def alpha : ℝ := 11*Real.pi/28
def eta (j : ℕ) : ℝ := Real.pi / Real.sqrt (2*(j:ℝ)-11.25)
def nodeCount (j : ℕ) : ℕ := ⌊3 / eta j⌋₊
def center : ℝ := -1/2
def logCoth (v : ℝ) : ℝ := Real.log ((Real.tanh (alpha*v))⁻¹)
def oddFreq (i : ℕ) : ℝ := 2*(i:ℝ)+1

def nearer (j : ℕ) (sign t : ℝ) : ℕ :=
  ((hermite j).roots.toFinset.filter fun z =>
    z.im = 0 ∧ 0 < sign*(z.re-center) ∧ sign*(z.re-center) < t).card

def midpointSum (N : ℕ) (h : ℝ) : ℝ :=
  2 * ∑ i : Fin N, logCoth (((i.val:ℝ)+1/2)*h)

def oddContribution (N : ℕ) (h : ℝ) (i : ℕ) : ℝ :=
  2*(1-Real.exp (-2*alpha*oddFreq i*(N:ℝ)*h)) /
    (oddFreq i*Real.sinh (alpha*oddFreq i*h))

def sigmaFive : ℝ := ∑ i ∈ Finset.range 5, 1/(oddFreq i)^2

theorem alpha_pos : 0 < alpha := by unfold alpha; positivity

theorem eta_bounds (j : ℕ) (hj : 225 ≤ j) : 0 < eta j ∧ eta j < 0.151 := by
  have hj' : (225:ℝ) ≤ j := by exact_mod_cast hj
  have h : (20.9:ℝ) < Real.sqrt (2*(j:ℝ)-11.25) := Real.lt_sqrt_of_sq_lt (by linarith)
  have hp : 0 < Real.sqrt (2*(j:ℝ)-11.25) := by linarith
  exact ⟨div_pos Real.pi_pos hp, (div_lt_iff₀ hp).mpr (by linarith only [h, Real.pi_lt_d4])⟩

theorem numerator_chain (j : ℕ) (hj : 225 ≤ j) (i : Fin 5) :
    eta j < 0.151 ∧ 2.849 < 3-eta j ∧ 3-eta j < (nodeCount j:ℝ)*eta j ∧
    0.998 < 1-Real.exp (-2*alpha*2.849) ∧
    1-Real.exp (-2*alpha*2.849) ≤ 1-Real.exp (-2*alpha*oddFreq i*(nodeCount j:ℝ)*eta j) := by
  obtain ⟨hη, hu⟩ := eta_bounds j hj
  have hN := Nat.lt_floor_add_one (3/eta j)
  change 3/eta j < (nodeCount j:ℝ)+1 at hN
  rw [div_lt_iff₀ hη] at hN
  have hα : 1.23 < alpha := by unfold alpha; linarith [Real.pi_gt_d4]
  have hseven : (500:ℝ) < Real.exp 7 := by
    have hbase : (2.5:ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hpow := pow_lt_pow_left₀ hbase (by norm_num) (by decide : (7:ℕ) ≠ 0)
    rw [show (7:ℝ) = (7:ℕ)*(1:ℝ) by norm_num, Real.exp_nat_mul]
    exact lt_trans (by norm_num) hpow
  have hexp := hseven.trans (Real.exp_lt_exp.mpr (by linarith : 7 < 2*alpha*2.849))
  refine ⟨hu, by linarith, by linarith, ?_, ?_⟩
  · rw [show -2*alpha*2.849 = -(2*alpha*2.849) by ring, Real.exp_neg]
    have h := one_div_lt_one_div_of_lt (by norm_num : (0:ℝ) < 500) hexp
    rw [one_div] at h
    linarith
  · apply sub_le_sub_left
    apply Real.exp_le_exp.mpr
    have hfreq : 1 ≤ oddFreq i := by unfold oddFreq; linarith [Nat.cast_nonneg (α := ℝ) i.val]
    have hprod : 2.849 ≤ oddFreq i * ((nodeCount j:ℝ)*eta j) :=
      (show 2.849 ≤ (nodeCount j:ℝ)*eta j by linarith).trans
        (le_mul_of_one_le_left (by positivity) hfreq)
    linarith only [mul_le_mul_of_nonneg_left hprod alpha_pos.le]

theorem factorial_bound (k : ℕ) : 6^k ≤ (2*k+1).factorial := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ, show 2*(k+1)+1 = (2*k+1)+1+1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    calc
      _ ≤ (2*k+1).factorial * 6 := Nat.mul_le_mul_right 6 ih
      _ ≤ _ := by
        have h := Nat.mul_le_mul (show 3 ≤ 2*k+1+1+1 by omega) (show 2 ≤ 2*k+1+1 by omega)
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using Nat.mul_le_mul_right (2*k+1).factorial h

theorem small_sinh_series (t : ℝ) (ht : 0 < t) (hsmall : t^2 < 6) :
    (∀ k : ℕ, t^(2*k) / ((2*k+1).factorial:ℝ) ≤ (t^2/6)^k) ∧
    HasSum (fun k : ℕ => (t^2/6)^k) (1/(1-t^2/6)) ∧
    Real.sinh t / t ≤ (∑' k : ℕ, (t^2/6)^k) ∧ 1/t-t/6 ≤ 1/Real.sinh t := by
  have hterm (k : ℕ) : t^(2*k) / ((2*k+1).factorial:ℝ) ≤ (t^2/6)^k := by
    rw [div_pow, ← pow_mul]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by exact_mod_cast factorial_bound k)
  have hg : HasSum (fun k : ℕ => (t^2/6)^k) (1/(1-t^2/6)) := by
    simpa only [one_div] using hasSum_geometric_of_lt_one (by positivity : 0 ≤ t^2/6) (by linarith)
  have hs : HasSum (fun k : ℕ => t^(2*k) / ((2*k+1).factorial:ℝ)) (Real.sinh t / t) := by
    convert (Real.hasSum_sinh t).div_const t using 1
    funext k
    rw [pow_succ]
    field_simp
  have hle := hs.tsum_eq ▸ hs.summable.tsum_le_tsum hterm hg.summable
  refine ⟨hterm, hg, hle, ?_⟩
  rw [hg.tsum_eq, div_le_div_iff₀ ht (by linarith : 0 < 1-t^2/6)] at hle
  apply (le_div_iff₀ (Real.sinh_pos_iff.mpr ht)).mpr
  apply (le_of_mul_le_mul_left (a := t) _ ht)
  calc
    _ = Real.sinh t * (1-t^2/6) := by field_simp
    _ ≤ _ := by linarith

theorem large_sinh_sign (t : ℝ) (ht : 0 < t) (hlarge : 6 ≤ t^2) :
    1/t-t/6 ≤ 0 ∧ 0 < 1/Real.sinh t := by
  exact ⟨sub_nonpos.mpr ((div_le_iff₀ ht).mpr (by nlinarith)), one_div_pos.mpr (Real.sinh_pos_iff.mpr ht)⟩

end Turan.UpperTailNodes
