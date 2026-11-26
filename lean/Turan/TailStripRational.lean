module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Degree
public import Turan.TailDefs
public import Turan.TailStripFactors
public import Mathlib.Analysis.Polynomial.Basic

@[expose] public section

noncomputable section
namespace Turan.TailStrip

open Complex Polynomial Filter

theorem mode_representation {n m j : ℕ} (hn : 2 ≤ n) (hnm : n < m)
    (hj : j = n ∨ j = m) (a b : ℂ) :
    ∃ P Q : Polynomial ℂ, P.degree ≤ Q.degree ∧
      (∀ z, Q.eval z = normalizedFamily n m a b z) ∧
      (∀ z, modeQuotient n m j a b z = P.eval z / Q.eval z) := by
  let scale := fun l : ℕ => (Real.sqrt (2^l * (l.factorial : ℝ)) : ℂ)
  let A := a / scale n
  let B := b / scale m
  let Q := family n m A B
  let c := if j = n then A else B
  let P := C c * hermite j
  have hQ (z : ℂ) : Q.eval z = normalizedFamily n m a b z := by
    simp [Q, family, A, B, scale, normalizedFamily, psi]
    ring
  refine ⟨P, Q, ?_, hQ, fun z => ?_⟩
  · by_cases hc : c = 0
    · simp [P, hc]
    have hdeg := family_degree n m hn hnm A B
    have hQne : Q ≠ 0 := by
      apply ne_zero_of_natDegree_gt (n := 0)
      dsimp only [Q]; rw [hdeg]; split_ifs <;> omega
    rw [degree_eq_natDegree hQne]
    apply degree_le_of_natDegree_le
    rw [show P.natDegree = j by exact (natDegree_C_mul hc).trans (hermite_degree j).1]
    change j ≤ (family n m A B).natDegree
    rw [hdeg]
    rcases hj with rfl | rfl
    · simp only [c, ite_eq_left rfl] at hc
      split_ifs <;> omega
    · have hmn := Nat.ne_of_gt hnm
      have hb : B ≠ 0 := by simpa [c, hmn] using hc
      simp [hb]
  · rw [hQ]
    rcases hj with rfl | rfl
    · simp [P, c, A, scale, modeQuotient, psi]; ring
    · simp [P, c, B, scale, modeQuotient, psi, Nat.ne_of_gt hnm]; ring

theorem mode_regular {n m j : ℕ} (hn : 2 ≤ n) (hnm : n < m)
    (hj : j = n ∨ j = m) (a b : ℂ) (hs : emptyStrip (normalizedFamily n m a b) (87/100)) :
    DifferentiableOn ℂ (modeQuotient n m j a b) strip ∧ farBound (modeQuotient n m j a b) := by
  obtain ⟨P,Q,hdeg,hQ,hmode⟩ := mode_representation hn hnm hj a b
  have hne (z : ℂ) (hz : z ∈ strip) : Q.eval z ≠ 0 := by
    rw [hQ]; apply hs; exact lt_of_le_of_lt hz (by norm_num : height < (87:ℝ)/100)
  constructor
  · rw [funext hmode]
    exact P.differentiable.differentiableOn.div Q.differentiable.differentiableOn hne
  · obtain ⟨K,hK⟩ := Asymptotics.isBigO_iff.mp (Polynomial.isBigO_cobounded_of_degree_le hdeg)
    obtain ⟨R,_,hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp hK
    refine ⟨K,R, fun z hz hstrip => ?_⟩
    rw [hmode, norm_div, div_le_iff₀ (norm_pos_iff.mpr (hne z hstrip))]
    exact hR (hz.trans (Complex.abs_re_le_norm z))

end Turan.TailStrip
