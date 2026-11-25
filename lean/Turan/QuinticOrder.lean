-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.QuinticAngle
import Mathlib.Data.Fin.Tuple.Sort

noncomputable section
open scoped ComplexConjugate
namespace Turan

/-- Moment equations and heights survive conjugation and reordering. Choose the
sign of the total argument first, then list the roots by decreasing angle. -/
theorem quintic_order_angles (X s : ℝ) (z : Fin 5 → ℂ)
    (hh : ∀ i, 87/100 ≤ |(z i).im|) (hz : ∑ i, z i = 0)
    (hz2 : ∑ i, z i^2 = 10) (ha : Real.pi ≤ |∑ i, qAngle X s (z i)|) :
    ∃ w : Fin 5 → ℂ, (∀ i, 87/100 ≤ |(w i).im|) ∧ (∑ i, w i = 0) ∧
      (∑ i, w i^2 = 10) ∧ Antitone (fun i => qAngle X s (w i)) ∧
      Real.pi ≤ ∑ i, qAngle X s (w i) := by
  obtain ⟨r, hrh, hr, hr2, hang⟩ : ∃ r : Fin 5 → ℂ,
      (∀ i, 87/100 ≤ |(r i).im|) ∧ (∑ i, r i = 0) ∧
      (∑ i, r i^2 = 10) ∧ Real.pi ≤ ∑ i, qAngle X s (r i) := by
    rcases le_total 0 (∑ i, qAngle X s (z i)) with hp | hn
    · exact ⟨z,hh,hz,hz2, by simpa [abs_of_nonneg hp] using ha⟩
    · refine ⟨fun i => conj (z i), fun i => by simpa using hh i, ?_, ?_, ?_⟩
      · simpa using congrArg (starRingEnd ℂ) hz
      · simpa [Complex.conj_ofNat] using congrArg (starRingEnd ℂ) hz2
      · simpa [qAngle_conj,Finset.sum_neg_distrib,abs_of_nonpos hn] using ha
  let f (i : Fin 5) := -qAngle X s (r i)
  let σ := Tuple.sort f
  refine ⟨r ∘ σ, fun i => hrh (σ i), (Equiv.sum_comp σ r).trans hr,
    (Equiv.sum_comp σ (fun i => r i^2)).trans hr2, ?_, ?_⟩
  · intro i j hij
    have := Tuple.monotone_sort f hij
    exact neg_le_neg_iff.mp this
  · exact hang.trans_eq (Equiv.sum_comp σ (fun i => qAngle X s (r i))).symm

end Turan
