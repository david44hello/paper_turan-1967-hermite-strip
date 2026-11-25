-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Coverage
namespace Turan

theorem attained_height_maximum_given (G1 : TrinomialDiskCheck) (middle : MiddleChecks)
    (F1 : QuinticChartCheck) (E10 : SexticChartCheck) :
    IsGreatest {r : ℝ | ∃ (n m : ℕ), 2 ≤ n ∧ n < m ∧ ∃ a b : ℂ,
      IsLeast {t : ℝ | ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| = t} r} h := by
  constructor
  · refine ⟨2, 3, by decide, by decide, extremalA, extremalB, ?_⟩
    obtain ⟨_, _, _, hz, hheight, _⟩ := extremal_cubics
    refine ⟨⟨W-1/2, ((hz _).1).mpr rfl, hheight⟩, ?_⟩
    rintro t ⟨z, hroot, rfl⟩
    rw [((hz z).1).mp hroot, hheight]
  · rintro t ⟨n, m, hn, hnm, a, b, ht⟩
    obtain ⟨z, hz, hbound⟩ := theorem_one_closed_given G1 middle F1 E10 n m hn hnm a b
    exact (ht.2 ⟨z, hz, rfl⟩).trans hbound

end Turan
