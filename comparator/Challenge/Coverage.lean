module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.MiddleDefs
public import Turan.ProjectiveDefs

@[expose] public section
open scoped ComplexConjugate
namespace Turan

theorem least_half_width_given (G1 : TrinomialDiskCheck) (middle : MiddleChecks)
    (F1 : QuinticChartCheck) (E10 : SexticChartCheck) :
    IsLeast {r : ℝ | ∀ n m : ℕ, 2 ≤ n → n < m → ∀ a b : ℂ,
      ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| ≤ r} h := by sorry

theorem exactly_two_polynomials_given (G1 : TrinomialDiskCheck) (middle : MiddleChecks)
    (F1 : QuinticChartCheck) (E10 : SexticChartCheck) :
    {p : Polynomial ℂ | (∃ n m : ℕ, 2 ≤ n ∧ n < m ∧ ∃ a b : ℂ, p = family n m a b) ∧
      (∀ z : ℂ, p.eval z = 0 → h ≤ |z.im|)} =
    {family 2 3 extremalA extremalB, family 2 3 (conj extremalA) (conj extremalB)} := by sorry

theorem middle_pair_count :
    (∑ m ∈ Finset.Icc 7 449, (m-2 : ℕ)) = 100118 := by sorry

end Turan
