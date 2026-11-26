module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.MiddleDefs
public import Turan.ProjectiveDefs

@[expose] public section
open scoped ComplexConjugate
namespace Turan

theorem middle_gap (checks : MiddleChecks) (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m)
    (hm : 7 ≤ m) (hm' : m ≤ 449) (a b : ℂ) :
    ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| < 87/100 := by sorry

theorem proposition_two_given (G1 : TrinomialDiskCheck) (middle : MiddleChecks)
    (F1 : QuinticChartCheck) (E10 : SexticChartCheck)
    (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m) (hne : (n,m) ≠ (2,3)) (a b : ℂ) :
    (∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| < 9/10) ∧
    ((n,m) ≠ (3,5) → ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| < 87/100) := by sorry

theorem theorem_one_closed_given (G1 : TrinomialDiskCheck) (middle : MiddleChecks)
    (F1 : QuinticChartCheck) (E10 : SexticChartCheck)
    (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m) (a b : ℂ) :
    ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| ≤ h := by sorry

theorem theorem_one_sharp (t : ℝ) (ht : t < h) :
    ∃ n m : ℕ, 2 ≤ n ∧ n < m ∧ ∃ a b : ℂ,
      ∀ z : ℂ, (family n m a b).eval z = 0 → t < |z.im| := by sorry

theorem theorem_one_extremizers_given (G1 : TrinomialDiskCheck) (middle : MiddleChecks)
    (F1 : QuinticChartCheck) (E10 : SexticChartCheck)
    (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m) (a b : ℂ) :
    (∀ z : ℂ, (family n m a b).eval z = 0 → h ≤ |z.im|) ↔
    n=2 ∧ m=3 ∧ ((a=extremalA ∧ b=extremalB) ∨
      (a=conj extremalA ∧ b=conj extremalB)) := by sorry

end Turan
