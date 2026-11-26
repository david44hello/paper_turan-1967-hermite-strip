module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Cubic
public import Turan.Decimal
public import Turan.LowerTail
public import Turan.Middle
public import Turan.Projective
public import Turan.QuarticSharp
public import Turan.Small34
public import Turan.Small45
public import Turan.Small56
public import Turan.Quintic

@[expose] public section

noncomputable section
open scoped ComplexConjugate
namespace Turan

private theorem small_strict (E10 : SexticChartCheck) (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m)
    (hm : m ≤ 6) (h23 : (n,m) ≠ (2,3)) (h35 : (n,m) ≠ (3,5)) (a b : ℂ) :
    ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| < 87/100 := by
  have cases : (n=2 ∧ m=4) ∨ (n=3 ∧ m=4) ∨ (n=2 ∧ m=5) ∨ (n=4 ∧ m=5) ∨
      ((n=2 ∨ n=3 ∨ n=4) ∧ m=6) ∨ (n=5 ∧ m=6) := by
    have h23' : ¬(n=2 ∧ m=3) := fun h => h23 (Prod.ext h.1 h.2)
    have h35' : ¬(n=3 ∧ m=5) := fun h => h35 (Prod.ext h.1 h.2)
    omega
  rcases cases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨h,rfl⟩ | ⟨rfl,rfl⟩
  · obtain ⟨w,hw,_⟩ := quartic_upper_root
    obtain ⟨bounds, hroot, _⟩ := lemma_nineteen w hw
    obtain ⟨z,hz,hy⟩ := hroot a b
    exact ⟨z,hz,by linarith [bounds.2.1]⟩
  · obtain ⟨z,hz,hy⟩ := lemma_twenty a b
    exact ⟨z,hz,by linarith⟩
  · exact quintic_all_coefficients a b
  · obtain ⟨z,hz,hy⟩ := lemma_twenty_one a b
    exact ⟨z,hz,by linarith⟩
  · obtain ⟨z,hz,hy⟩ := sextic_chart_gap E10 n h a b
    exact ⟨z,hz,by linarith⟩
  · obtain ⟨z,hz,hy⟩ := lemma_twenty_two a b
    exact ⟨z,hz,by linarith⟩

theorem proposition_two_given (G1 : TrinomialDiskCheck) (middle : MiddleChecks)
    (F1 : QuinticChartCheck) (E10 : SexticChartCheck)
    (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m) (hne : (n,m) ≠ (2,3)) (a b : ℂ) :
    (∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| < 9/10) ∧
    ((n,m) ≠ (3,5) → ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| < 87/100) := by
  by_cases h35 : (n,m) = (3,5)
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj h35
    obtain ⟨z,hz,hy⟩ := quintic_chart_gap F1 a b
    exact ⟨⟨z,hz,by linarith⟩, fun h => (h rfl).elim⟩
  have strict : ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| < 87/100 := by
    by_cases large : 450 ≤ m
    · exact lemma_eight_given G1 n m hn large hnm a b
    by_cases mid : 7 ≤ m
    · exact middle_gap middle n m hn hnm mid (by omega) a b
    exact small_strict E10 n m hn hnm (by omega) hne h35 a b
  obtain ⟨z,hz,hy⟩ := strict
  exact ⟨⟨z,hz,by linarith⟩, fun _ => ⟨z,hz,hy⟩⟩

theorem theorem_one_closed_given (G1 : TrinomialDiskCheck) (middle : MiddleChecks)
    (F1 : QuinticChartCheck) (E10 : SexticChartCheck)
    (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m) (a b : ℂ) :
    ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| ≤ h := by
  by_cases h23 : (n,m) = (2,3)
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj h23
    exact cubic_closed_strip a b
  obtain ⟨z,hz,hy⟩ := (proposition_two_given G1 middle F1 E10 n m hn hnm h23 a b).1
  exact ⟨z,hz,by linarith [height_decimal.1]⟩

theorem theorem_one_sharp (t : ℝ) (ht : t < h) :
    ∃ n m : ℕ, 2 ≤ n ∧ n < m ∧ ∃ a b : ℂ,
      ∀ z : ℂ, (family n m a b).eval z = 0 → t < |z.im| :=
  ⟨2,3,by decide,by decide,cubic_sharp t ht⟩

theorem theorem_one_extremizers_given (G1 : TrinomialDiskCheck) (middle : MiddleChecks)
    (F1 : QuinticChartCheck) (E10 : SexticChartCheck)
    (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m) (a b : ℂ) :
    (∀ z : ℂ, (family n m a b).eval z = 0 → h ≤ |z.im|) ↔
    n=2 ∧ m=3 ∧ ((a=extremalA ∧ b=extremalB) ∨
      (a=conj extremalA ∧ b=conj extremalB)) := by
  constructor
  · intro hfree
    by_cases h23 : (n,m) = (2,3)
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj h23
      exact ⟨rfl,rfl,(cubic_open_strip a b).mp hfree⟩
    obtain ⟨z,hz,hy⟩ := (proposition_two_given G1 middle F1 E10 n m hn hnm h23 a b).1
    exfalso
    linarith [hfree z hz, height_decimal.1]
  · rintro ⟨rfl,rfl,hcoeff⟩
    exact (cubic_open_strip a b).mpr hcoeff

end Turan
