-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Main

noncomputable section
open scoped ComplexConjugate
namespace Turan

theorem least_half_width_given (G1 : TrinomialDiskCheck) (middle : MiddleChecks)
    (F1 : QuinticChartCheck) (E10 : SexticChartCheck) :
    IsLeast {r : ℝ | ∀ n m : ℕ, 2 ≤ n → n < m → ∀ a b : ℂ,
      ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| ≤ r} h := by
  refine ⟨theorem_one_closed_given G1 middle F1 E10, ?_⟩
  intro t hworks
  by_contra! ht
  obtain ⟨n,m,hn,hnm,a,b,hsharp⟩ := theorem_one_sharp t ht
  obtain ⟨z,hz,hy⟩ := hworks n m hn hnm a b
  exact hy.not_gt (hsharp z hz)

theorem exactly_two_polynomials_given (G1 : TrinomialDiskCheck) (middle : MiddleChecks)
    (F1 : QuinticChartCheck) (E10 : SexticChartCheck) :
    {p : Polynomial ℂ | (∃ n m : ℕ, 2 ≤ n ∧ n < m ∧ ∃ a b : ℂ, p = family n m a b) ∧
      (∀ z : ℂ, p.eval z = 0 → h ≤ |z.im|)} =
    {family 2 3 extremalA extremalB, family 2 3 (conj extremalA) (conj extremalB)} := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨n,m,hn,hnm,a,b,rfl⟩,hzero⟩
    obtain ⟨rfl,rfl,hcoeff⟩ := (theorem_one_extremizers_given G1 middle F1 E10 n m hn hnm a b).mp hzero
    rcases hcoeff with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp
  · rintro (rfl | rfl)
    · exact ⟨⟨2,3,by decide,by decide,_,_,rfl⟩,(cubic_open_strip _ _).mpr (.inl ⟨rfl,rfl⟩)⟩
    · exact ⟨⟨2,3,by decide,by decide,_,_,rfl⟩,(cubic_open_strip _ _).mpr (.inr ⟨rfl,rfl⟩)⟩

theorem middle_pair_count :
    (∑ m ∈ Finset.Icc 7 449, (m-2 : ℕ)) = 100118 := by decide +kernel

end Turan
