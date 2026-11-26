module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Coverage
public import Turan.Disk
public import Turan.Hermite

@[expose] public section

noncomputable section
open Polynomial
namespace Turan

theorem figure_one_width (G1 : TrinomialDiskCheck) (middle : MiddleChecks)
    (F1 : QuinticChartCheck) (E10 : SexticChartCheck) (C : ℝ) :
    (∀ n m : ℕ, 2 ≤ n → n < m → ∀ a b : ℂ, ∃ z : ℂ,
      (family n m a b).eval z = 0 ∧ |z.im| ≤ C) ↔ h ≤ C := by
  constructor
  · intro hc
    apply (least_half_width_given G1 middle F1 E10).2
    exact hc
  · intro hc n m hn hnm a b
    obtain ⟨z,hz,hy⟩ := theorem_one_closed_given G1 middle F1 E10 n m hn hnm a b
    exact ⟨z,hz,hy.trans hc⟩

theorem trinomial_exists_strip :
    ∃ A : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ a : ℂ,
      ∃ z : ℂ, 1+2*z+a*(hermite n).eval z = 0 ∧ |z.im| ≤ A := by
  obtain ⟨R,_,hR⟩ := proposition_three
  refine ⟨R, ?_⟩
  intro n hn a
  obtain ⟨z,hz,hy⟩ := (hR n (n+1) hn (Nat.lt_succ_self _) a 0).2
  exact ⟨z,by simpa [family,eval_add,eval_mul] using hz,hy.le⟩

theorem quadratic_trinomial_least_width :
    IsLeast {r : ℝ | ∀ a : ℂ, ∃ z : ℂ, 1+2*z+a*(hermite 2).eval z = 0 ∧ |z.im| ≤ r}
      (1/2) := by
  constructor
  · intro a
    obtain ⟨z,hz,hy⟩ := cubic_zero_b_half_strip a
    exact ⟨z,by simpa [family,eval_add,eval_mul] using hz,hy⟩
  · intro r hr
    obtain ⟨z,hz,hy⟩ := hr ((1+Complex.I)/4)
    have hfac : 1+2*z+(1+Complex.I)/4*(hermite 2).eval z =
        (1+Complex.I)*(z+1/2-Complex.I/2)^2 := by
      rw [hermite_low.1]
      norm_num [eval_sub, eval_mul, eval_pow]
      linear_combination (z + (1-Complex.I)/4) * Complex.I_sq
    rw [hfac] at hz
    have hnon : (1:ℂ)+Complex.I ≠ 0 := by intro h; simpa using congrArg Complex.re h
    have hroot : z + 1/2 = Complex.I/2 := sub_eq_zero.mp (pow_eq_zero_iff (by decide : 2 ≠ 0) |>.mp
      ((mul_eq_zero.mp hz).resolve_left hnon))
    have hi := congrArg Complex.im hroot
    norm_num [Complex.add_im, Complex.div_ofNat_im] at hi
    simpa [hi] using hy

end Turan
