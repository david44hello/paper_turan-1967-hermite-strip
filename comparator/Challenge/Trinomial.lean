module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TrinomialDefs

@[expose] public section
namespace Turan

theorem trinomial_small (n : ℕ) (hn : n = 2 ∨ n = 3) (a : ℂ) :
    ∃ c : ℂ, 1 + 2*c + a*psi n c = 0 ∧ |c.re| ≤ 2 ∧ |c.im| < 76/100 := by sorry

theorem trinomial_finite (check : TrinomialDiskCheck) (n : ℕ) (hn : 4 ≤ n) (hn' : n ≤ 79) (a : ℂ) :
    ∃ c : ℂ, 1 + 2*c + a*psi n c = 0 ∧ |c.re| ≤ 2 ∧ |c.im| < 76/100 := by sorry

theorem trinomial_large (n : ℕ) (hn : 80 ≤ n) (a : ℂ) :
    ∃ c : ℂ, 1 + 2*c + a*psi n c = 0 ∧ |c.re| ≤ 2 ∧ |c.im| < 76/100 := by sorry

theorem lemma_ten_given (check : TrinomialDiskCheck) (n : ℕ) (hn : 2 ≤ n) (a : ℂ) :
    ∃ c : ℂ, 1 + 2*c + a*psi n c = 0 ∧ |c.re| ≤ 2 ∧ |c.im| < 76/100 := by sorry

end Turan
