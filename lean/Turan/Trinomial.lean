-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.TrinomialSmall
import Turan.TrinomialFinite
import Turan.TrinomialLarge

namespace Turan

theorem lemma_ten_given (check : TrinomialDiskCheck) (n : ℕ) (hn : 2 ≤ n) (a : ℂ) :
    ∃ c : ℂ, 1 + 2*c + a*psi n c = 0 ∧ |c.re| ≤ 2 ∧ |c.im| < 76/100 := by
  by_cases hsmall : n < 4
  · exact trinomial_small n (by omega) a
  by_cases hlarge : 80 ≤ n
  · exact trinomial_large n hlarge a
  exact trinomial_finite check n (by omega) (by omega) a

end Turan
