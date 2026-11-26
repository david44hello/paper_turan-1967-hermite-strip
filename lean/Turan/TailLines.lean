module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TailLinesHelper
public import Turan.TailDerivatives

@[expose] public section

namespace Turan

theorem lemma_fifteen (n m : ℕ) (hm : 450 ≤ m) (hhalf : m ≤ 2*n) (hnm : n < m)
    (a b : ℂ) (hs : emptyStrip (normalizedFamily n m a b) (87/100))
    (j : ℕ) (hj : j = n ∨ j = m) (z : ℂ) (hz : |z.im| = 7/11) :
    ‖modeQuotient n m j a b z‖ ≤ 4200 * (omega m z)^4 / ((j:ℝ)*(m-n:ℝ)) := by
  exact lemma_fifteen_of_derivative_bounds n m hm hhalf hnm a b hs
    (lemma_fourteen n m hm hhalf hnm a b hs) j hj z hz

#print axioms lemma_fifteen

end Turan
