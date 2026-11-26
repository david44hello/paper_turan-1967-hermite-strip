module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TailStripCore
public import Turan.TailLines

@[expose] public section

namespace Turan

theorem lemma_sixteen (n m : ℕ) (hm : 450 ≤ m) (hhalf : m ≤ 2*n) (hnm : n < m)
    (a b : ℂ) (hs : emptyStrip (normalizedFamily n m a b) (87/100)) (j : ℕ) (hj : j=n ∨ j=m) :
    ‖modeQuotient n m j a b (-1/2)‖ ≤ 25000*(m:ℝ)^2/((j:ℝ)*(m-n:ℝ))*nodeProduct j := by
  exact lemma_sixteen_of_line_bound n m hm hhalf hnm a b hs j hj
    (lemma_fifteen n m hm hhalf hnm a b hs j hj)

end Turan
