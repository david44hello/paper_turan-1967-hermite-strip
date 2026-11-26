module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TailStrip
public import Turan.TailNodes
public import Turan.TailComparison
public import Turan.TailGapCore

@[expose] public section

namespace Turan

theorem large_upper_index_gap (n m : ℕ) (hm : 450 ≤ m) (hhalf : m ≤ 2*n) (hnm : n < m)
    (a b : ℂ) : ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| < 87/100 :=
  upper_index_gap_of_mode_bounds n m hm hhalf hnm a b
    (lemma_sixteen n m hm hhalf hnm) lemma_seventeen (tail_numeric_compare n m · hm hhalf hnm)

end Turan
