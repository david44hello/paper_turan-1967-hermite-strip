-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.CircleCertificate
import Turan.Ratio
import Turan.Transfer
import Turan.Winding
import Turan.MiddleDefs

namespace Turan
theorem middle_gap (checks : MiddleChecks) (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m)
    (hm : 7 ≤ m) (hm' : m ≤ 449) (a b : ℂ) :
    ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| < 87/100 := by
  rcases checks n m hn hnm hm hm' with h | h | h | h
  · exact circle_certificate_gap n m hn hnm h a b
  · exact ratio_certificate_gap n m hn hnm h a b
  · exact transfer_certificate_gap n m hn hnm h a b
  · exact winding_certificate_gap n m hn hnm h a b
end Turan
