-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Challenge.RecoveryDetails
import Turan.SlotDefs

noncomputable section
open Polynomial
namespace Turan.RecoveryDetails

theorem normalizedPoly_eval (n m : ℕ) (a b z : ℂ) :
    (normalizedPoly n m a b).eval z = normalizedFamily n m a b z := by sorry

theorem jetBound_of_emptyStrip (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m) (a b c : ℂ)
    (hf : emptyStrip (normalizedFamily n m a b) (87/100)) (hy : |c.im| < 76/100) :
    jetBound (normalizedPoly n m a b) c m := by sorry

end Turan.RecoveryDetails
