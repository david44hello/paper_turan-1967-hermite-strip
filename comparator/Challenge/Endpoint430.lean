-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Challenge.LowerTailDetails
namespace Turan.LowerTailSteps
theorem rounded_logTail_at_450 :
    |Real.log 2200000 - 14.6040| < 0.00005 ∧
    |5*Real.log 450 - 30.5462| < 0.00005 ∧
    |logTail 450 - (-12.6998)| < 0.00005 ∧
    deriv logTail 450 = -289/1800 := by sorry

end Turan.LowerTailSteps
