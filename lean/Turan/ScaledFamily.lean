-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.CircleDefs
import Turan.TailDefs

noncomputable section
namespace Turan

def scaledFamily (n m : ℕ) (a b z : ℂ) : ℂ :=
  1 + 2*z + a*(scaledMode n).eval z + b*(scaledMode m).eval z

end Turan
