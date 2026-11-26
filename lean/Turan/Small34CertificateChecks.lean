module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Small34CertificateData

@[expose] public section

namespace Turan.Small34Certificate

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def both (a b v : ℤ) : Bool := test upper a b v && test lower a b v

theorem checkLeft : both (-2000000) (-1) 0 = true := by decide +kernel
theorem check₁ : both (-2000000) (-1000000) 1 = true := by decide +kernel
theorem check₂ : both (-1000000) (-750000) 1 = true := by decide +kernel
theorem check₃ : both (-750000) (-500000) 1 = true := by decide +kernel
theorem check₄ : both (-500000) 0 1 = true := by decide +kernel
theorem check₅ : both 0 500000 1 = true := by decide +kernel
theorem check₆ : both 500000 750000 1 = true := by decide +kernel
theorem check₇ : both 750000 1000000 1 = true := by decide +kernel
theorem check₈ : both 1000000 2000000 1 = true := by decide +kernel
theorem checkRight : both 2000000 1 0 = true := by decide +kernel

end Turan.Small34Certificate
