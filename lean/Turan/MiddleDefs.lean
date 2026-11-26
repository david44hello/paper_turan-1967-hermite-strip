module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.RatioDefs
public import Turan.WindingDefs

@[expose] public section

namespace Turan

/-- The four classes of exact certificates for the finite range. The partition
check covers the index pairs; the class verifiers supply their coefficient
inequalities. None of the four alternatives asserts the existence of a zero. -/
def MiddleChecks : Prop :=
  ∀ n m : ℕ, 2 ≤ n → n < m → 7 ≤ m → m ≤ 449 →
    CircleCertificate n m ∨ RatioCertificate n m ∨
      TransferCertificate n m ∨ WindingCertificate n m

end Turan
