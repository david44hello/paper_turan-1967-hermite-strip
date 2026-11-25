-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Small34Cubic
import Turan.Small34Counting
import Turan.Small34AngleBound

namespace Turan

/-- Every member of the (3,4) family has a zero strictly inside the strip
of half-width 5/7. -/
theorem lemma_twenty (a b : ℂ) :
    ∃ z : ℂ, (family 3 4 a b).eval z = 0 ∧ |z.im| < 5/7 := by
  by_cases hb : b = 0
  · subst b
    exact small34_cubic a
  apply small34_quartic_bound a b hb
  intro l₁ r₁ l₂ r₂ l₃ r₃ hl₁ hr₁ hl₂ hr₂ hl₃ hr₃ z hz
  apply small34_weighted_bound <;> assumption

#print axioms lemma_twenty

end Turan
