module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs

@[expose] public section

noncomputable section
namespace Turan.Small56

def Node (G D : ℤ) (g d : ℝ) : Prop :=
  |g - (G:ℝ)/1000000| ≤ 2/1000000 ∧ |d - (D:ℝ)/1000000| ≤ 2/1000000 ∧
  ∀ a b : ℂ, (family 5 6 a b).eval ((g:ℂ)-1/2) * d =
    (family 5 6 a b).eval ((d:ℂ)-1/2) * g
structure Entry where
  G : ℤ
  D : ℤ
  g : ℝ
  d : ℝ
  cert : Node G D g d
  Gsize : 2 < |(G:ℝ)|
  Dsize : 2 < |(D:ℝ)|

end Turan.Small56
