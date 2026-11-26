module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs

@[expose] public section
noncomputable section
namespace Turan

def nodeMode (j : ℕ) (w : ℂ) : ℂ := (hermite j).eval (w-1/2)/w
def divided (f : ℂ → ℂ) (x y : ℂ) : ℂ := (f x-f y)/(x-y)

end Turan
