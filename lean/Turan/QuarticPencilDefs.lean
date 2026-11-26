module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.DeltaDefs

@[expose] public section

noncomputable section
open Polynomial
namespace Turan

def contactPencilPoly (d : ℝ) : Polynomial ℂ :=
  (2*X+C (d:ℂ))^2*(4*X^2+4*X+2) - (4*X^4-4*X^2+3)

theorem contactPencilPoly_eval (d : ℝ) (z : ℂ) :
    (contactPencilPoly d).eval z =
      (2*z+(d:ℂ))^2*(4*z^2+4*z+2) - (4*z^4-4*z^2+3) := by
  simp [contactPencilPoly, eval_add, eval_sub, eval_mul, eval_pow]

end Turan
