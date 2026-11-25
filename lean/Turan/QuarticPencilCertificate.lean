-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs

noncomputable section
namespace Turan.QuarticPencil

/-- The part of the height resultant independent of the real parameter.
The argument is the shifted squared height, `t = 3 * im(z)^2 - 2`. -/
def base (t : ℝ) : ℝ :=
  110592*t^6 + 1105920*t^5 + 4488192*t^4 + 9192448*t^3 + 9316032*t^2 + 3523584*t - 246880

/-- The correction to the base polynomial divided by `d²` is
`evenPart t (d²) + (d-4)² * squarePart t (d²)`. Both polynomials
have strictly positive coefficients. -/
def evenPart (t u : ℝ) : ℝ :=
  (45*u^4 + 7827*u^3 + 128840*u^2 + 1533704*u + 3620288)
    + (36*u^4 + 9492*u^3 + 261576*u^2 + 3175920*u + 10695168)*t
    + (2688*u^3 + 177600*u^2 + 2596512*u + 12000000)*t^2
    + (38080*u^2 + 1002880*u + 6679552)*t^3
    + (149760*u + 1898496)*t^4
    + 221184*t^5

def squarePart (t u : ℝ) : ℝ :=
  (135*u^3 + 3564*u^2 + 2664*u + 4792)
    + (108*u^3 + 4788*u^2 + 15096*u + 2688)*t
    + (1584*u^2 + 14016*u + 9120)*t^2
    + (3648*u + 8960)*t^3
    + 2304*t^4

theorem correction_pos {t : ℝ} (ht : 0 ≤ t) (d : ℝ) :
    0 < evenPart t (d^2) + (d-4)^2 * squarePart t (d^2) := by
  unfold evenPart squarePart
  positivity

theorem base_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : base s ≤ base t := by
  unfold base
  gcongr

end Turan.QuarticPencil
