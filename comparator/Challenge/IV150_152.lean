module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.RouteDefs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

@[expose] public section

noncomputable section
open Polynomial Real Set

namespace Turan

/-- The first variable is the squared displacement from the midpoint.
The second comparison concerns the value at the midpoint, as a function of height. -/
theorem small34_cot_monotonicity {s : ℝ} (hs : 0 < s) :
    (∀ h : ℝ, 0 < h → StrictMono (fun u : ℝ => (u + h^2 - s^2) / (2*h*s))) ∧
    StrictMonoOn (fun h : ℝ => (h^2 - s^2) / (2*h*s)) (Ioi 0) := sorry

/-- The sharp envelope at minimum height, on either side of the real axis. -/
theorem small34_cot_envelope {l r h : ℝ} (hlr : l < r) (hh : 0 < h)
    (z : ℂ) (hz : h ≤ |z.im|) :
    let s := (r-l)/2
    (h^2 - s^2) / (2*h*s) ≤ Real.cot |intervalAngle l r z| ∧
    (h^2 - s^2) / (2*h*s) = Real.cot (2 * arctan (s/h)) := sorry

/-- The three displayed leading coefficients after division by 16b. -/
theorem small34_monic_expansion (a b : ℂ) (hb : b ≠ 0) :
    let p := C (16*b)⁻¹ * family 3 4 a b
    p = X^4 + C (a/(2*b)) * X^3 - C 3 * X^2
      + C ((2-12*a)/(16*b)) * X + C ((1+12*b)/(16*b)) := sorry

/-- A real lift exists with the principal initial value.
Every continuous lift has the same real increment, counting roots with multiplicity. -/
theorem small34_continuous_argument_change (a b : ℂ) (hb : b ≠ 0)
    {l r : ℝ} (hlr : l ≤ r)
    (hroots : ∀ w ∈ (family 3 4 a b).roots, w.im ≠ 0) :
    let p := family 3 4 a b
    let isLift := fun θ : ℝ → ℝ =>
      ContinuousOn θ (Icc l r) ∧
      ∀ t ∈ Icc l r, (θ t : Real.Angle) = ((p.eval (t : ℂ)).arg : Real.Angle)
    (∃ θ, isLift θ ∧ θ l = (p.eval (l : ℂ)).arg) ∧
    ∀ θ, isLift θ → θ r - θ l = (p.roots.map (intervalAngle l r)).sum := sorry

end Turan
