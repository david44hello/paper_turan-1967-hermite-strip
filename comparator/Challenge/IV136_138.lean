-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs

noncomputable section
namespace Turan

/-- The two quadratic factors are indexed by their shifted squares u and v. -/
theorem quartic_shifted_squares_real (u v : ℂ) (huv : u * v = -1 / 2)
    (hu : u.im = 0) :
    v.im = 0 ∧ u.re * v.re < 0 ∧
    (1 / 2 < (u + 1 / 2).re ∨ 1 / 2 < (v + 1 / 2).re) ∧
    ∃ t : ℝ, (t : ℂ) ^ 2 = u + 1 / 2 ∨ (t : ℂ) ^ 2 = v + 1 / 2 := sorry

/-- Both shifted squares use the same choice of conjugation. -/
theorem quartic_shifted_squares_polar (u v : ℂ) (huv : u * v = -1 / 2)
    (hu : u.im ≠ 0) :
    ‖u‖ * ‖v‖ = 1 / 2 ∧ ∃ φ : ℝ, 0 < φ ∧ φ < Real.pi ∧
      let U := (‖u‖ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)
      let V := (‖v‖ : ℂ) * Complex.exp (((Real.pi - φ : ℝ) : ℂ) * Complex.I)
      (u = U ∧ v = V) ∨ (star u = U ∧ star v = V) := sorry

/-- The positive radial threshold in Lemma 19(ii), for y > 0 and 0 < θ < π. -/
def quarticRadialThreshold (y θ : ℝ) : ℝ :=
  2 * y * (y * Real.cos θ + Real.sqrt (y ^ 2 + (1 / 2) * Real.sin θ ^ 2)) /
    Real.sin θ ^ 2

/-- Apply at either angle to a square root of the corresponding X. -/
theorem quartic_shifted_square_radial_bound (z : ℂ) (y ρ θ : ℝ)
    (hy : 0 < y) (hz : y ≤ |z.im|) (hρ : 0 ≤ ρ) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (hpolar : z ^ 2 - 1 / 2 = (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) :
    0 ≤ ρ ^ 2 * Real.sin θ ^ 2 - 4 * y ^ 2 * ρ * Real.cos θ -
        4 * y ^ 2 * (y ^ 2 + 1 / 2) ∧
    0 < quarticRadialThreshold y θ ∧ quarticRadialThreshold y θ ≤ ρ := sorry

/-- The least absolute imaginary part among zeros of the homogeneous pencil. -/
theorem quartic_homogeneous_height_sq_bound (a b : ℂ) (hab : a ≠ 0 ∨ b ≠ 0)
    (y : ℝ) (hy : IsLeast {r : ℝ | ∃ z : ℂ,
      a * (hermite 2).eval z + b * (hermite 4).eval z = 0 ∧ |z.im| = r} y) :
    8 * y ^ 4 + 4 * y ^ 2 - 1 ≤ 0 ∧ y ^ 2 ≤ (Real.sqrt 3 - 1) / 4 := sorry

end Turan
