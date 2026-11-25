-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

noncomputable section
open scoped RealInnerProductSpace
namespace Turan

/-- Project the fifth coordinate vector off the constant vector and
the imaginary-part vector. The sum Σ* runs over just the four upper entries. -/
theorem quintic_fifth_orthogonal_projection (z : Fin 5 → ℂ)
    (hz : ∑ i, z i = 0) (hz2 : ∑ i, (z i) ^ 2 = 10)
    (hupper : ∀ i : Fin 4, 0 < (z i.castSucc).im) :
    let x : EuclideanSpace ℝ (Fin 5) := WithLp.toLp 2 (fun i => (z i).re)
    let y : EuclideanSpace ℝ (Fin 5) := WithLp.toLp 2 (fun i => (z i).im)
    let ones : EuclideanSpace ℝ (Fin 5) := WithLp.toLp 2 (fun _ => (1 : ℝ))
    let e₅ := EuclideanSpace.single (4 : Fin 5) (1 : ℝ)
    let p := (Submodule.span ℝ {ones, y})ᗮ.starProjection e₅
    let σ := ∑ i : Fin 4, (z i.castSucc).im ^ 2
    let t := (z 4).im
    0 < ‖y‖ ^ 2 ∧ (z 4).re = ⟪x, p⟫ ∧ ‖p‖ ^ 2 = 4 / 5 - t ^ 2 / ‖y‖ ^ 2 ∧
      (z 4).re ^ 2 ≤ ‖x‖ ^ 2 * ‖p‖ ^ 2 ∧
      ‖x‖ ^ 2 * ‖p‖ ^ 2 = 10 * (4 / 5 - t ^ 2 / ‖y‖ ^ 2) + (4 * σ - t ^ 2) / 5 ∧
      10 * (4 / 5 - t ^ 2 / ‖y‖ ^ 2) + (4 * σ - t ^ 2) / 5 ≤ 3 + (3 / 5) * σ := by
  sorry

/-- Lower bounds for the cleared difference, with the signed cross term. -/
theorem quintic_difference_sqrt_chain (σ x₅ X s : ℝ)
    (hproj : x₅ ^ 2 ≤ 3 + (3 / 5) * σ) (hX : |X| < 1 / 2)
    (hσ : 4 * (87 / 100 : ℝ) ^ 2 ≤ σ) (hs₀ : 1 / 2 < s) (hs₁ : s < 511 / 1000) :
    let D := 10 + 2 * σ - 2 * x₅ ^ 2 + 4 * X * x₅ + 3 * X ^ 2 - 3 * s ^ 2
    let B := 4 + (4 / 5) * σ - 2 * Real.sqrt (3 + (3 / 5) * σ) - 3 * s ^ 2
    let C := 1 / 2 + σ / 2 - 3 * s ^ 2
    B ≤ D ∧ C ≤ B ∧ 0 < C := by
  sorry

/-- The half-length domain includes the comparison endpoint 0.511. -/
theorem quintic_rectangle_quadratic_monotonicity :
    let g := fun s y : ℝ => s ^ 2 + (56 / 45) * s * y - y ^ 2
    (∀ y : ℝ, 87 / 100 ≤ y → StrictMonoOn (fun s => g s y) (Set.Icc (1 / 2) (511 / 1000))) ∧
      ∀ s ∈ Set.Icc (1 / 2) (511 / 1000), StrictAntiOn (g s) (Set.Ici (87 / 100)) := by
  sorry

/-- Strict real margin and the division step for vertical separation. -/
theorem quintic_discriminant_sqrt_separation (z : Fin 5 → ℂ)
    (hz : ∑ i, z i = 0) (hz2 : ∑ i, (z i) ^ 2 = 10)
    (hrect : ∀ i : Fin 5, i < 3 →
      |(z i).re| < 4 / 5 ∧ 87 / 100 ≤ (z i).im ∧ (z i).im < 1) :
    let w := z 3 - z 4
    let Δ := w ^ 2
    52 / 5 < Δ.re ∧ Δ.re ≤ w.re ^ 2 ∧ Real.sqrt 10 < |w.re| ∧
      |w.im| = |Δ.im| / (2 * |w.re|) ∧
      |Δ.im| / (2 * |w.re|) < 24 / (2 * Real.sqrt 10) ∧ 24 / (2 * Real.sqrt 10) < 4 := by
  sorry

/-- Sum both second moments over all five indexed roots. -/
theorem quintic_all_five_moment_bounds (z : Fin 5 → ℂ)
    (hz : ∑ i, z i = 0) (hz2 : ∑ i, (z i) ^ 2 = 10)
    (hh : ∀ i, 87 / 100 ≤ |(z i).im|)
    (hupper : ∀ i : Fin 5, i < 3 → 0 < (z i).im ∧ (z i).im < 1)
    (hlower : (z 3).im < 0 ∧ (z 4).im < 0) :
    let I := ∑ i, (z i).im ^ 2
    let R := ∑ i, (z i).re ^ 2
    let B := 3 + (213 / 100) * (|(z 3).im| + |(z 4).im|)
    I < B ∧ B < 939 / 100 ∧ R = 10 + I ∧ R < 20 := by
  sorry

end Turan
