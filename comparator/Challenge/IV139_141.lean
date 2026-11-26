module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

@[expose] public section

noncomputable section
open Filter Polynomial
open scoped Topology
namespace Turan

/-- The finite (2,4) family always has a lowest zero (family_has_lowest_zero). -/
def quarticFamilyHeight (p : ℂ × ℂ) : ℝ :=
  sInf {r : ℝ | ∃ z : ℂ, (family 2 4 p.1 p.2).eval z = 0 ∧ |z.im| = r}

/-- The product norm on the coefficient pair is M = max (‖a‖) (‖b‖). -/
theorem quartic_unbounded_normalized_subsequence (p : ℕ → ℂ × ℂ)
    (hunbounded : ¬ BddAbove (Set.range (fun j => ‖p j‖))) :
    ∃ (σ : ℕ → ℕ) (q : ℂ × ℂ), StrictMono σ ∧
      Tendsto (fun k => ‖p (σ k)‖) atTop atTop ∧ ‖q‖ = 1 ∧
      Tendsto (fun k => (‖p (σ k)‖)⁻¹ • p (σ k)) atTop (𝓝 q) ∧
      let G := C q.1 * hermite 2 + C q.2 * hermite 4
      G ≠ 0 ∧ TendstoLocallyUniformly
        (fun k z => (family 2 4 (p (σ k)).1 (p (σ k)).2).eval z / (‖p (σ k)‖ : ℂ))
        (fun z => G.eval z) atTop := sorry

/-- Here p indexes the extracted subsequence, and the conclusion concerns its
original, unscaled polynomials. -/
theorem quartic_normalized_escape_low_zero (p : ℕ → ℂ × ℂ) (a b : ℂ)
    (hM : Tendsto (fun j => ‖p j‖) atTop atTop)
    (hab : a ≠ 0 ∨ b ≠ 0)
    (hconv : TendstoLocallyUniformly
      (fun j z => (family 2 4 (p j).1 (p j).2).eval z / (‖p j‖ : ℂ))
      (fun z => a * (hermite 2).eval z + b * (hermite 4).eval z) atTop) :
    ∀ᶠ j in atTop, ∃ z : ℂ, (family 2 4 (p j).1 (p j).2).eval z = 0 ∧
      |z.im| < 1 / 2 := sorry

/-- The height limit contradicts the eventual low zeros along any escape. -/
theorem quartic_coefficients_bounded_of_height_limit (p : ℕ → ℂ × ℂ) (η : ℝ)
    (hη : 1 / 2 < η) (hlim : Tendsto (fun j => quarticFamilyHeight (p j)) atTop (𝓝 η)) :
    BddAbove (Set.range (fun j => ‖p j‖)) := sorry

/-- A subsequence of the given maximizing sequence converges to a maximizer.
Each zero of that member is approached by zeros along the same coefficient subsequence. -/
theorem quartic_maximizing_subsequence (p : ℕ → ℂ × ℂ) (η : ℝ)
    (hsup : IsLUB (Set.range quarticFamilyHeight) η)
    (hlim : Tendsto (fun j => quarticFamilyHeight (p j)) atTop (𝓝 η)) :
    ∃ (σ : ℕ → ℕ) (q : ℂ × ℂ), StrictMono σ ∧
      Tendsto (fun k => p (σ k)) atTop (𝓝 q) ∧ quarticFamilyHeight q = η ∧
      ∀ z : ℂ, (family 2 4 q.1 q.2).eval z = 0 →
        ∃ w : ℕ → ℂ, (∀ k, (family 2 4 (p (σ k)).1 (p (σ k)).2).eval (w k) = 0) ∧
          Tendsto w atTop (𝓝 z) := sorry

end Turan
