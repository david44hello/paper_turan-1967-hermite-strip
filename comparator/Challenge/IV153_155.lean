module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Challenge.Small34SourceDefs
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

@[expose] public section

noncomputable section
open Polynomial Real Set Filter
open scoped Topology

namespace Turan

/-- Evaluation on the entire real boundary line identifies
each complex polynomial with the corresponding existing rounded product. -/
theorem small34_boundary_product_polynomials :
    ∃ P Q : Polynomial ℂ,
      P.Monic ∧ P.natDegree = 22 ∧ (∀ x : ℝ, P.eval (x : ℂ) = small34ZUpper x (5/7)) ∧
      Q.Monic ∧ Q.natDegree = 22 ∧ (∀ x : ℝ, Q.eval (x : ℂ) = small34ZLower x (5/7)) := sorry

/-- Outer, inner, outer boxes for the coefficients 5, −4, 2. -/
def small34GUpper (z : ℂ) : ℝ :=
  5 * small34Angle (-1.311446) (-0.096251) z - 4 * small34Angle (-1.553002) 1.794300 z
    + 2 * small34Angle (-0.308319) 2.074718 z

/-- Inner, outer, inner boxes for the coefficients 5, −4, 2. -/
def small34GLower (z : ℂ) : ℝ :=
  5 * small34Angle (-1.311445) (-0.096252) z - 4 * small34Angle (-1.553003) 1.794301 z
    + 2 * small34Angle (-0.308318) 2.074717 z

/-- Exact rotation on the boundary, with the printed normalization. -/
theorem small34_upper_sine_prefactor (x : ℝ) :
    let Z := small34ZUpper x (5/7)
    Z.re - 44 * Z.im = -Real.sqrt 1937 * ‖Z‖ *
      Real.sin (small34GUpper ⟨x, 5/7⟩ - arctan (1/44)) := sorry

/-- Decay is uniform over directions of escape in the upper half-plane. -/
theorem small34_angle_harmonic_decay {l r : ℝ} (hlr : l < r) :
    InnerProductSpace.HarmonicOnNhd (small34Angle l r) {z : ℂ | 0 < z.im} ∧
    ContinuousOn (small34Angle l r) {z : ℂ | 5/7 ≤ z.im} ∧
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ,
      0 < z.im → R ≤ ‖z‖ → |small34Angle l r z| < ε := sorry

/-- Both rounded angles vanish at both ends of the line.
The supremum of the shifted upper angle lies strictly between −π and zero. -/
theorem small34_boundary_extrema :
    let u := fun x : ℝ => small34GUpper ⟨x, 5/7⟩
    let v := fun x : ℝ => small34GLower ⟨x, 5/7⟩
    Tendsto (fun x => (u x, v x)) (atBot ⊔ atTop) (𝓝 (0, 0)) ∧
    sSup (range fun x => u x - arctan (1/44)) ∈ Ioo (-π) 0 ∧
    arctan (1/14) - π < sInf (range v) := sorry

/-- The same boundary extrema control the entire closed half-plane. -/
theorem small34_halfplane_boundary_bounds (z : ℂ) (hz : 5/7 ≤ z.im) :
    small34GUpper z - arctan (1/44) ≤
      sSup (range fun x : ℝ => small34GUpper ⟨x, 5/7⟩ - arctan (1/44)) ∧
    sInf (range fun x : ℝ => small34GLower ⟨x, 5/7⟩) ≤ small34GLower z := sorry

end Turan
