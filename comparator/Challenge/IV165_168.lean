-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs
import Turan.RouteDefs

noncomputable section
namespace Turan

/-- A.4, 2032–2035 and 2051–2055. The explicit shifted nodes and their Vieta data. -/
theorem quintic_shifted_node_identities (S : ℝ) :
    let X := (S - 1) / 2
    let s := Real.sqrt (1 + S ^ 2) / 2
    let Zplus := (S + Real.sqrt (S ^ 2 + 1)) / 2
    let Zminus := (S - Real.sqrt (S ^ 2 + 1)) / 2
    X + s = Zplus - 1 / 2 ∧ X - s = Zminus - 1 / 2 ∧
      Zplus + Zminus = S ∧ Zplus * Zminus = -(1 / 4) ∧ Zminus < Zplus := by
  sorry

/-- Convexity and endpoint values of the derivative of the node cubic. -/
theorem quintic_node_derivative_test :
    let f := fun S : ℝ => 2 * S ^ 3 - 5 * S ^ 2 - 4 * S + 1
    let d := fun S : ℝ => 6 * S ^ 2 - 10 * S - 4
    (∀ S, HasDerivAt f (d S) S) ∧ ConvexOn ℝ Set.univ d ∧
      d 0 = -4 ∧ d (1 / 4) = -(49 / 8) ∧
      ∀ S ∈ Set.Icc 0 (1 / 4), d S < 0 := by
  sorry

/-- Both strict comparisons for the centered cotangent quotient. -/
theorem quintic_cot_quotient_monotonicity :
    let q := fun y s : ℝ => (y ^ 2 - s ^ 2) / (2 * y * s)
    (∀ s : ℝ, 0 < s → StrictMonoOn (fun y => q y s) (Set.Ioi 0)) ∧
      ∀ y : ℝ, 0 < y → StrictAntiOn (q y) (Set.Ioi 0) := by
  sorry

/-- Count indexed roots, with multiplicity, before selecting a triple. -/
theorem quintic_initial_upper_count (X s : ℝ) (z : Fin 5 → ℂ)
    (hs₀ : 1 / 2 < s) (hs₁ : s < 511 / 1000)
    (hh : ∀ i, 87 / 100 ≤ |(z i).im|) (hz : ∑ i, z i = 0)
    (hsum : Real.pi ≤ ∑ i, intervalAngle (X - s) (X + s) (z i)) :
    let n := (Finset.univ.filter (fun i : Fin 5 => 0 < (z i).im)).card
    n = 3 ∨ n = 4 := by
  sorry

end Turan
