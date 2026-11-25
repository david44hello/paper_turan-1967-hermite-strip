-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs

noncomputable section

open scoped Topology
namespace Turan.Small45

/-- The two symmetric divided-difference formulas of A.3, in the independent
sum and product variables. At distinct nonzero arguments they are [q₄], [q₅]. -/
theorem divided_differences_zero_iff_eliminant (S p : ℂ) (hS : S ≠ -9) (hp : p ≠ 0) :
    (16 * (S^2 - p) - 32*S - 24 - 1/p = 0 ∧
      32 * (S^3 - 2*p*S) - 80 * (S^2 - p) - 80*S + 200 + 41/p = 0) ↔
    p = (2*S^3 + 36*S^2 - 87*S - 49) / (4*S + 36) ∧
      S^6 + 14*S^5 - 111*S^4 + 228*S^3 - 143*S^2 - 6*S + 41 = 0 := sorry

/-- The shifted-coordinate rational function, with its first pair counted twice. -/
def nodeQuotient (l r u v : ℝ) (w : ℂ) : ℂ :=
  (w - l)^2 * (w - u) / ((w - r)^2 * (w - v))

def modelQuotient : ℂ → ℂ := nodeQuotient (-20.10) 0 0.44 2.47

/-- Finite poles are characterized by blowup on a punctured neighbourhood. -/
theorem model_poles_and_infinity :
    (∀ w : ℂ, (Filter.Tendsto (fun z => ‖modelQuotient z‖) (𝓝[≠] w) Filter.atTop ↔
      w = 0 ∨ w = 2.47)) ∧
    (∀ w : ℂ, w ≠ 0 → w ≠ 2.47 → AnalyticAt ℂ modelQuotient w) ∧
    Filter.Tendsto modelQuotient (Filter.cocompact ℂ) (𝓝 1) := sorry

theorem model_boundary_margin :
    ∃ B ∈ Set.Ioo (1 : ℝ) 225, ∀ w : ℂ, w.im = 17/20 → ‖modelQuotient w‖ ≤ B := sorry

/-- A uniform diameter bound above the limit at infinity controls the large
semicircles and their filled half-disks. Reflection gives the same cap below. -/
theorem model_half_disk_extension (B : ℝ) (hB : 1 < B)
    (hline : ∀ w : ℂ, w.im = 17/20 → ‖modelQuotient w‖ ≤ B) :
    let c : ℂ := (17/20) * Complex.I
    (∃ R₀ > (0 : ℝ), ∀ R ≥ R₀,
      (∀ w : ℂ, 17/20 ≤ w.im → ‖w-c‖ = R → ‖modelQuotient w‖ ≤ B) ∧
      (∀ w : ℂ, 17/20 ≤ w.im → ‖w-c‖ ≤ R → ‖modelQuotient w‖ ≤ B)) ∧
    (∀ w : ℂ, modelQuotient (star w) = star (modelQuotient w)) ∧
    (∀ w : ℂ, 17/20 ≤ |w.im| → ‖modelQuotient w‖ ≤ B) := sorry

theorem node_quotient_strict_transfer (l r u v : ℝ)
    (hl : l ∈ Set.Ioo (-20.11) (-20.09)) (hr : r ∈ Set.Ioo (-1/125000) 0)
    (hu : u ∈ Set.Ioo 0.43 0.45) (hv : v ∈ Set.Ioo 2.46 2.48)
    (w : ℂ) (hw : 17/20 ≤ |w.im|) :
    ‖nodeQuotient l r u v w‖ < 225 * (86/85)^4 * (1 + 1/106250)^2 := sorry

end Turan.Small45
