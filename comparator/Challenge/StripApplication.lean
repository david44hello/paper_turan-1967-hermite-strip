module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.StripDetailDefs

@[expose] public section
open Set
noncomputable section
namespace Turan.StripDetails

def selected (j : ℕ) : Finset ℝ :=
  ((hermite j).roots.toFinset.filter
    (fun s => s.im=0 ∧ -(7:ℝ)/2 ≤ s.re ∧ s.re ≤ 5/2)).image Complex.re

theorem strip_quotient_application (n m j : ℕ) (hm : 450 ≤ m) (hh : m ≤ 2*n) (hnm : n < m)
    (hj : j=n ∨ j=m) (a b : ℂ) (hs : emptyStrip (normalizedFamily n m a b) (87/100)) :
    let U := modeQuotient n m j a b
    let S := (m:ℝ)^2/((j:ℝ)*(m-n:ℝ))
    let P := fun z : ℂ => ∏ s ∈ selected j, factor s z
    ∃ V : ℂ → ℂ, (∀ z : ℂ, |z.im| < 87/100 → AnalyticAt ℂ V z) ∧
      (∀ z : ℂ, |z.im| < 87/100 → U z = V z * weight m z * P z) ∧
      (∀ z : ℂ, |z.im| = height → ‖V z‖ = ‖U z / weight m z‖) ∧
      (∀ ε > (0:ℝ), ∃ R > (0:ℝ), ∀ z : ℂ, |z.im| ≤ height → R ≤ |z.re| → ‖V z‖ < ε) ∧
      (∀ z : ℂ, |z.im| ≤ height → ‖V z‖ < 23952*S) ∧
      ‖U (-1/2)‖ ≤ 24166*S*nodeProduct j := by sorry

end Turan.StripDetails
