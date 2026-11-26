module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Challenge.UpperSourceDefs
public import Challenge.UpperStripMapDef
public import Challenge.UpperStripWeightDefs

@[expose] public section

noncomputable section
open Set
namespace Turan.UpperTailStrip

/-- Pointwise analyticity throughout the whole printed strip at every
regular point. Under emptyStrip the denominator condition holds at every point there. -/
theorem quotient_analytic (n m j : ℕ) (a b z : ℂ) (hz : |z.im| < 87/100)
    (hF : normalizedFamily n m a b z ≠ 0) :
    AnalyticAt ℂ (modeQuotient n m j a b) z := by sorry

def affineDen (n m : ℕ) (z : ℂ) : ℂ :=
  1+2*(1-1/(n:ℂ))*(1-1/(m:ℂ))*z

def affinePole (n m : ℕ) : ℝ := -1/(2*(1-1/(n:ℝ))*(1-1/(m:ℝ)))

/-- Identification of the pole also gives nonvanishing at every nonreal point. -/
theorem affine_zero (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m) (z : ℂ) :
    (affineDen n m z = 0 ↔ z = (affinePole n m : ℂ)) ∧
    (z.im ≠ 0 → affineDen n m z ≠ 0) := by sorry

/-- Identification of the exact quotient and the strict line bound for both modes. -/
theorem named_ratio_line (n m j j' : ℕ) (hm : 450 ≤ m) (hh : m ≤ 2*n) (hnm : n < m)
    (hj : (j=n ∧ j'=m) ∨ (j=m ∧ j'=n)) (z : ℂ) (hz : |z.im| = TailStrip.height) :
    projectedRatio n m j' z - 1 = z / (((j:ℂ)-1)*(z-(affinePole n m : ℂ))) ∧
    ‖projectedRatio n m j' z - 1‖ < 2.59/(j:ℝ) ∧
    ‖projectedRatio n m j' z - 1‖ < 5/(j:ℝ) ∧
    ‖projectedRatio n m j' z‖ < 1+5/(j:ℝ) ∧ 1+5/(j:ℝ) ≤ 46/45 := by sorry

/-- The factor depends on m even before the uniform bound by 151/165. -/
theorem variable_weight_lower (m : ℕ) (hm : 450 ≤ m) (z : ℂ) (hz : z ∈ TailStrip.strip) :
    let A := Real.sqrt (2*(m:ℝ))
    stripWeight m z = (TailStrip.weightBase m z / (A : ℂ))^4 ∧ stripWeight m z ≠ 0 ∧
    (1-4*TailStrip.height/A)^4*(omega m z)^4/(4*(m:ℝ)^2) ≤ ‖stripWeight m z‖ := by sorry

/-- Uniform over the closed strip at both ends, with and without the finite
product of kernel factors. No zero-free-strip assumption is needed for this limit. -/
theorem weighted_decay (n m j : ℕ) (hm : 450 ≤ m) (hh : m ≤ 2*n) (hnm : n < m)
    (hj : j=n ∨ j=m) (a b : ℂ) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, 0 < X ∧ ∀ z ∈ TailStrip.strip, X ≤ |z.re| →
      ‖modeQuotient n m j a b z / stripWeight m z‖ < ε ∧
      ‖modeQuotient n m j a b z /
        (stripWeight m z * ∏ s ∈ selectedRoots j, TailStrip.factor s.re z)‖ < ε := by sorry

/-- The image equality includes surjectivity onto every point of the open disk. -/
theorem strip_tanh_image (s : ℝ) :
    stripTanh s '' {z : ℂ | |z.im| < TailStrip.height} = Metric.ball (0:ℂ) 1 ∧
    (∀ z ∈ TailStrip.strip, TailStrip.factor s z = stripTanh s z ∧
      (stripTanh s z = 0 ↔ z = (s:ℂ))) ∧
    (∀ z : ℂ, |z.im| = TailStrip.height → ‖stripTanh s z‖ = 1) := by sorry

end Turan.UpperTailStrip
