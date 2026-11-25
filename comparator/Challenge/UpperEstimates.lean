-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Challenge.UpperSourceDefs
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

noncomputable section
open Polynomial Metric
namespace Turan.UpperEstimates

theorem shifted_operators_commute (p : Polynomial ℂ) (j k : ℂ) :
    EStar (EStar p + C k*p) + C j*(EStar p+C k*p) =
    EStar (EStar p + C j*p) + C k*(EStar p+C j*p) := by sorry

/-- The existing system uses the variable t = Ω(z-z₀), so its ordinary derivative is D. -/
def diskNorm (p : Polynomial ℂ) (r : ℝ) : ℝ :=
  sSup ((fun t : ℂ => ‖p.eval t‖) '' closedBall 0 r)

theorem radial_state (S : TailGrowthSystem) (t : ℂ) (ht : ‖t‖ ≤ 7) :
    ‖S.state t‖ ≤ Real.exp (1.75*‖t‖)*‖S.state 0‖ := by sorry

theorem half_radius_filter (S : TailGrowthSystem) (i : Fin 4) (r : ℝ)
    (hr : 1/2 ≤ r) (hr' : r ≤ 7) :
    let p := S.P i
    let B := diskNorm p r
    let C₁ : ℝ := 8+2*0.56+1
    diskNorm p.derivative (r-1/2) ≤ 2*B ∧
    diskNorm p.derivative.derivative (r-1/2) ≤ 8*B ∧
    diskNorm (S.P (i.val+1)) (r-1/2) ≤ C₁*B ∧
    (0 < B → C₁*B < 11*B) := by sorry

theorem state_center_sharp (S : TailGrowthSystem) (h : S.P 0 ≠ 0) :
    let B := diskNorm (S.P 0) 2
    (∀ i : Fin 4, let R := 2-(i.val:ℝ)/2
      diskNorm (S.P i) R ≤ 11^i.val*B ∧
      ‖(S.P i).derivative.eval 0‖ ≤ 11^i.val*B/R) ∧
    (2*11^3/1.75 : ℝ) = 10648/7 ∧
    ‖S.state 0‖ ≤ (10648/7)*B ∧ (10648/7)*B < 1600*B := by sorry

def upsilon (S : TailGrowthSystem) (t : ℂ) : ℝ :=
  Real.log ((Real.exp 12.25 * ‖S.state 0‖) / ‖(S.P 0).eval t‖)

theorem harmonic_majorant (S : TailGrowthSystem)
    (hf : ∀ t : ℂ, ‖t‖ ≤ 7 → (S.P 0).eval t ≠ 0) :
    0 < Real.exp 12.25 * ‖S.state 0‖ ∧
    InnerProductSpace.HarmonicOnNhd (upsilon S) (closedBall 0 7) ∧
    ∀ t : ℂ, ‖t‖ ≤ 7 → 0 ≤ upsilon S t := by sorry

theorem centered_comparison (S : TailGrowthSystem)
    (hf : ∀ t : ℂ, ‖t‖ ≤ 7 → (S.P 0).eval t ≠ 0)
    (t₁ : ℂ) (ht : ‖t₁‖ ≤ 2) (hmax : ‖(S.P 0).eval t₁‖ = diskNorm (S.P 0) 2) :
    upsilon S t₁ < 12.25 + Real.log 1600 ∧
    upsilon S 0 ≤ (9/5)*upsilon S t₁ ∧ (9/5)*upsilon S t₁ < 35.34 := by sorry

def affineZero (n m : ℕ) : ℝ := -1/(2*(1-1/(n:ℝ))*(1-1/(m:ℝ)))

theorem affine_factorization (n m j j' : ℕ) (hm : 450 ≤ m) (hh : m ≤ 2*n) (hnm : n < m)
    (hj : (j=n ∧ j'=m) ∨ (j=m ∧ j'=n)) (z : ℂ) :
    let x := affineZero n m
    let P := 1+2*(1-1/(n:ℂ))*(1-1/(m:ℂ))*z
    let P' := 1+2*(1-1/(j':ℂ))*z
    |x| ≤ 1/(1-1/(m:ℝ)) ∧ 1/(1-1/(m:ℝ)) ≤ 450/449 ∧
    (P = 0 ↔ z = (x:ℂ)) ∧ P = 2*(1-1/(j':ℂ))*(1-1/(j:ℂ))*(z-x) ∧
    P'-P = 2*(1-1/(j':ℂ))*z/j ∧
    (z ≠ (x:ℂ) → projectedRatio n m j' z - 1 = z/(((j:ℂ)-1)*(z-x))) := by sorry

theorem projection_strict_lines (n m j j' : ℕ) (hm : 450 ≤ m) (hh : m ≤ 2*n) (hnm : n < m)
    (hj : (j=n ∧ j'=m) ∨ (j=m ∧ j'=n)) (z : ℂ) (hz : |z.im| = 7/11) :
    let x := affineZero n m
    let Q := projectedRatio n m j' z
    7/11 ≤ ‖z-(x:ℂ)‖ ∧ ‖z/(z-x)‖ ≤ 1+|x|/(7/11) ∧
    1+|x|/(7/11) ≤ 1+(450/449)*(11/7) ∧ (1+(450/449)*(11/7):ℝ) < 2.575 ∧
    ‖Q-1‖ < 5/(j:ℝ) ∧ ‖Q‖ < 1+5/(j:ℝ) ∧ 1+5/(j:ℝ) ≤ 46/45 := by sorry

theorem line_operator_quotients (m : ℕ) (hm : 450 ≤ m) (z : ℂ) (hz : |z.im| = 7/11)
    (p : Polynomial ℂ) (hp : p.eval z ≠ 0)
    (hd : ∀ k : ℕ, 1 ≤ k → k ≤ 4 →
      ‖(derivative^[k] p).eval z / p.eval z‖ ≤ (11*omega m z)^k) :
    let W := omega m z
    let C₂ := (11:ℝ)^4/4 + 11^3*0.272 + 11^2*(0.272^2+1/900) + 11*0.272/900
    ‖z‖/W ≤ 1/4+7/330 ∧ (1/4+7/330:ℝ) < 0.272 ∧
    ‖(EStar p).eval z / p.eval z‖ ≤ (11*W)^2/2+11*‖z‖*W ∧
    (11*W)^2/2+11*‖z‖*W < (60.5+11*0.272)*W^2 ∧ (60.5+11*0.272)*W^2 < 64*W^2 ∧
    ‖(EStar (EStar p)).eval z / p.eval z‖ ≤ C₂*W^4 ∧ C₂*W^4 < 4035*W^4 := by sorry

/-- The paper normalizes the existing affine weight by sqrt(2m) before taking its fourth power. -/
def stripPi (m : ℕ) (z : ℂ) : ℂ :=
  (TailStrip.weightBase m z / (Real.sqrt (2*(m:ℝ)):ℂ))^4

theorem strip_weight_zero (m : ℕ) (hm : 450 ≤ m) (z : ℂ) :
    let s := Real.sqrt (2*(m:ℝ))
    stripPi m z = (1 - 4*Complex.I*z/(s:ℂ))^4 ∧
    (stripPi m z = 0 ↔ z = -Complex.I*(s:ℂ)/4) ∧
    (-Complex.I*(s:ℂ)/4).im ≤ -7.5 := by sorry

theorem strip_weight_lower (m : ℕ) (hm : 450 ≤ m) (z : ℂ) (hz : |z.im| ≤ 7/11) :
    let s := Real.sqrt (2*(m:ℝ))
    let W := omega m z
    let γ := 4*(7/11)/s
    let v := 1 - 4*Complex.I*z/(s:ℂ)
    γ ≤ 14/165 ∧ ‖v‖^2 = (1+4*z.im/s)^2 + 16*z.re^2/(2*(m:ℝ)) ∧
    (1-γ)^2*W^2/(2*(m:ℝ)) ≤ ‖v‖^2 ∧
    (151/165)^4 * W^4/(4*(m:ℝ)^2) ≤ ‖stripPi m z‖ := by sorry

end Turan.UpperEstimates
