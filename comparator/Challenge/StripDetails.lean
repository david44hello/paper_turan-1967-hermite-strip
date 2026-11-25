-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.StripDetailDefs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
noncomputable section
open Set
namespace Turan.StripDetails


theorem boundary_weighted_quotient (m j n : ℕ) (hm : 450 ≤ m) (hj : 0 < j) (hnm : n < m)
    (z U : ℂ) (hy : |z.im|=height)
    (hb : ‖U‖ ≤ 4200*(omega m z)^4/((j:ℝ)*(m-n:ℝ))) :
    let S := (m:ℝ)^2/((j:ℝ)*(m-n:ℝ))
    ‖U/weight m z‖ ≤ 4*4200*(165/151:ℝ)^4*S ∧ 4*4200*(165/151:ℝ)^4*S < 23952*S := by sorry

theorem strip_factor_modulus (s : ℝ) (z : ℂ) (hy : |z.im| ≤ height) :
    let ζ := coordinate s z
    |ζ.im| ≤ Real.pi/4 ∧ 0 ≤ (Complex.exp (2*ζ)).re ∧
    factor s z=(Complex.exp (2*ζ)-1)/(Complex.exp (2*ζ)+1) ∧
    ‖factor s z‖ ≤ 1 ∧ (‖factor s z‖=1 ↔ |z.im|=height) := by sorry

theorem strip_factor_uniform_limit (s ε : ℝ) (hε : 0 < ε) :
    ∃ R > (0:ℝ), ∀ z : ℂ, |z.im| ≤ height → R ≤ |z.re| → |‖factor s z‖-1| < ε := by sorry

theorem strip_factor_divisor (s : ℝ) :
    (∀ z : ℂ, Complex.sinh (coordinate s z)=0 ↔
      ∃ k : ℤ, z=(s:ℂ)+4*(height:ℂ)*Complex.I*(k:ℂ)) ∧
    (∀ z : ℂ, Complex.cosh (coordinate s z)=0 → 2*height ≤ |z.im|) ∧
    (∀ z : ℂ, |z.im| < 87/100 → AnalyticAt ℂ (factor s) z ∧ (factor s z=0 ↔ z=(s:ℂ))) ∧
    HasDerivAt (factor s) ((Real.pi/(4*height):ℝ):ℂ) (s:ℂ) := by sorry

theorem strip_remove_nodes (S : Finset ℝ) (f : ℂ → ℂ)
    (ha : ∀ z : ℂ, |z.im| < 87/100 → AnalyticAt ℂ f z)
    (hzero : ∀ s ∈ S, f (s:ℂ)=0) :
    ∃ V : ℂ → ℂ, (∀ z : ℂ, |z.im| < 87/100 → AnalyticAt ℂ V z) ∧
      (∀ z : ℂ, |z.im| < 87/100 → f z = V z * ∏ s ∈ S, factor s z) ∧
      ∀ z : ℂ, |z.im| = height → ‖V z‖ = ‖f z‖ := by sorry

theorem strip_rectangle_maximum (f : ℂ → ℂ) (B : ℝ) (hB : 0 < B)
    (ha : ∀ z : ℂ, |z.im| ≤ height → AnalyticAt ℂ f z)
    (hline : ∀ z : ℂ, |z.im| = height → ‖f z‖ < B)
    (hdecay : ∀ ε > (0:ℝ), ∃ R : ℝ, ∀ z : ℂ, |z.im| ≤ height → R ≤ |z.re| → ‖f z‖ < ε) :
    (∃ R₀ > (0:ℝ), ∀ R ≥ R₀, ∃ M < B, ∀ z : ℂ, |z.re| ≤ R → |z.im| ≤ height → ‖f z‖ ≤ M) ∧
    ∀ z : ℂ, |z.im| ≤ height → ‖f z‖ < B := by sorry

theorem strip_center_weight (m : ℕ) (hm : 450 ≤ m) :
    ‖weight m (-1/2)‖ = (1+2/(m:ℝ))^2 ∧ (1+2/(m:ℝ))^2 ≤ (226/225:ℝ)^2 ∧
    23952*(226/225:ℝ)^2 < 24166 ∧ (24166:ℝ) < 25000 := by sorry

end Turan.StripDetails
