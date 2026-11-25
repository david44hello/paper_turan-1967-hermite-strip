-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.CircleDefs
import Turan.TransferDefs

noncomputable section
open Polynomial
namespace Turan

def ratioScale (j : ℕ) : ℕ := 2^((scaledNormSq j).log2/2)

def ratioMode (j : ℕ) : Polynomial ℂ := C ((ratioScale j : ℂ)⁻¹) * scaledMode j

/-- Coefficient of degree k in exp(-xrv-r²v²/2). -/
def gaugeCoeff (x r : ℝ) (k : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (k/2+1),
    (-x*r)^(k-2*l)*(-r^2/2)^l /
      (((k-2*l).factorial:ℝ)*(l.factorial:ℝ))

def gaugedJet (j : ℕ) (x r : ℝ) (k : ℕ) : ℂ :=
  let p := diskExpansion (ratioMode j) x r
  ∑ l ∈ Finset.range (k+1), p.coeff l * (gaugeCoeff x r (k-l) : ℂ)

def omittedTail (j : ℕ) (x r : ℝ) : ℝ :=
  let q := circleQ j x (2*r)
  (‖gaugedJet j x r 0‖*seriesUpper q 0 + 2*‖gaugedJet j x r 1‖*seriesUpper q 1)/1024

/-- Pointwise form of the exact coefficient tests on the two ratio charts.
The disk at -1/2 controls the inverse scale. The second disk tests a positive
Taylor coefficient through order ten, with separate bounds for both tails. -/
def RatioCertificate (n m : ℕ) : Prop :=
  ∀ (i j : ℕ), ((i=n ∧ j=m) ∨ (i=m ∧ j=n)) → ∀ χ : ℂ, ‖χ‖ ≤ 1 → 0 ≤ χ.im →
  ∃ (X₀ : ℤ) (R U k : ℕ), 0 < R ∧ 0 < U ∧ 1 ≤ k ∧ k ≤ 10 ∧
    let x : ℝ := X₀/256
    let r : ℝ := R/256
    let r₀ : ℝ := U/256
    r < 87/100 ∧ r₀ < 87/100 ∧ circleQ i x (2*r) ≤ 36 ∧ circleQ j x (2*r) ≤ 36 ∧
    let invBound := (coefficientMass (diskExpansion (ratioMode i) (-1/2) r₀) +
      ‖χ‖*coefficientMass (diskExpansion (ratioMode j) (-1/2) r₀))/(2*r₀)
    let c := fun l => gaugedJet i x r l + χ*gaugedJet j x r l
    (∑ l ∈ (Finset.range 11).erase k, ‖c l‖) + omittedTail i x r + ‖χ‖*omittedTail j x r +
      invBound*(|1+2*x|+2*r)*2^(⌈3*(|x| * r+r^2/2)/2⌉ : ℤ) < ‖c k‖

end Turan
