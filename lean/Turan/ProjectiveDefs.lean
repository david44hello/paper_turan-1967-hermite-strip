module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs

@[expose] public section

open scoped Turan.NumeralFacts

noncomputable section
open Polynomial
namespace Turan

/-- The three polynomials in each finite projective cover, with the integer
normalizations used to form its Taylor coefficients. -/
def lowBasis (n m : ℕ) : Fin 3 → Polynomial ℂ :=
  if (n,m) = (3,5) then ![8*X+4, 8*X^3+6, 8*X^5+15]
  else if n = 2 then ![8+16*X, -8+16*X^2, 15-30*X^4+4*X^6]
  else if n = 3 then ![15+30*X, 15+30*X+C (5/2)*hermite 3, C (-1/8)*hermite 6]
  else ![15+30*X, C (5/4)*hermite 4, C (1/4)*(hermite 6+15*hermite 4)]

/-- Each chart fixes one coefficient to one. The other two range over
the closed complex box used by the exact verifier. -/
def ProjectiveDiskCheck (basis : Fin 3 → Polynomial ℂ) (grid : ℕ) (height : ℝ) (degree : ℕ) : Prop :=
  ∀ (i : Fin 3) (u : Fin 3 → ℂ), u i = 1 →
    (∀ j, |(u j).re| ≤ 1 ∧ |(u j).im| ≤ 1) →
    ∃ (x y : ℤ) (r k : ℕ), 0 < r ∧ 1 ≤ k ∧ k ≤ degree ∧
      let w : ℂ := ⟨(x : ℝ)/grid, (y : ℝ)/grid⟩
      let ρ : ℝ := (r : ℝ)/grid
      let p := (∑ j, C (u j)*basis j).comp (C w + C (ρ:ℂ)*X)
      |w.im| + ρ ≤ height ∧ (∑ d ∈ p.support.erase k, ‖p.coeff d‖) < ‖p.coeff k‖

def QuinticChartCheck : Prop := ProjectiveDiskCheck (lowBasis 3 5) 65536 (29491/32768) 5
def SexticChartCheck : Prop :=
  ∀ n ∈ ([2,3,4] : List ℕ), ProjectiveDiskCheck (lowBasis n 6) 65536 (57016/65536) 6

end Turan
