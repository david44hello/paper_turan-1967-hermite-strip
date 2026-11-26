module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Normalized

@[expose] public section

open scoped Turan.NumeralFacts

noncomputable section
open Polynomial
namespace Turan

/-- The integer scale used by the finite trinomial certificates. -/
def chartScale (n : ℕ) : ℕ := (2*n - 1).sqrt + 1

/-- The even polynomial has value one at zero. The odd polynomial has
derivative equal to the integer scale there. -/
def chartMode (n : ℕ) : Polynomial ℂ :=
  let p := hermite n
  let s := if Even n then (p.eval 0)⁻¹ else (chartScale n : ℂ)/p.derivative.eval 0
  C s * p

def trinomialChart (n : ℕ) (swap : Bool) (θ : ℂ) : Polynomial ℂ :=
  let low := C (chartScale n : ℂ) * (X + C (1/2))
  if swap then C θ * low + chartMode n else low + C θ * chartMode n

/-- The uniform coefficient inequalities supplied by the supplement's finite
dyadic covers. The centers and radii have the same grids as its records. -/
def TrinomialDiskCheck : Prop :=
  ∀ n : ℕ, 4 ≤ n → n ≤ 79 → ∀ (swap : Bool) (θ : ℂ),
    |θ.re| ≤ 1 → 0 ≤ θ.im → θ.im ≤ 1 →
    ∃ (x y : ℤ) (t k : ℕ), t ∈ ([4,6,8,12,16,24,32] : List ℕ) ∧ 1 ≤ k ∧ k ≤ 4 ∧
      let w : ℂ := ⟨(x : ℝ)/16384, (y : ℝ)/16384⟩
      let r : ℝ := (t : ℝ)/(16*chartScale n)
      let p := (trinomialChart n swap θ).comp (C w + C (r : ℂ)*X)
      ‖w‖ + r < 9/10 ∧ |w.im| + r < 76/100 ∧
        (∑ d ∈ p.support.erase k, ‖p.coeff d‖) < ‖p.coeff k‖

end Turan
