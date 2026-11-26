module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs

@[expose] public section

noncomputable section
namespace Turan

-- 147, line 1757. X = 4x², Y = 4y² in case (A).
theorem quartic_balanced_intermediate_bound {X Y β : ℝ} (hY : 2 < Y)
    (hX : (X - 2) * (β^2 - 2*β + 2 + Y) = 2 - β^2) :
    X ≤ 2 + 2/(1 + Y) ∧ 2 + 2/(1 + Y) < Y + 2 := sorry

-- 148, lines 1774–1778
theorem quartic_upper_divided_coefficient {α : ℂ} (hα : 0 < α.im) :
    let H := 12*α - 2
    let c := α + 1/2 - 1/H
    H ≠ 0 ∧ (12*α^2 + 4*α - 2)/H = c ∧
      c.im = α.im + 12*α.im/‖H‖^2 ∧ 0 < c.im := sorry

theorem quartic_upper_divided_recovery {α : ℂ} (hα : 0 < α.im) {l₁ l₀ : ℝ}
    (heq : (12*α - 2) * (l₀ : ℂ) =
      -(12*α^4 + 16*α^3 + 12*α^2 - 3) + (12*α^2 + 4*α - 2) * (l₁ : ℂ)) :
    let H := 12*α - 2
    let g := (12*α^4 + 16*α^3 + 12*α^2 - 3)/H
    let c := α + 1/2 - 1/H
    (l₀ : ℂ) = -g + c * (l₁ : ℂ) ∧
      l₁ = g.im/c.im ∧ l₀ = -g.re + c.re*l₁ := sorry

-- 149, lines 1786–1789. The multiset allows any repeated pair and t = 0.
theorem quartic_repeated_upper_offsets {p q r : ℂ}
    (hq : q.im = p.im) (hr : r.im = p.im) (hrep : p = q ∨ p = r ∨ q = r) :
    let α := (p + q + r)/3
    ∃ t : ℝ, let z₀ := α + (t : ℂ)
             let v := α - 2*(t : ℂ)
             ({p, q, r} : Multiset ℂ) = {z₀, z₀, v} ∧ v.re - z₀.re = -3*t := sorry

end Turan
