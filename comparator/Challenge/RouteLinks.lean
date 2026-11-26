module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.RouteDefs
public import Turan.TailDefs

@[expose] public section
open Polynomial Metric
namespace Turan

theorem transfer_arbitrary_perturbation (check : UniformTransferCheck) (n : ℕ)
    (hn : 2 ≤ n) (hn' : n ≤ 7) (swap : Bool) (θ : ℂ) (hχ : |θ.re| ≤ 1)
    (him : 0 ≤ θ.im) (him' : θ.im ≤ 1) :
    ∃ (w : ℂ) (r : ℝ), 0 < r ∧ ‖w‖+r ≤ 5/4 ∧ |w.im|+r < 87/100 ∧
      ∀ g : Polynomial ℂ, (∀ z : ℂ, ‖z‖ ≤ 5/4 → ‖g.eval z‖ < 1/64) →
        ∃ z ∈ ball w r, (transferPencil n swap θ+g).eval z = 0 := by sorry

theorem polygon_forces_zero_in_convex_set (p : Polynomial ℂ) (K : Set ℂ) (hK : Convex ℝ K)
    (hc : IsCompact K) (N : ℕ) (v A center : ℕ → ℂ) (hN : 0 < N)
    (hv : v N = v 0) (hA : A N = A 0) (hk : ∀ i ≤ N, v i ∈ K)
    (he : ∀ i < N, EdgeCheck p (v i) (v (i+1)) (A i) (A (i+1)) (center i))
    (hcros : 0 < ∑ i ∈ Finset.range N, rayCross (A i) (A (i+1))) :
    ∃ z ∈ K, p.eval z = 0 := by sorry

theorem interval_angle_cot (l r : ℝ) (hlr : l < r) (z : ℂ) (hz : z.im ≠ 0) :
    let μ := (l+r)/2
    let s := (r-l)/2
    Real.cot |intervalAngle l r z| = ((z.re-μ)^2+z.im^2-s^2)/(2*|z.im| * s) := by sorry

theorem equal_value_angle_sum (p : Polynomial ℂ) (l r : ℝ) (hlr : l < r)
    (hl : l ≠ -1/2) (hr : r ≠ -1/2) (hfree : ∀ x : ℝ, p.eval (x:ℂ) ≠ 0)
    (hval : p.eval (r:ℂ) / p.eval (l:ℂ) = (2*(r:ℂ)+1)/(2*(l:ℂ)+1)) :
    ∃ k : ℤ, (p.roots.map (intervalAngle l r)).sum =
      (2*(k:ℝ)+(if l < -1/2 ∧ -1/2 < r then 1 else 0))*Real.pi := by sorry

theorem caratheodory_all_orders (g : ℂ → ℂ) (z : ℂ) (R : ℝ) (hr : 0 < R)
    (hg : DifferentiableOn ℂ g (ball z R)) (hpos : ∀ w ∈ ball z R, 0 ≤ (g w).re)
    (l : ℕ) (hl : 1 ≤ l) :
    ‖iteratedDeriv l g z‖ ≤ 2*(l.factorial:ℝ)*(g z).re/R^l := by sorry

theorem projected_mode_identity (n m j j' : ℕ) (hn : 2 ≤ n) (hnm : n<m)
    (hj : (j=n ∧ j'=m) ∨ (j=m ∧ j'=n)) (a b : ℂ) (z : ℂ)
    (hz : 1+2*(1-1/(n:ℂ))*(1-1/(m:ℂ))*z ≠ 0) :
    let p := family n m a b
    let β := if j=n then a else b
    let t := EStar p + C (j':ℂ)*p
    ((j':ℂ)-j)*β*(hermite j).eval z =
      (1-projectedRatio n m j' z)*t.eval z -
        (projectedRatio n m j' z/(j:ℂ))*(EStar t).eval z := by sorry

end Turan
