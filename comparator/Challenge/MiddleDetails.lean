module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Mathlib.Analysis.Analytic.Order
public import Turan.NodeDefs
public import Turan.RouteDefs
public import Turan.ScaledFamily

@[expose] public section
noncomputable section
open Polynomial Set Metric
namespace Turan

/-- A uniform lower bound for one Taylor coefficient and summable upper bounds
for the remaining coefficients give the zero count for each parameter. -/
theorem uniform_dominant_coefficient {α : Type*} (K : Set α)
    (f : α → ℂ → ℂ) (a : α → ℕ → ℂ) (k : ℕ) (hk : 1 ≤ k) (L : ℝ) (U : ℕ → ℝ)
    (hU : Summable U) (hgap : ∑' j, U j < L)
    (hf : ∀ t ∈ K, Differentiable ℂ (f t))
    (ha : ∀ t ∈ K, ∀ z : ℂ, HasSum (fun j => a t j*z^j) (f t z))
    (hl : ∀ t ∈ K, L ≤ ‖a t k‖)
    (hu : ∀ t ∈ K, ∀ j, (if j=k then 0 else ‖a t j‖) ≤ U j) :
    ∀ t ∈ K, ∃ roots : Multiset ℂ, roots.card = k ∧ ∀ z : ℂ,
      (roots.count z : ℕ∞) = if ‖z‖ < 1 then analyticOrderAt (f t) z else 0 := by sorry

theorem circle_joint_cut_on_disk (n m : ℕ) (a b : ℂ) (x r s t : ℝ) (hr : 0 < r)
    (hs : ∀ z ∈ ball (x:ℂ) r, scaledFamily n m a b z ≠ 0)
    (horient : 0 ≤ (a*star b).re * circlePivot n x r * circlePivot m x r)
    (hσ : 0 ≤ s) (hτ : 0 ≤ t) (hst : s^2+t^2 ≤ 1) :
    ‖a‖*(s*|circlePivot n x r| - (circleMass n x r - |circlePivot n x r|)) +
    ‖b‖*(t*|circlePivot m x r| - (circleMass m x r - |circlePivot m x r|)) ≤ |1+2*x|+2*r := by sorry

theorem transfer_outer_cap (S : Polynomial ℂ) (m : ℕ) (b : ℂ) (x r : ℝ) (hr : 0 < r)
    (hsgn : ((hermite m).eval ((x-r:ℝ):ℂ)).re * ((hermite m).eval ((x+r:ℝ):ℂ)).re < 0)
    (hfree : ∀ z ∈ ball (x:ℂ) r, S.eval z + b*(hermite m).eval z ≠ 0) :
    let L := min ‖(hermite m).eval ((x-r:ℝ):ℂ)‖ ‖(hermite m).eval ((x+r:ℝ):ℂ)‖
    let M := sSup ((fun z => ‖S.eval z‖) '' sphere (x:ℂ) r)
    0 < L ∧ ‖b‖ ≤ M/L := by sorry

theorem nominal_chord_in_edge_disk (p : Polynomial ℂ) (u v A B c : ℂ)
    (hc : EdgeCheck p u v A B c) (t : ℝ) (ht : t ∈ Icc 0 1) :
    ‖(1-t) • A + t • B - c‖ < ‖c‖ ∧
    ‖p.eval ((1-t) • u + t • v) - c‖ < ‖c‖ := by sorry

/-- The continuous phase of each certified image edge, expressed in the
disk's branch, has the same total increment as the oriented nominal polygon. -/
theorem checked_edges_winding_equality (p : Polynomial ℂ) (N : ℕ) (v A c : ℕ → ℂ)
    (hv : v N = v 0) (ha : A N = A 0)
    (he : ∀ i < N, EdgeCheck p (v i) (v (i+1)) (A i) (A (i+1)) (c i)) :
    let angle := fun i (t : ℝ) => (p.eval ((1-t) • v i + t • v (i+1)) / c i).arg
    (∀ i < N, ContinuousOn (angle i) (Icc 0 1)) ∧
    (∑ i ∈ Finset.range N, (angle i 1 - angle i 0)) =
      2*Real.pi*((∑ i ∈ Finset.range N, rayCross (A i) (A (i+1)) : ℤ):ℝ) := by sorry

theorem node_pair_continuous_increment (n m : ℕ) (a b : ℂ) (x y : ℝ) (hx : x≠0) (hy : y≠0)
    (hxy : x<y) (hn : divided (nodeMode n) x y=0) (hm : divided (nodeMode m) x y=0)
    (hfree : ∀ t : ℝ, (family n m a b).eval (t:ℂ) ≠ 0) :
    let F := family n m a b
    ∃ A : ℝ → ℝ, Continuous A ∧
      (∀ t : ℝ, Complex.exp ((A t:ℂ)*Complex.I) = F.eval (t:ℂ)/(‖F.eval (t:ℂ)‖:ℂ)) ∧
      ∃ k : ℤ, A (y-1/2)-A (x-1/2) = (F.roots.map (intervalAngle (x-1/2) (y-1/2))).sum ∧
        A (y-1/2)-A (x-1/2) = (2*(k:ℝ)+(if x*y<0 then 1 else 0))*Real.pi := by sorry

end Turan
