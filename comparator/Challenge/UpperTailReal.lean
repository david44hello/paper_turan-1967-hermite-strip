module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Algebra.QuadraticDiscriminant

@[expose] public section

noncomputable section
open Set
namespace Turan.UpperTailReal

def lhs (j : ℝ) := 0.608 * Real.sqrt (2*j - 11.25) - 0.315
def rhs (m n j : ℝ) := Real.log (50000*m^2 / (j*(m-n)))
def margin (m n : ℝ) := lhs n - rhs m n n
def rightMinorant (m : ℝ) := 0.608 * Real.sqrt (2*m - 13.25) - 0.315 - Real.log (50200*m)
def domain : Set (ℝ × ℝ) := {p | 450 ≤ p.1 ∧ p.1/2 ≤ p.2 ∧ p.2 ≤ p.1-1}

theorem global_minimum :
    (450, 225) ∈ domain ∧
    IsLeast ((fun p : ℝ × ℝ => margin p.1 p.2) '' domain) (margin 450 225) ∧
    0.214 < margin 450 225 := by sorry

theorem margin_pos (m n : ℝ) (hm : 450 ≤ m) (hn : n ∈ Icc (m/2) (m-1)) :
    0 < margin m n := by sorry

theorem compare_j (m n : ℝ) (hm : 450 ≤ m) (hn : n ∈ Icc (m/2) (m-1)) :
    StrictMonoOn lhs (Icc n m) ∧ StrictAntiOn (rhs m n) (Icc n m) ∧
    (rhs m n n < lhs n → rhs m n m < lhs m) := by sorry

theorem margin_second (m n : ℝ) (hm : 450 ≤ m) (hn : n ∈ Icc (m/2) (m-1)) :
    let d₂ := -0.608 / (Real.sqrt (2*n-11.25))^3 - 1/n^2 - 1/(m-n)^2
    HasDerivAt (deriv (margin m)) d₂ n ∧ d₂ < 0 := by sorry

theorem minimum_at_an_endpoint (m : ℝ) (hm : 450 ≤ m) :
    StrictConcaveOn ℝ (Icc (m/2) (m-1)) (margin m) ∧
    IsLeast (margin m '' Icc (m/2) (m-1)) (min (margin m (m/2)) (margin m (m-1))) := by sorry

theorem left_endpoint (m : ℝ) (hm : 450 ≤ m) :
    rhs m (m/2) (m/2) = Real.log 200000 ∧
    margin m (m/2) = 0.608*Real.sqrt (m-11.25)-0.315-Real.log 200000 ∧
    12.4203 < lhs 225 ∧ Real.log 200000 < 12.2061 ∧
    (0.214 : ℝ) < 12.4203-12.2061 ∧ margin 450 225 < 0.215 := by sorry

theorem right_endpoint (m : ℝ) (hm : 450 ≤ m) :
    50000*m/(m-1) ≤ 50000*450/449 ∧ (50000*450/449 : ℝ) < 50200 ∧
    rhs m (m-1) (m-1) ≤ Real.log (50200*m) ∧ rightMinorant m ≤ margin m (m-1) ∧
    17.7902 < lhs 449 ∧ Real.log (50200*450) < 16.9331 ∧
    (0.857 : ℝ) < 17.7902-16.9331 := by sorry

theorem endpoint_derivatives (m : ℝ) (hm : 450 ≤ m) :
    let L := 0.304 / Real.sqrt (m-11.25)
    let R := 0.608 / Real.sqrt (2*m-13.25) - 1/m
    HasDerivAt (fun t => margin t (t/2)) L m ∧ 0 < L ∧
    HasDerivAt rightMinorant R m ∧ 0 < R ∧
    discrim (0.369664 : ℝ) (-2) 13.25 < 0 ∧ 0 < 0.369664*m^2-2*m+13.25 := by sorry

theorem endpoint_persistence :
    StrictMonoOn (fun m => margin m (m/2)) (Ici 450) ∧
    StrictMonoOn rightMinorant (Ici 450) := by sorry

end Turan.UpperTailReal
