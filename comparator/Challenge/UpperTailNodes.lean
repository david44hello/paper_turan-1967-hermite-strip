-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.TailDefs
import Mathlib.Analysis.Convex.Deriv

noncomputable section
open Set
namespace Turan.UpperTailNodes

def alpha : ℝ := 11*Real.pi/28
def eta (j : ℕ) : ℝ := Real.pi / Real.sqrt (2*(j:ℝ)-11.25)
def nodeCount (j : ℕ) : ℕ := ⌊3 / eta j⌋₊
def center : ℝ := -1/2
def logCoth (v : ℝ) : ℝ := Real.log ((Real.tanh (alpha*v))⁻¹)
def oddFreq (i : ℕ) : ℝ := 2*(i:ℝ)+1

/-- Count all distinct Hermite zeros strictly nearer on the indicated side.
The calls below use signs +1 and -1. -/
def nearer (j : ℕ) (sign t : ℝ) : ℕ :=
  ((hermite j).roots.toFinset.filter fun z =>
    z.im = 0 ∧ 0 < sign*(z.re-center) ∧ sign*(z.re-center) < t).card

/-- The rank equalities force the actual consecutive zeros on each side. -/
theorem ordered_nodes (j : ℕ) (hj : 225 ≤ j) (h0 : psi j (-1/2) ≠ 0) :
    0 < nodeCount j ∧ ∃ d e : Fin (nodeCount j) → ℝ, StrictMono d ∧ StrictMono e ∧
    (∀ i, d i ∈ Ioc 0 3 ∧ e i ∈ Ioc 0 3 ∧
      psi j ((center+d i : ℝ) : ℂ) = 0 ∧ psi j ((center-e i : ℝ) : ℂ) = 0 ∧
      nearer j 1 (d i) = i.val ∧ nearer j (-1) (e i) = i.val ∧
      d i + e i ≤ (2*(i.val:ℝ)+1)*eta j) ∧
    (∀ i : Fin (nodeCount j), i.val = 0 → d i < eta j ∧ e i < eta j ∧ d i+e i ≤ eta j) ∧
    (∀ i k : Fin (nodeCount j), k.val = i.val+1 → d k ≤ d i+eta j ∧ e k ≤ e i+eta j) := by sorry

/-- The weight and its first two derivatives on the open positive ray. -/
theorem logCoth_shape :
    StrictAntiOn logCoth (Ioi 0) ∧ StrictConvexOn ℝ (Ioi 0) logCoth ∧
    ∀ v : ℝ, 0 < v → 0 < logCoth v ∧
      HasDerivAt logCoth (-2*alpha/Real.sinh (2*alpha*v)) v ∧
      HasDerivAt (deriv logCoth)
        (4*alpha^2*Real.cosh (2*alpha*v)/(Real.sinh (2*alpha*v))^2) v := by sorry

/-- The pair is compared before any frequency truncation; i=0 is the first pair. -/
theorem pair_midpoint (d e h : ℝ) (i : ℕ) (hd : 0 < d) (he : 0 < e) (hh : 0 < h)
    (hpair : d+e ≤ (2*(i:ℝ)+1)*h) :
    2*logCoth (((i:ℝ)+1/2)*h) ≤ logCoth d + logCoth e := by sorry

def midpointSum (N : ℕ) (h : ℝ) : ℝ :=
  2 * ∑ i : Fin N, logCoth (((i.val:ℝ)+1/2)*h)

def oddContribution (N : ℕ) (h : ℝ) (i : ℕ) : ℝ :=
  2*(1-Real.exp (-2*alpha*oddFreq i*(N:ℝ)*h)) /
    (oddFreq i*Real.sinh (alpha*oddFreq i*h))

/-- HasSum records convergence and the value of the full odd series. -/
theorem full_midpoint_series (N : ℕ) (h : ℝ) (hh : 0 < h) :
    HasSum (oddContribution N h) (midpointSum N h) := by sorry

theorem full_node_lower_bound (j : ℕ) (hj : 225 ≤ j) (h0 : psi j (-1/2) ≠ 0) :
    midpointSum (nodeCount j) (eta j) ≤ -Real.log (nodeProduct j) ∧
    (∑' i : ℕ, oddContribution (nodeCount j) (eta j) i) ≤ -Real.log (nodeProduct j) := by sorry

/-- This retains the printed intermediate exponential for each of the five odd terms. -/
theorem numerator_chain (j : ℕ) (hj : 225 ≤ j) (i : Fin 5) :
    eta j < 0.151 ∧ 2.849 < 3-eta j ∧ 3-eta j < (nodeCount j:ℝ)*eta j ∧
    0.998 < 1-Real.exp (-2*alpha*2.849) ∧
    1-Real.exp (-2*alpha*2.849) ≤ 1-Real.exp (-2*alpha*oddFreq i*(nodeCount j:ℝ)*eta j) := by sorry

/-- All Taylor orders and the two regimes in the reciprocal-sinh estimate. -/
theorem factorial_bound (k : ℕ) : 6^k ≤ (2*k+1).factorial := by sorry

theorem small_sinh_series (t : ℝ) (ht : 0 < t) (hsmall : t^2 < 6) :
    (∀ k : ℕ, t^(2*k) / ((2*k+1).factorial:ℝ) ≤ (t^2/6)^k) ∧
    HasSum (fun k : ℕ => (t^2/6)^k) (1/(1-t^2/6)) ∧
    Real.sinh t / t ≤ (∑' k : ℕ, (t^2/6)^k) ∧ 1/t-t/6 ≤ 1/Real.sinh t := by sorry

theorem large_sinh_sign (t : ℝ) (ht : 0 < t) (hlarge : 6 ≤ t^2) :
    1/t-t/6 ≤ 0 ∧ 0 < 1/Real.sinh t := by sorry

def sigmaFive : ℝ := ∑ i ∈ Finset.range 5, 1/(oddFreq i)^2

/-- The weakening drops 0.998 from the negative term only. -/
theorem five_term_linear (j : ℕ) (hj : 225 ≤ j) (h0 : psi j (-1/2) ≠ 0) :
    let slope := 2*0.998*sigmaFive/(alpha*Real.pi)
    let penalty := 5*alpha*eta j/3
    let retained := 2*0.998*(sigmaFive/(alpha*eta j)-5*alpha*eta j/6)
    slope*Real.sqrt (2*(j:ℝ)-11.25)-penalty ≤ retained ∧
    retained ≤ -Real.log (nodeProduct j) ∧
    sigmaFive = 117469/99225 ∧ 1.18386 < sigmaFive ∧
    alpha < 1.2342 ∧ alpha*Real.pi < 3.8774 ∧
    0.6094 < (2.36299/3.8774 : ℝ) ∧ (2.36299/3.8774 : ℝ) < slope ∧
    penalty < 5*1.2342*0.151/3 ∧ (5*1.2342*0.151/3 : ℝ) < 0.3107 := by sorry

end Turan.UpperTailNodes
