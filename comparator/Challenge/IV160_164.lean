module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Challenge.Small56SourceDefs

@[expose] public section

noncomputable section

open scoped Topology
open Polynomial
namespace Turan.Small56

def shiftedNodeValue (l : ℕ) (w : ℝ) : ℂ := (hermite l).eval ((w : ℂ) - 1/2) / w

def nodeDividedDifference (l : ℕ) (g d : ℝ) : ℂ :=
  (shiftedNodeValue l g - shiftedNodeValue l d) / ((g : ℂ) - d)

/-- Polynomial long division in the shifted variable w. -/
def quadraticRemainder (l : ℕ) (S p : ℝ) : Polynomial ℂ :=
  ((hermite l).comp (X - C (1/2))) %ₘ (X^2 - C (S : ℂ) * X + C (p : ℂ))

theorem divided_difference_of_remainder (l : ℕ) (S p g d : ℝ)
    (hg : g^2 - S*g + p = 0) (hd : d^2 - S*d + p = 0)
    (hne : g ≠ d) (hg0 : g ≠ 0) (hd0 : d ≠ 0) :
    let rem := quadraticRemainder l S p
    (∀ w ∈ ({g, d} : Set ℝ), shiftedNodeValue l w = rem.coeff 0 / w + rem.coeff 1) ∧
    nodeDividedDifference l g d = -(rem.coeff 0) / p := sorry

/-- The A.3 definition of a pair of nodes, specialized to the two public
constant-remainder formulas. No eliminant or denominator premise is needed. -/
theorem nodes_iff_zero_remainders (S p g d : ℝ)
    (hg : g^2 - S*g + p = 0) (hd : d^2 - S*d + p = 0)
    (hne : g ≠ d) (hg0 : g ≠ 0) (hd0 : d ≠ 0) :
    (nodeDividedDifference 5 g d = 0 ∧ nodeDividedDifference 6 g d = 0) ↔
      remainder5 S p = 0 ∧ remainder6 S p = 0 := sorry

/-- The zipped lists encode the five oriented rows, repeated with their
multiplicities. Entry.cert supplies both closed boxes and the node equation. -/
theorem table_entry_strict_lower (e : Entry)
    (hrow : (e.G, e.D) ∈ Certificate.gamma.zip Certificate.delta) :
    lower e < |e.g / e.d| := sorry

def nodeQuotient (s : List Entry) (w : ℂ) : ℂ :=
  (s.map (fun e => (w - e.g) / (w - e.d))).prod

theorem node_quotient_strict_transfer (s : List Entry)
    (hg : s.map Entry.G = Certificate.gamma) (hd : s.map Entry.D = Certificate.delta)
    (w : ℂ) (hw : 43/50 ≤ |w.im|) :
    let B : ℝ := (9/5) * (1 + 1/430000)^24
    ‖nodeQuotient s w‖ < B ∧ B < 181/100 := sorry

/-- Each integer coordinate in the certificate is in millionths. -/
def modelFactorProduct (cs : List ℤ) (w : ℂ) : ℂ :=
  (cs.map (fun n => w - (n : ℂ)/1000000)).prod

def modelQuotient (w : ℂ) : ℂ :=
  modelFactorProduct Certificate.gamma w / modelFactorProduct Certificate.delta w

theorem model_quotient_strict (w : ℂ) (hw : 43/50 ≤ |w.im|) :
    ‖modelQuotient w‖ < 9/5 := sorry

theorem model_poles_and_infinity :
    (∀ w : ℂ, (Filter.Tendsto (fun z => ‖modelQuotient z‖) (𝓝[≠] w) Filter.atTop ↔
      ∃ n ∈ Certificate.delta, w = (n : ℂ)/1000000)) ∧
    (∀ w : ℂ, (∀ n ∈ Certificate.delta, w ≠ (n : ℂ)/1000000) →
      AnalyticAt ℂ modelQuotient w) ∧
    Filter.Tendsto modelQuotient (Filter.cocompact ℂ) (𝓝 1) := sorry

theorem model_boundary_margin :
    ∃ B ∈ Set.Ioo (1 : ℝ) (9/5), ∀ w : ℂ, w.im = 43/50 → ‖modelQuotient w‖ ≤ B := sorry

theorem model_half_disk_extension (B : ℝ) (hB : 1 < B)
    (hline : ∀ w : ℂ, w.im = 43/50 → ‖modelQuotient w‖ ≤ B) :
    let c : ℂ := (43/50) * Complex.I
    (∃ R₀ > (0 : ℝ), ∀ R ≥ R₀,
      (∀ w : ℂ, 43/50 ≤ w.im → ‖w-c‖ = R → ‖modelQuotient w‖ ≤ B) ∧
      (∀ w : ℂ, 43/50 ≤ w.im → ‖w-c‖ ≤ R → ‖modelQuotient w‖ ≤ B)) ∧
    (∀ w : ℂ, modelQuotient (star w) = star (modelQuotient w)) ∧
    (∀ w : ℂ, 43/50 ≤ |w.im| → ‖modelQuotient w‖ ≤ B) := sorry

end Turan.Small56
