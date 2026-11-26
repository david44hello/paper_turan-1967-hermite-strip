module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TrinomialDefs
public import Challenge.GirouxModeDefs
public import Turan.TransferDefs

@[expose] public section
open Polynomial
noncomputable section
namespace Turan.MehlerJets

theorem weight_of_squared_diagonal (n : ℕ) (X Y A : ℝ) (hA : 0 ≤ A)
    (hs : (1/5:ℝ)^n*A^2 ≤ (Real.sqrt (1-1/25:ℝ))⁻¹*Real.exp (X^2/3+Y^2/2)) :
    A*Real.exp (-X^2/2) ≤ (1-(1:ℝ)/25)^(-(1:ℝ)/4)*
      Real.exp (-X^2/3+Y^2/4+((n:ℝ)/2)*Real.log 5) := by sorry

theorem weighted_diagonal_estimate (n : ℕ) (z : ℂ) :
    ‖psi n z‖*Real.exp (-z.re^2/2) ≤ (1-(1:ℝ)/25)^(-(1:ℝ)/4)*
      Real.exp (-z.re^2/3+z.im^2/4+((n:ℝ)/2)*Real.log 5) := by sorry

theorem cubic_trinomial_root_triple (a : ℂ) (ha : a ≠ 0) :
    let G := 1 + 2*X + C a * Giroux.mode 3
    ∃ ζ : Fin 3 → ℂ, (List.ofFn ζ : Multiset ℂ) = G.roots ∧
      (∑ i, (ζ i).im)=0 ∧ (∏ i, ‖ζ i-(-1/2:ℂ)‖)=5/8 ∧
      ∃ i, |(ζ i).re| ≤ 2 ∧ |(ζ i).im| < 76/100 := by sorry

theorem g1_chart_count_given (G1 : TrinomialDiskCheck) (n : ℕ) (hn : 4 ≤ n) (hn' : n ≤ 79)
    (swap : Bool) (θ : ℂ) (hx : |θ.re| ≤ 1) (hy : 0 ≤ θ.im) (hy' : θ.im ≤ 1) :
    ∃ (x y : ℤ) (t k : ℕ), t ∈ ([4,6,8,12,16,24,32] : List ℕ) ∧ 1 ≤ k ∧ k ≤ 4 ∧
      let w : ℂ := ⟨(x:ℝ)/16384,(y:ℝ)/16384⟩
      let r := (t:ℝ)/(16*chartScale n)
      let G := trinomialChart n swap θ
      0 < r ∧ ‖w‖+r < 9/10 ∧ |w.im|+r < 76/100 ∧
      (G.roots.filter (fun z => ‖z-w‖ < r)).card = k ∧
      ∀ z ∈ G.roots, ‖z-w‖ < r → |z.re| ≤ 2 ∧ |z.im| < 76/100 := by sorry

end Turan.MehlerJets
