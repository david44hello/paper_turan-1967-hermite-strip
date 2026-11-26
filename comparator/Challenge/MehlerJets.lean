module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Normalized
public import Challenge.MehlerDiagonalDef
public import Challenge.GirouxModeDefs
public import Turan.Oscillator
public import Turan.TransferDefs
public import Turan.TrinomialDefs

@[expose] public section

noncomputable section
open Polynomial
open scoped ComplexConjugate
namespace Turan.MehlerJets

def spatialSeries (p : ℂ × ℂ) : ℂ :=
  ∑' k : ℕ, (1/5 : ℂ)^k * psi k p.1 * psi k p.2

def spatialKernel (p : ℂ × ℂ) : ℂ :=
  (Real.sqrt (1-(1/5:ℝ)^2) : ℂ)⁻¹ * Complex.exp
    ((2*p.1*p.2/5-(p.1^2+p.2^2)/25)/(1-(1/5:ℂ)^2))

theorem mehler_spatial_entire (p : ℂ × ℂ) :
    AnalyticAt ℂ spatialSeries p ∧ AnalyticAt ℂ spatialKernel p := by sorry

theorem spatial_eq_of_real_plane (f g : ℂ × ℂ → ℂ)
    (hf : ∀ p, AnalyticAt ℂ f p) (hg : ∀ p, AnalyticAt ℂ g p)
    (hreal : ∀ x y : ℝ, f ((x:ℂ),(y:ℂ)) = g ((x:ℂ),(y:ℂ))) :
    f = g := by sorry

theorem diagonal_substitution (z : ℂ) (r : ℝ) :
    z^2 + (conj z)^2 = ((2*(z.re^2-z.im^2) : ℝ) : ℂ) ∧
    2*z*conj z*(r:ℂ) - (z^2+(conj z)^2)*(r:ℂ)^2 =
      ((2*r*(z.re^2+z.im^2)-2*r^2*(z.re^2-z.im^2) : ℝ) : ℂ) := by sorry

theorem diagonal_exponent (z : ℂ) (r : ℝ) (hr : 0 ≤ r) (hr' : r < 1) :
    diagonalExponent z r =
      ((2*r/(1+r)*z.re^2 + 2*r/(1-r)*z.im^2 : ℝ) : ℂ) ∧
    diagonalExponent z (1/5) = ((z.re^2/3 + z.im^2/2 : ℝ) : ℂ) := by sorry

theorem mehler_diagonal_extraction (z : ℂ) (n : ℕ) :
    let a := fun k : ℕ => (1/5 : ℝ)^k * ‖psi k z‖^2
    let S := (Real.sqrt (1-1/25 : ℝ))⁻¹ * Real.exp (z.re^2/3 + z.im^2/2)
    (∀ k, (1/5 : ℂ)^k * psi k z * psi k (conj z) = (a k : ℂ)) ∧
    (∀ k, 0 ≤ a k) ∧ HasSum a S ∧ a n ≤ S := by sorry

theorem step_two_strict_geometry (m x : ℝ) (hm : 450 ≤ m)
    (hlo : Real.sqrt (9*m/5) ≤ x) (z : ℂ) (hz : ‖z-(x:ℂ)‖ = 1/Real.sqrt m) :
    let s := Real.sqrt m
    MonotoneOn (fun t : ℝ => t^2-2*t/s) (Set.Ici (1/s)) ∧
    0 < x-1/s ∧ x-1/s ≤ z.re ∧
    (x-1/s)^2-1/m ≤ z.re^2-z.im^2 ∧
    (x-1/s)^2-1/m = x^2-2*x/s ∧
    9*m/5-2*Real.sqrt (9/5) ≤ x^2-2*x/s ∧
    9*m/5-27/10 < 9*m/5-2*Real.sqrt (9/5) := by sorry

theorem step_two_low_mode (n m : ℕ) (hm : 450 ≤ m) (hn : 2*n ≤ m) (x : ℝ)
    (hlo : Real.sqrt (9*(m:ℝ)/5) ≤ x) (z : ℂ)
    (hz : ‖z-(x:ℂ)‖ = 1/Real.sqrt m) (hphi : 1/(5*Real.sqrt m) < ‖phi m z‖) :
    let M := (m:ℝ)
    let E := -(3/5-Real.log 5/4)*M + 9/10 + 5/(12*M)
    let P := (25/24 : ℝ) ^ (1/4 : ℝ)
    ‖psi n z / psi m z‖ < 5*P*Real.sqrt M*Real.exp E ∧
    E < -(197/1000)*M + 901/1000 ∧ 5*P*Real.exp (901/1000) < 25/2 ∧
    ‖psi n z‖ < (25/2)*Real.sqrt M*Real.exp (-(197/1000)*M)*‖psi m z‖ := by sorry

theorem step_two_affine_arithmetic (m : ℕ) (hm : 450 ≤ m) (x : ℝ)
    (hlo : Real.sqrt (9*(m:ℝ)/5) ≤ x)
    (hhi : x ≤ Real.sqrt (9*(m:ℝ)/5) + 3*Real.pi/Real.sqrt m)
    (z : ℂ) (hz : ‖z-(x:ℂ)‖ = 1/Real.sqrt m)
    (hphi : 1/(5*Real.sqrt m) < ‖phi m z‖) :
    let M := (m:ℝ)
    let s := Real.sqrt M
    let L := 2*Real.sqrt (9/5) + 1/s + (6*Real.pi+2)/M
    ‖1+2*z‖ ≤ L*s ∧ L < 278/100 ∧
    ‖(1+2*z) / psi m z‖ < 14*Real.exp (27/20)*M*Real.exp (-(9/10)*M) ∧
    14*Real.exp (27/20) < 55 ∧ (11/4)*s < Real.exp ((703/1000)*M) ∧
    55*M*Real.exp (-(9/10)*M) < 20*s*Real.exp (-(197/1000)*M) := by sorry

theorem trinomial_distance_product (n : ℕ) (hn : 2 ≤ n) (a : ℂ) (ha : a ≠ 0) :
    let G : Polynomial ℂ := 1 + 2*X + C a * Giroux.mode n
    (G.roots.map (fun ζ : ℂ => ‖ζ-(-1/2 : ℂ)‖)).prod =
      ‖(hermite n).eval (-1/2)‖ / (2:ℝ)^n := by sorry

theorem cubic_large_imaginary_factor (ζ : Fin 3 → ℂ)
    (hsum : (∑ i, (ζ i).im) = 0) (him : ∀ i, 76/100 ≤ |(ζ i).im|) :
    (∃ i, 152/100 ≤ |(ζ i).im|) ∧
    (76/100:ℝ)^2*(152/100) ≤ ∏ i, ‖ζ i - (-1/2:ℂ)‖ ∧
    (5/8:ℝ) < (76/100:ℝ)^2*(152/100) := by sorry

def g1Jet (n : ℕ) (ω : ℂ) (l : ℕ) : ℂ :=
  (diskExpansion (chartMode n) ω (1/(chartScale n : ℝ))).coeff l

theorem g1_derivative_recurrence (n : ℕ) (hn : 4 ≤ n) (hn' : n ≤ 79)
    (ω : ℂ) (hω : 2*‖ω‖ ≤ (chartScale n : ℝ)) :
    let N := (chartScale n : ℂ)
    let γ := g1Jet n ω
    (∀ l : ℕ, (l.factorial:ℂ)*γ l = (derivative^[l] (chartMode n)).eval ω / N^l) ∧
    (∀ l : ℕ, ((l+2).factorial:ℂ)*γ (l+2) =
      (2*ω/N)*((l+1).factorial:ℂ)*γ (l+1) +
      (2*((l:ℂ)-(n:ℂ))/N^2)*(l.factorial:ℂ)*γ l) ∧
    ‖2*ω/N‖ ≤ 1 ∧ (∀ l : ℕ, l ≤ n → ‖2*((l:ℂ)-(n:ℂ))/N^2‖ ≤ 1) ∧
    (∀ l : ℕ, n < l → γ l = 0) := by sorry

theorem g1_factorial_tail (n : ℕ) (hn : 4 ≤ n) (hn' : n ≤ 79)
    (ω : ℂ) (hω : 2*‖ω‖ ≤ (chartScale n : ℝ)) (l : ℕ) :
    let γ := g1Jet n ω
    (l.factorial:ℝ)*‖γ l‖ ≤ (2:ℝ)^l * max ‖γ 0‖ ‖γ 1‖ := by sorry

theorem g1_original_disk_count (n : ℕ) (swap : Bool) (θ ω : ℂ) (ρ : ℝ) (k : ℕ)
    (hρ : 0 < ρ) (hk : 1 ≤ k) (hsize : ‖ω‖+ρ < 9/10) (hheight : |ω.im|+ρ < 76/100)
    (hdom : let p := diskExpansion (trinomialChart n swap θ) ω ρ
      (∑ j ∈ p.support.erase k, ‖p.coeff j‖) < ‖p.coeff k‖) :
    let G := trinomialChart n swap θ
    (G.roots.filter (fun z => ‖z-ω‖ < ρ)).card = k ∧
    ∀ z ∈ G.roots, ‖z-ω‖ < ρ → |z.re| ≤ 2 ∧ |z.im| < 76/100 := by sorry

end Turan.MehlerJets
