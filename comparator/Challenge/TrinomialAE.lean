-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Challenge.GirouxModeDefs
import Turan.SlotDefs
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section
open Polynomial Metric Set
open scoped ComplexConjugate
namespace Turan.TrinomialAE

abbrev w₀ : ℝ := -1/2
abbrev R : ℝ := 65/100
abbrev outerRadius : ℝ := 76/100
abbrev clearance : ℝ := 11/100
abbrev diameter : Set ℝ := Ioo (w₀-R) (w₀+R)

/-- Giroux.mode_eval identifies the last summand with a times ψₙ. -/
def G (n : ℕ) (a : ℂ) : Polynomial ℂ := 1 + 2*X + C a * Giroux.mode n

def reflectedValue (p : Polynomial ℂ) (z : ℂ) : ℂ := conj (p.eval (conj z))

def LogOn (f g : ℂ → ℂ) (D : Set ℂ) : Prop :=
  AnalyticOnNhd ℂ f D ∧ ∀ z ∈ D, Complex.exp (f z) = g z

/-- A real-valued continuous lift of the argument, allowing any choice at the initial point. -/
def PhaseOn (θ : ℝ → ℝ) (p : Polynomial ℂ) (S : Set ℝ) : Prop :=
  ContinuousOn θ S ∧ ∀ t ∈ S, p.eval (t:ℂ) ≠ 0 ∧
    (θ t : Real.Angle) = ((p.eval (t:ℂ)).arg : Real.Angle)

def logBound (x : ℝ) := Real.log (90*x)
def beta (x : ℝ) := Real.pi / Real.sqrt (2*x)
def J (u : ℝ) := Real.artanh (u/R)

def normalizedLog (n : ℕ) (f : ℂ → ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  (Real.pi : ℂ) * (f z - f (t:ℂ)) / ((4*logBound n : ℝ):ℂ)

theorem boundary_derivatives (p : Polynomial ℂ) (n : ℕ) (hn : 80 ≤ n)
    (hdeg : p.natDegree ≤ n) (z : ℂ) (hz : z ∈ sphere (w₀:ℂ) R)
    (hlocal : ∀ w ∈ ball z clearance, p.eval w ≠ 0) :
    (∀ w ∈ p.roots, clearance ≤ ‖z-w‖) ∧ ‖z‖ ≤ 1.15 ∧
    ‖p.derivative.eval z / p.eval z‖ ≤ (n:ℝ)/clearance ∧
    ‖p.derivative.derivative.eval z / p.eval z‖ ≤
      (n:ℝ)*((n:ℝ)-1)/clearance^2 ∧
    ‖(removeMode n p).eval z / p.eval z‖ ≤
      1 + 1.15/clearance + ((n:ℝ)-1)/(2*clearance^2) ∧
    1 + 1.15/clearance + ((n:ℝ)-1)/(2*clearance^2) < 43*(n:ℝ) := by sorry

theorem affine_quotient (n : ℕ) (hn : 80 ≤ n) (a z : ℂ) (hz : z ∈ sphere (w₀:ℂ) R) :
    let g := (removeMode n (G n a)).eval z
    g = 1 + 2*(1-1/(n:ℂ))*z ∧
    1.3*(1-1/(n:ℝ)) - 1/(n:ℝ) ≤ ‖g‖ ∧ g ≠ 0 ∧
    ‖(1+2*z)/g‖ ≤ R/(R*(1-1/(n:ℝ))-1/(2*(n:ℝ))) ∧
    R/(R*(1-1/(n:ℝ))-1/(2*(n:ℝ))) ≤ R/0.635625 ∧ R/0.635625 < 1.03 := by sorry

theorem reciprocal_ratios (n : ℕ) (hn : 80 ≤ n) (a z : ℂ) (ha : a ≠ 0)
    (hz : z ∈ sphere (w₀:ℂ) R)
    (hlocal : ∀ b : ℂ, b = a ∨ b = conj a →
      ∀ w ∈ ball z clearance, (G n b).eval w ≠ 0) :
    ∀ b : ℂ, b = a ∨ b = conj a →
      let g := (G n b).eval z
      let Lg := (removeMode n (G n b)).eval z
      ‖(G n (conj b)).eval z / g‖ ≤ 1+2*‖(1+2*z)/Lg‖*‖Lg/g‖ ∧
      1+2*‖(1+2*z)/Lg‖*‖Lg/g‖ < 1+2*1.03*43*(n:ℝ) ∧
      1+2*1.03*43*(n:ℝ) < 90*(n:ℝ) := by sorry

theorem outer_log (p : Polynomial ℂ)
    (hfree : ∀ z ∈ ball (w₀:ℂ) outerRadius, p.eval z ≠ 0) :
    ∃ L : ℂ → ℂ, LogOn L (fun z => p.eval z) (ball (w₀:ℂ) outerRadius) ∧
      LogOn (fun z => L z - conj (L (conj z))) (fun z => p.eval z / reflectedValue p z)
        (ball (w₀:ℂ) outerRadius) := by sorry

theorem closed_log_bound (p : Polynomial ℂ) (n : ℕ) (hn : 80 ≤ n) (f : ℂ → ℂ)
    (hf : LogOn f (fun z => p.eval z / reflectedValue p z) (ball (w₀:ℂ) outerRadius))
    (hbd : ∀ z ∈ sphere (w₀:ℂ) R, ‖p.eval z / reflectedValue p z‖ < 90*n ∧
      ‖reflectedValue p z / p.eval z‖ < 90*n) :
    InnerProductSpace.HarmonicOnNhd (fun z => (f z).re) (ball (w₀:ℂ) outerRadius) ∧
    ∀ z ∈ closedBall (w₀:ℂ) R, (f z).re = Real.log ‖p.eval z / reflectedValue p z‖ ∧
      |(f z).re| < logBound n := by sorry

theorem diameter_derivative (p : Polynomial ℂ) (f : ℂ → ℂ)
    (hf : LogOn f (fun z => p.eval z / reflectedValue p z) (ball (w₀:ℂ) outerRadius)) :
    (∃ θ : ℝ → ℝ, PhaseOn θ p diameter) ∧
    ∀ θ : ℝ → ℝ, PhaseOn θ p diameter → ∀ t ∈ diameter,
      HasDerivAt θ (p.derivative.eval (t:ℂ) / p.eval (t:ℂ)).im t ∧
      (f (t:ℂ)).re = 0 ∧ deriv f (t:ℂ) = 2*Complex.I*((deriv θ t : ℝ) : ℂ) := by sorry

theorem tangent_normalization (n : ℕ) (hn : 80 ≤ n) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (ball (w₀:ℂ) R))
    (hstrip : ∀ z ∈ ball (w₀:ℂ) R, |(f z).re| < logBound n)
    (t : ℝ) (ht : t ∈ diameter) (hreal : (f (t:ℂ)).re = 0) :
    let F := normalizedLog n f t
    (∀ z ∈ ball (w₀:ℂ) R, |(F z).re| < Real.pi/4) ∧
    DifferentiableOn ℂ (Complex.tan ∘ F) (ball (w₀:ℂ) R) ∧
    MapsTo (Complex.tan ∘ F) (ball (w₀:ℂ) R) (ball 0 1) ∧
    (Complex.tan ∘ F) (t:ℂ) = 0 ∧ deriv (Complex.tan ∘ F) (t:ℂ) = deriv F (t:ℂ) := by sorry

theorem schwarz_pick_at_real (H : ℂ → ℂ) (hH : DifferentiableOn ℂ H (ball (w₀:ℂ) R))
    (hm : MapsTo H (ball (w₀:ℂ) R) (ball 0 1)) (t : ℝ) (ht : t ∈ diameter)
    (hzero : H (t:ℂ) = 0) : ‖deriv H (t:ℂ)‖ ≤ R/(R^2-(t-w₀)^2) := by sorry

theorem phase_derivative_bound (n : ℕ) (hn : 80 ≤ n) (p : Polynomial ℂ) (f : ℂ → ℂ)
    (hf : LogOn f (fun z => p.eval z / reflectedValue p z) (ball (w₀:ℂ) outerRadius))
    (hstrip : ∀ z ∈ ball (w₀:ℂ) R, |(f z).re| < logBound n)
    (θ : ℝ → ℝ) (hθ : PhaseOn θ p diameter) (t : ℝ) (ht : t ∈ diameter) :
    ‖deriv (normalizedLog n f t) (t:ℂ)‖ ≤ R/(R^2-(t-w₀)^2) ∧
    |deriv θ t| ≤ (2*logBound n/Real.pi)*R/(R^2-(t-w₀)^2) := by sorry

theorem consecutive_nodes (n : ℕ) (hn : 80 ≤ n) (hcenter : psi n (w₀:ℂ) ≠ 0) :
    ∃ s₁ s₂ : ℝ,
      IsGreatest {s : ℝ | s ∈ Icc (w₀-beta n) w₀ ∧ psi n (s:ℂ) = 0} s₁ ∧
      IsLeast {s : ℝ | s ∈ Icc w₀ (w₀+beta n) ∧ psi n (s:ℂ) = 0} s₂ ∧
      s₁ < w₀ ∧ w₀ < s₂ ∧ (∀ s ∈ Ioo s₁ s₂, psi n (s:ℂ) ≠ 0) ∧ s₂-s₁ < beta n := by sorry

theorem real_coefficient_zero (n : ℕ) (a s₁ s₂ : ℝ) (hs₁ : s₁ < w₀) (hs₂ : w₀ < s₂)
    (h₁ : psi n (s₁:ℂ) = 0) (h₂ : psi n (s₂:ℂ) = 0) :
    ∃ t ∈ Ioo s₁ s₂, (G n (a:ℂ)).eval (t:ℂ) = 0 := by sorry

theorem exact_phase_change (n : ℕ) (a : ℂ) (ha : a.im ≠ 0) (s₁ s₂ : ℝ)
    (hs₁ : s₁ < w₀) (hs₂ : w₀ < s₂) (h₁ : psi n (s₁:ℂ) = 0) (h₂ : psi n (s₂:ℂ) = 0)
    (hinterior : ∀ t ∈ Ioo s₁ s₂, psi n (t:ℂ) ≠ 0) :
    (∀ t ∈ Ioo s₁ s₂, ((G n a).eval (t:ℂ)).im = a.im * (psi n (t:ℂ)).re) ∧
    ((∀ t ∈ Ioo s₁ s₂, 0 < ((G n a).eval (t:ℂ)).im) ∨
     (∀ t ∈ Ioo s₁ s₂, ((G n a).eval (t:ℂ)).im < 0)) ∧
    (∃ θ : ℝ → ℝ, PhaseOn θ (G n a) (Icc s₁ s₂)) ∧
    ∀ θ : ℝ → ℝ, PhaseOn θ (G n a) (Icc s₁ s₂) → |θ s₂-θ s₁| = Real.pi := by sorry

theorem artanh_primitive :
    J 0 = 0 ∧ (∀ u ∈ Ioo (-R) R, HasDerivAt J (R/(R^2-u^2)) u) ∧
    ConvexOn ℝ (Ico 0 R) J ∧
    ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → u+v < R → J u + J v ≤ J (u+v) := by sorry

theorem integrated_obstruction (n : ℕ) (hn : 0 < n) (hβ : beta n < R)
    (θ : ℝ → ℝ) (s₁ s₂ : ℝ) (hs₁ : s₁ < w₀) (hs₂ : w₀ < s₂) (hgap : s₂-s₁ < beta n)
    (hθ : DifferentiableOn ℝ θ diameter)
    (hderiv : ∀ t ∈ Icc s₁ s₂, |deriv θ t| ≤ (2*logBound n/Real.pi)*R/(R^2-(t-w₀)^2))
    (hchange : |θ s₂-θ s₁| = Real.pi) :
    Real.pi ≤ (2*logBound n/Real.pi)*(J (w₀-s₁) + J (s₂-w₀)) ∧
    (2*logBound n/Real.pi)*(J (w₀-s₁) + J (s₂-w₀)) ≤ (2*logBound n/Real.pi)*J (beta n) ∧
    Real.pi^2 ≤ 2*logBound n*J (beta n) := by sorry

theorem threshold_components :
    0.382099 < beta 80/R ∧ beta 80/R < 0.382100 ∧
    8.8818 < logBound 80 ∧ logBound 80 < 8.88185 ∧
    0.402515 < J (beta 80) ∧ J (beta 80) < 0.40252 ∧
    2*logBound 80*J (beta 80) < 7.2 ∧ 9.8 < Real.pi^2 := by sorry

theorem uniform_monotonicity :
    StrictMonoOn (fun u : ℝ => Real.artanh u/u) (Ioo 0 1) ∧
    StrictAntiOn (fun x : ℝ => logBound x/Real.sqrt x) (Ici 80) ∧
    (∀ x ∈ Ici (80:ℝ), J (beta x) ≤ Real.sqrt (80/x)*J (beta 80)) ∧
    StrictAntiOn (fun x : ℝ => 2*logBound x*J (beta x)) (Ici 80) := by sorry

end Turan.TrinomialAE
