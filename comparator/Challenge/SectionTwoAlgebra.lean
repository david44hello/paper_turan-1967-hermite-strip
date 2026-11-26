module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.SlotDefs
public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section

noncomputable section
open Polynomial Filter Metric
open scoped Topology BigOperators Classical
namespace Turan.SectionTwo

variable {s : ℕ}

def slotSum (k : Fin s → ℕ) (a : Fin s → ℂ) : Polynomial ℂ :=
  ∑ v, C (a v) * hermite (k v)

def lambda (k : ℕ) : ℝ := 2 * (k : ℝ)
def topLambda (k : Fin s → ℕ) : ℝ := lambda (Finset.univ.sup k)
def frequency (k : Fin s → ℕ) : ℝ := Real.sqrt (topLambda k)

def scaledJet (ω : ℝ) (p : Polynomial ℂ) (l : ℕ) (z : ℂ) : ℂ :=
  ((derivative^[l]) p).eval z / (ω : ℂ)^l

def unitInitialJet (k : Fin s → ℕ) (p : Polynomial ℂ) : Prop :=
  (∀ l : Fin (2*s), ‖scaledJet (frequency k) p l 0‖ ≤ 1) ∧
    ∃ l : Fin (2*s), ‖scaledJet (frequency k) p l 0‖ = 1

def realFilter (μ : ℝ) (p : Polynomial ℂ) : Polynomial ℂ :=
  p + C (2 / (μ : ℂ)) * EStar p

def applyFilters (k : Fin s → ℕ) (V : Finset (Fin s)) (p : Polynomial ℂ) : Polynomial ℂ :=
  V.toList.foldr (fun v q => realFilter (lambda (k v)) q) p

def multiplier (k : Fin s → ℕ) (V : Finset (Fin s)) (v : Fin s) : ℝ :=
  ∏ t ∈ V, (1 - lambda (k v) / lambda (k t))

def scaledShift (L μ : ℝ) (p : Polynomial ℂ) : Polynomial ℂ :=
  C ((L : ℂ)⁻¹) * (2 * EStar p + C (μ : ℂ)*p)

def annihilator (k : Fin s → ℕ) (p : Polynomial ℂ) : Polynomial ℂ :=
  (List.finRange s).foldr (fun v q => scaledShift (topLambda k) (lambda (k v)) q) p

def odeArguments (k : Fin s → ℕ) (z : ℂ) : Fin (s+2) → ℂ :=
  Fin.cons (z / (frequency k : ℂ)) (Fin.cons ((topLambda k : ℂ)⁻¹)
    (fun v : Fin s => ((lambda (k v) / topLambda k : ℝ) : ℂ)))

theorem single_filter_action (μ : ℝ) (hμ : 0 < μ) (k : ℕ) :
    realFilter μ (hermite k) = C ((1 - lambda k / μ : ℝ) : ℂ) * hermite k ∧
    (realFilter μ (hermite k) = 0 ↔ lambda k = μ) := by sorry

theorem surviving_multipliers (k : ℕ → Fin s → ℕ) (γ : Fin s → ℝ)
    (hL : Tendsto (fun j => topLambda (k j)) atTop atTop)
    (hγ : ∀ v, Tendsto (fun j => lambda (k j v) / topLambda (k j)) atTop (𝓝 (γ v))) :
    let V := Finset.univ.filter (fun v => 0 < γ v)
    (∀ᶠ j in atTop, ∀ v, applyFilters (k j) V (hermite (k j v)) =
      C ((multiplier (k j) V v : ℝ) : ℂ) * hermite (k j v)) ∧
    (∀ v ∈ V, ∀ᶠ j in atTop, multiplier (k j) V v = 0) ∧
    (∀ v, γ v = 0 → Tendsto (fun j => multiplier (k j) V v) atTop (𝓝 1)) := by sorry

theorem select_escaping_polynomials (P : ℕ → Polynomial ℂ)
    (h : ∀ R : ℝ, 0 < R → ∃ i, ∀ z : ℂ, ‖z‖ < R → (P i).eval z ≠ 0) :
    ∃ i : ℕ → ℕ, (∀ (j : ℕ) (z : ℂ), ‖z‖ < (j : ℝ)+1 → (P (i j)).eval z ≠ 0) ∧
      escapesDisks (fun j => P (i j)) := by sorry

theorem select_active_slots (k : ℕ → Fin 4 → ℕ) (a : ℕ → Fin 4 → ℂ)
    (hpos : ∀ j, ∃ v, a j v ≠ 0 ∧ 0 < k j v) :
    ∃ (φ : ℕ → ℕ) (V : Finset (Fin 4)) (γ : Fin 4 → ℝ), StrictMono φ ∧
      (∀ j v, v ∈ V ↔ a (φ j) v ≠ 0) ∧
      (∀ v ∈ V, (∃ d, ∀ j, k (φ j) v = d) ∨ Tendsto (fun j => k (φ j) v) atTop atTop) ∧
      ∀ v ∈ V, γ v ∈ Set.Icc 0 1 ∧
        Tendsto (fun j => lambda (k (φ j) v) / lambda (V.sup (k (φ j)))) atTop (𝓝 (γ v)) := by sorry

theorem scaled_commutations (ω : ℝ) (hω : 0 < ω) (μ ν : ℝ) (p : Polynomial ℂ) :
    let D := fun q : Polynomial ℂ => C (ω : ℂ)⁻¹ * q.derivative
    let b := C (-2/(ω : ℂ)) * X
    D (b*p) = b*D p + C (-2/(ω : ℂ)^2)*p ∧
    scaledShift (ω^2) μ (scaledShift (ω^2) ν p) =
      scaledShift (ω^2) ν (scaledShift (ω^2) μ p) := by sorry

theorem scaled_annihilator_normal_form (s : ℕ) (hs : s ∈ Set.Icc 2 4) :
    ∃ P : Fin (2*s) → MvPolynomial (Fin (s+2)) ℂ,
      (∀ (k : Fin s → ℕ), 1 ≤ topLambda k → ∀ (p : Polynomial ℂ) (z : ℂ),
        (annihilator k p).eval z = scaledJet (frequency k) p (2*s) z +
          ∑ l, MvPolynomial.eval (odeArguments k z) (P l) * scaledJet (frequency k) p l z) ∧
      (∀ R : ℝ, 0 ≤ R → ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (k : Fin s → ℕ), 1 ≤ topLambda k →
        ∀ z : ℂ, ‖z‖ ≤ R → ∀ l, ‖MvPolynomial.eval (odeArguments k z) (P l)‖ ≤ C₀) ∧
      ∀ (k : Fin s → ℕ) (a : Fin s → ℂ), annihilator k (slotSum k a) = 0 := by sorry

theorem normalize_initial_jet (hs : s ∈ Set.Icc 2 4) (k : Fin s → ℕ)
    (hL : 1 ≤ topLambda k) (a : Fin s → ℂ) (hp : slotSum k a ≠ 0) :
    ∃ t : ℂ, t ≠ 0 ∧ unitInitialJet k (C t * slotSum k a) := by sorry

theorem scaled_jet_system (s : ℕ) (hs : s ∈ Set.Icc 2 4) :
    ∃ A : (Fin s → ℕ) → Fin (2*s) → Fin (2*s) → Polynomial ℂ,
      (∀ (k : Fin s → ℕ), 1 ≤ topLambda k → ∀ (a : Fin s → ℂ) (l : Fin (2*s)) (z : ℂ),
        deriv (scaledJet (frequency k) (slotSum k a) l) z =
          ∑ t : Fin (2*s), (A k l t).eval z * scaledJet (frequency k) (slotSum k a) t z) ∧
      ∀ R : ℝ, 0 ≤ R → ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (k : Fin s → ℕ), 1 ≤ topLambda k →
        ∀ z : ℂ, ‖z‖ ≤ R → ∀ l t, ‖(A k l t).eval z‖ ≤ C₀ * frequency k := by sorry

theorem normalized_growth (s : ℕ) (hs : s ∈ Set.Icc 2 4) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (k : Fin s → ℕ) (a : Fin s → ℂ), 1 ≤ topLambda k →
      unitInitialJet k (slotSum k a) →
      (∀ z : ℂ, ‖z‖ ≤ R → ‖(slotSum k a).eval z‖ ≤ Real.exp (C₀ * frequency k)) ∧
      ∃ z : ℂ, ‖z‖ ≤ 1 ∧ 1 / (((2*s-1).factorial : ℕ) : ℝ) ≤ ‖(slotSum k a).eval z‖ := by sorry

def projectSlot (k : Fin s → ℕ) (v : Fin s) (p : Polynomial ℂ) : Polynomial ℂ :=
  (Finset.univ.erase v).toList.foldr (fun t q =>
    C (((lambda (k t) - lambda (k v) : ℝ) : ℂ)⁻¹) *
      (2 * EStar q + C (lambda (k t) : ℂ) * q)) p

theorem project_slot_estimate (s : ℕ) (hs : s ∈ Set.Icc 2 4) (z : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (k : Fin s → ℕ), Function.Injective k →
      ∀ (a : Fin s → ℂ) (v : Fin s),
      projectSlot k v (slotSum k a) = C (a v) * hermite (k v) ∧
      (∀ t, t ≠ v → 2 ≤ |lambda (k t) - lambda (k v)|) ∧
      ∀ M : ℝ, 0 ≤ M → (∀ w ∈ closedBall z ε, ‖(slotSum k a).eval w‖ ≤ M) →
        ‖(projectSlot k v (slotSum k a)).eval z‖ ≤ C₀ * (1 + topLambda k)^(s-1) * M := by sorry

end Turan.SectionTwo
