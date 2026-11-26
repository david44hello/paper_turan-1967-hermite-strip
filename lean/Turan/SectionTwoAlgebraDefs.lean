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

def projectSlot (k : Fin s → ℕ) (v : Fin s) (p : Polynomial ℂ) : Polynomial ℂ :=
  (Finset.univ.erase v).toList.foldr (fun t q =>
    C (((lambda (k t) - lambda (k v) : ℝ) : ℂ)⁻¹) *
      (2 * EStar q + C (lambda (k t) : ℂ) * q)) p

end Turan.SectionTwo
