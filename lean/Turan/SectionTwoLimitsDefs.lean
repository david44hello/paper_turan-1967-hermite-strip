-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.SectionTwoAlgebraDefs
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

noncomputable section
open Polynomial Filter Metric InnerProductSpace
open scoped Topology BigOperators ComplexConjugate Classical
namespace Turan.SectionTwo

variable {s : ℕ}

def scaledLog (ω : ℝ) (p : Polynomial ℂ) (z : ℂ) : ℝ :=
  Real.log ‖p.eval z‖ / ω

def complexGradient (u : ℂ → ℝ) (z : ℂ) : ℂ :=
  ((fderiv ℝ u z 1 : ℝ) : ℂ) - Complex.I * ((fderiv ℝ u z Complex.I : ℝ) : ℂ)

def jetRatio (ω : ℝ) (p : Polynomial ℂ) (l : ℕ) (z : ℂ) : ℂ :=
  scaledJet ω p l z / p.eval z

def removalRound (k : ℕ → Fin s → ℕ) (active removed : Finset (Fin s)) : Prop :=
  removed ⊆ active ∧
    ((removed = ∅ ∧ ∀ v ∈ active, ∃ d, ∀ j, k j v = d) ∨
     (removed.Nonempty ∧ Tendsto (fun j => active.sup (k j)) atTop atTop ∧
       ∃ γ : Fin s → ℝ, ∀ v ∈ active,
         Tendsto (fun j => lambda (k j v) / lambda (active.sup (k j))) atTop (𝓝 (γ v)) ∧
         (v ∈ removed ↔ 0 < γ v)))

end Turan.SectionTwo
