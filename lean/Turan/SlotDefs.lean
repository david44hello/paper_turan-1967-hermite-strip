module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.RouteDefs
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

@[expose] public section

noncomputable section
open Polynomial Filter
namespace Turan

def fourSlots (n m : ℕ) (c d a b : ℂ) : Polynomial ℂ :=
  C c*hermite 0 + C d*hermite 1 + C a*hermite n + C b*hermite m

def escapesDisks (F : ℕ → Polynomial ℂ) : Prop :=
  ∀ R : ℝ, 0 < R → ∀ᶠ j in atTop, ∀ z : ℂ, ‖z‖ ≤ R → (F j).eval z ≠ 0

def removeMode (k : ℕ) (p : Polynomial ℂ) : Polynomial ℂ :=
  p + C (k : ℂ)⁻¹*EStar p

def slotFilter (n m : ℕ) (γ : ℝ) (p : Polynomial ℂ) : Polynomial ℂ :=
  if 0 < γ then removeMode n (removeMode m p) else removeMode m p

end Turan
