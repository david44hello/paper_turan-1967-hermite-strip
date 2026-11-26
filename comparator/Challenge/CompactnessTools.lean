module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs
public import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

@[expose] public section
open Metric Filter
open scoped Topology
namespace Turan

theorem harnack_disk (f : ℂ → ℝ) (c z : ℂ) (R : ℝ)
    (hf : InnerProductSpace.HarmonicContOnCl f (ball c R))
    (hn : ∀ w ∈ sphere c R, 0 ≤ f w) (hz : z ∈ ball c R) :
    (R-‖z-c‖)/(R+‖z-c‖)*f c ≤ f z ∧ f z ≤ (R+‖z-c‖)/(R-‖z-c‖)*f c := by sorry

theorem zeros_persist_locally (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hF : ∀ j, Differentiable ℂ (F j)) (hf : Differentiable ℂ f)
    (hconv : TendstoLocallyUniformly F f atTop) (hn : f ≠ 0) (c : ℂ) (hc : f c = 0)
    (r : ℝ) (hr : 0 < r) :
    ∀ᶠ j in atTop, ∃ z ∈ ball c r, F j z = 0 := by sorry

end Turan
