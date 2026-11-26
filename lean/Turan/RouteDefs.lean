module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.WindingDefs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

noncomputable section
open Polynomial
namespace Turan

def intervalAngle (l r : ℝ) (z : ℂ) : ℝ :=
  ∫ t in l..r, z.im / ((t-z.re)^2+z.im^2)

def UniformTransferCheck : Prop :=
  ∀ n : ℕ, 2 ≤ n → n ≤ 7 → ∀ (swap : Bool) (θ : ℂ),
    |θ.re| ≤ 1 → 0 ≤ θ.im → θ.im ≤ 1 →
    ∃ (w : ℂ) (r : ℝ) (k : ℕ), 0 < r ∧ 1 ≤ k ∧ ‖w‖+r ≤ 5/4 ∧ |w.im|+r < 87/100 ∧
      1/64 < coefficientMargin (diskExpansion (transferPencil n swap θ) w r) k

def EStar (p : Polynomial ℂ) : Polynomial ℂ := C (1/2)*p.derivative.derivative-X*p.derivative

def projectedRatio (n m j' : ℕ) (z : ℂ) : ℂ :=
  (1+2*(1-1/(j':ℂ))*z)/(1+2*(1-1/(n:ℂ))*(1-1/(m:ℂ))*z)

end Turan
