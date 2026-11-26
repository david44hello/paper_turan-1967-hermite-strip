module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.DeltaDefs
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Polynomial Filter Set Metric
open scoped Topology
namespace Turan

def contactPencilPoly (d : ℝ) : Polynomial ℂ :=
  (2*X+C (d:ℂ))^2*(4*X^2+4*X+2) - (4*X^4-4*X^2+3)

theorem quartic_contact_square_alternatives (w d : ℂ) :
    (2*w+d)^2=4*w^2 ↔ d=0 ∨ d= -4*w := by sorry

/-- The threshold-line argument starts at a pencil root, including d=0. -/
theorem quartic_pencil_line_identification (w : ℂ)
    (hw : 0<w.im ∧ 12*w^4+16*w^3+12*w^2-3=0) (s d : ℝ)
    (hz : (contactPencilPoly d).eval (⟨s-1/2,w.im⟩ : ℂ)=0) :
    (⟨s-1/2,w.im⟩ : ℂ)=w ∧ d=0 := by sorry

/-- A constant-degree pencil with no zero on the boundary line along a parameter
interval has constant root count above the line, with multiplicity. -/
theorem quartic_pencil_count_on_interval (h u v : ℝ) (huv : u ≤ v)
    (hboundary : ∀ d ∈ Icc u v, ∀ z : ℂ, z.im=h → (contactPencilPoly d).eval z ≠ 0) :
    ((contactPencilPoly u).roots.filter (fun z => h<z.im)).card =
      ((contactPencilPoly v).roots.filter (fun z => h<z.im)).card := by sorry

theorem quartic_pencil_large_parameter_limits :
    TendstoLocallyUniformly (fun (d : ℝ) (z : ℂ) => (contactPencilPoly d).eval z / (d:ℂ)^2)
      quarticDen (comap (fun d : ℝ => |d|) atTop) ∧
    TendstoLocallyUniformly (fun (d : ℝ) (t : ℂ) => (contactPencilPoly d).eval ((d:ℂ)*t)/(d:ℂ)^4)
      (fun t => 4*t^2*(3*t+1)*(t+1)) (comap (fun d : ℝ => |d|) atTop) := by sorry

/-- The fixed and rescaled disks separate the four roots. In the rescaled
coordinates a conjugation-invariant disk with a single root forces reality. -/
theorem quartic_pencil_large_parameter_roots (r : ℝ) (hr₀ : 0<r) (hr₁ : r<1/6) :
    ∀ᶠ d : ℝ in comap (fun u : ℝ => |u|) atTop,
      let roots := (contactPencilPoly d).roots
      let nearUpper := fun z : ℂ => ‖z-(-1/2+Complex.I/2)‖ < r
      let nearLower := fun z : ℂ => ‖z-(-1/2-Complex.I/2)‖ < r
      let g₁ := fun z : ℂ => ‖z/(d:ℂ)+1‖ < r
      let g₂ := fun z : ℂ => ‖z/(d:ℂ)+1/3‖ < r
      (roots.filter nearUpper).card=1 ∧ (roots.filter nearLower).card=1 ∧
      (roots.filter g₁).card=1 ∧ (roots.filter g₂).card=1 ∧
      (∀ z ∈ roots, nearUpper z ∨ nearLower z ∨ g₁ z ∨ g₂ z) ∧
      (∀ z ∈ roots, g₁ z ∨ g₂ z → z.im=0) := by sorry

end Turan
