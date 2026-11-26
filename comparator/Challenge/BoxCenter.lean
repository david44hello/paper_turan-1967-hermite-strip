module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs

@[expose] public section
open Polynomial Set
namespace Turan

theorem box_center_edge_chord {α : Type*} (K : Set α) (x : α) (hx : x ∈ K)
    (p : α → Polynomial ℂ) (u v c : ℂ)
    (hbox : ∀ a ∈ K, ∀ t ∈ Icc (0:ℝ) 1, ‖(p a).eval ((1-t) • u + t • v)-c‖ < ‖c‖) :
    let A := (p x).eval u
    let B := (p x).eval v
    ‖A-c‖ < ‖c‖ ∧ ‖B-c‖ < ‖c‖ ∧
      ∀ t ∈ Icc (0:ℝ) 1, ‖(1-t) • A + t • B - c‖ < ‖c‖ := by sorry

end Turan
