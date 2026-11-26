module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.NodeDefs

@[expose] public section

noncomputable section
namespace Turan

open Filter
open scoped Topology

/-- The contacts in the original z coordinate, counted with polynomial multiplicity. -/
def quarticBoundaryRoots (a b : ℂ) (y : ℝ) : Multiset ℂ :=
  (family 2 4 a b).roots.filter (fun z => |z.im| = y)

/-- Vertical displacement in the z coordinate, before the shift to w. -/
def quarticVerticalMove (ε : ℝ) (z : ℂ) : ℂ :=
  z + Complex.I * ((ε * (z.im / |z.im|) : ℝ) : ℂ)

/-- The value and tangency equations prescribed by the old boundary multiset. -/
def quarticMovedRows (M : Multiset ℂ) (ε : ℝ) (a b : ℂ) : Prop :=
  ∀ z ∈ M, let w := quarticVerticalMove ε z + 1/2
           a * nodeMode 2 w + b * nodeMode 4 w = -2 ∧
             (2 ≤ M.count z → a * deriv (nodeMode 2) w + b * deriv (nodeMode 4) w = 0)

#print axioms quarticBoundaryRoots
#print axioms quarticVerticalMove
#print axioms quarticMovedRows

end Turan
