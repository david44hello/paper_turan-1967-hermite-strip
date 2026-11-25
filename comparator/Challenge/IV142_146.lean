-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.NodeDefs

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

-- 142, lines 1708–1712
theorem quartic_contact_equations {a b z : ℂ} (hz : z.im ≠ 0)
    (hroot : (family 2 4 a b).eval z = 0) :
    let w := z + 1/2
    a * nodeMode 2 w + b * nodeMode 4 w = -2 ∧
      (2 ≤ (family 2 4 a b).rootMultiplicity z →
        a * deriv (nodeMode 2) w + b * deriv (nodeMode 4) w = 0) := sorry

theorem quartic_contact_mode_derivatives {w : ℂ} (hw : w ≠ 0) :
    HasDerivAt (nodeMode 2) (4 + 1/w^2) w ∧
    HasDerivAt (nodeMode 4) (48*w^2 - 64*w - 24 - 1/w^2) w := sorry

-- 143, lines 1712–1718
theorem quartic_single_contact_row {a b z : ℂ} (hz : z.im ≠ 0)
    (hroot : (family 2 4 a b).eval z = 0) :
    let w := z + 1/2
    nodeMode 2 w ≠ 0 ∨ nodeMode 4 w ≠ 0 := sorry

theorem quartic_vertical_interpolation (a b : ℂ) (y : ℝ) (hy : 0 < y)
    (hfew : (quarticBoundaryRoots a b y).card ≤ 2) :
    let M := quarticBoundaryRoots a b y
    ∃ (A B : ℝ → ℂ) (η : ℝ), 0 < η ∧ A 0 = a ∧ B 0 = b ∧
      ContinuousOn A (Set.Ico 0 η) ∧ ContinuousOn B (Set.Ico 0 η) ∧
      (∀ ε ∈ Set.Ico 0 η, quarticMovedRows M ε (A ε) (B ε)) ∧
      (∀ z : ℂ, M = {z} →
        if nodeMode 2 (z + 1/2) ≠ 0 then ∀ ε ∈ Set.Ico 0 η, B ε = b
        else ∀ ε ∈ Set.Ico 0 η, A ε = a) := sorry

-- 144, lines 1718–1722. Here u and v are shifted roots (w coordinates).
theorem quartic_dependent_value_rows {a b u v : ℂ}
    (hu : a * nodeMode 2 u + b * nodeMode 4 u = -2)
    (hv : a * nodeMode 2 v + b * nodeMode 4 v = -2)
    (hdet : nodeMode 2 u * nodeMode 4 v - nodeMode 4 u * nodeMode 2 v = 0) :
    nodeMode 2 u = nodeMode 2 v ∧ nodeMode 4 u = nodeMode 4 v := sorry

theorem quartic_equal_row_nodes_real {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (h₂ : nodeMode 2 u = nodeMode 2 v) (h₄ : nodeMode 4 u = nodeMode 4 v) :
    let S := u + v
    divided (nodeMode 2) u v = 0 ∧ divided (nodeMode 4) u v = 0 ∧
      u*v = -1/4 ∧ S^2 - 2*S - 1 = 0 ∧ S.im = 0 ∧ u.im = 0 ∧ v.im = 0 := sorry

theorem quartic_distinct_contact_rows {a b z₁ z₂ : ℂ} (hne : z₁ ≠ z₂)
    (h₁ : z₁.im ≠ 0) (h₂ : z₂.im ≠ 0)
    (hr₁ : (family 2 4 a b).eval z₁ = 0) (hr₂ : (family 2 4 a b).eval z₂ = 0) :
    let u := z₁ + 1/2
    let v := z₂ + 1/2
    nodeMode 2 u * nodeMode 4 v - nodeMode 4 u * nodeMode 2 v ≠ 0 := sorry

-- 145, lines 1722–1726
/-- Apply to the derivative row at a multiple root using its zero pairing from ID 142. -/
theorem quartic_dependent_tangent_row {a b w t₂ t₄ : ℂ}
    (hval : a * nodeMode 2 w + b * nodeMode 4 w = -2)
    (htan : a*t₂ + b*t₄ = 0)
    (hdet : nodeMode 2 w * t₄ - nodeMode 4 w * t₂ = 0) :
    t₂ = 0 ∧ t₄ = 0 := sorry

theorem quartic_contact_critical_arithmetic {w : ℂ} (hw : w ≠ 0)
    (h₂ : deriv (nodeMode 2) w = 0) :
    w^2 = -1/4 ∧ deriv (nodeMode 4) w = -32 - 64*w ∧
      (deriv (nodeMode 4) w = 0 → w = -1/2) ∧ deriv (nodeMode 4) w ≠ 0 := sorry

theorem quartic_double_contact_rows {a b z : ℂ} (hz : z.im ≠ 0)
    (hm : 2 ≤ (family 2 4 a b).rootMultiplicity z) :
    let w := z + 1/2
    nodeMode 2 w * deriv (nodeMode 4) w - nodeMode 4 w * deriv (nodeMode 2) w ≠ 0 := sorry

-- 146, lines 1726–1730. The matching counts every old and new residual root.
theorem quartic_vertical_persistence (a b : ℂ) (hb : b ≠ 0) (y : ℝ) (hy : 0 < y)
    (hlow : ∀ z : ℂ, (family 2 4 a b).eval z = 0 → y ≤ |z.im|)
    (hfew : (quarticBoundaryRoots a b y).card ≤ 2) (A B : ℝ → ℂ)
    (hA : Tendsto A (𝓝[>] (0 : ℝ)) (𝓝 a)) (hB : Tendsto B (𝓝[>] (0 : ℝ)) (𝓝 b))
    (hrows : ∀ᶠ ε in 𝓝[>] (0 : ℝ), quarticMovedRows (quarticBoundaryRoots a b y) ε (A ε) (B ε)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      let F := family 2 4 (A ε) (B ε)
      let moved := (quarticBoundaryRoots a b y).map (quarticVerticalMove ε)
      let oldRest := (family 2 4 a b).roots.filter (fun z => y < |z.im|)
      F.natDegree = 4 ∧ quarticBoundaryRoots (A ε) (B ε) (y + ε) = moved ∧
        (∃ R : Multiset ℂ, F.roots = moved + R ∧
          Multiset.Rel (fun z z' : ℂ => dist z z' < δ) oldRest R ∧
          ∀ z ∈ R, y + ε < |z.im|) ∧
        (∀ z : ℂ, F.eval z = 0 → y < |z.im|) := sorry

end Turan
