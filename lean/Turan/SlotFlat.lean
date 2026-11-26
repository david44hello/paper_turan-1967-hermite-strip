module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.SlotFlatReduction
public import Turan.SlotFlatLift
public import Turan.SlotBounded
public import Turan.Degree

@[expose] public section

noncomputable section
open Polynomial Filter Metric
open scoped Topology
namespace Turan

theorem slot_flat_limit (n m : ℕ → ℕ) (c d a b : ℕ → ℂ)
    (hi : ∀ j, 2 ≤ n j ∧ n j < m j) (hm : Tendsto m atTop atTop)
    (hn : (∃ B : ℕ, ∀ᶠ j in atTop, n j ≤ B) ∨ Tendsto n atTop atTop)
    (F : ℕ → Polynomial ℂ) (hF : ∀ j, F j = fourSlots (n j) (m j) (c j) (d j) (a j) (b j))
    (he : escapesDisks F) :
    TendstoLocallyUniformly (fun j z => (F j).eval z / (F j).eval 0) (fun _ => 1) atTop := by
  let L (j : ℕ) := C (c j)*hermite 0 + C (d j)*hermite 1
  let G (j : ℕ) := L j + C (a j)*hermite (n j)
  have hG (j : ℕ) : G j = fourSlots (n j) (m j) (c j) (d j) (a j) 0 := by simp [G,L,fourSlots]
  obtain ⟨heG,hr⟩ := slot_delete_largest n m c d a b (Eventually.of_forall hi) hm F G hF hG he
  apply slot_flat_lift F G he heG hr
  have hLdeg (j : ℕ) : (L j).natDegree ≤ 1 := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact (natDegree_C_mul_le _ _).trans ((hermite_degree 0).1.le.trans (by decide))
    · exact (natDegree_C_mul_le _ _).trans (hermite_degree 1).1.le
  rcases hn with ⟨B,hB⟩ | hlarge
  · apply bounded_flat_limit G heG (max 1 B)
    filter_upwards [hB] with j hj
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact (hLdeg j).trans (le_max_left ..)
    · exact (natDegree_C_mul_le _ _).trans ((hermite_degree _).1.le.trans (hj.trans (le_max_right ..)))
  · have hg' (j : ℕ) : G j = fourSlots 2 (n j) (c j) (d j) 0 (a j) := by simp [fourSlots,G,L]
    have hl' (j : ℕ) : L j = fourSlots 2 (n j) (c j) (d j) 0 0 := by simp [fourSlots,L]
    have hindices : ∀ᶠ j in atTop, 2 ≤ (2:ℕ) ∧ 2 < n j := by
      filter_upwards [tendsto_atTop.mp hlarge 3] with j hj
      exact ⟨le_rfl,hj⟩
    obtain ⟨heL,hrL⟩ := slot_delete_largest (fun _ => 2) n c d (fun _ => 0) a
      hindices hlarge G L hg' hl' heG
    exact slot_flat_lift G L heG heL hrL (bounded_flat_limit L heL 1 (Eventually.of_forall hLdeg))

end Turan
