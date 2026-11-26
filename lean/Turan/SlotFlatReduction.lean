module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.SlotSuppression
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

@[expose] public section

noncomputable section
open Polynomial Filter Metric
open scoped Topology
namespace Turan

/-- Removing a diverging highest mode preserves escape from every fixed disk.
Its relative effect on the original polynomial tends to zero on compact sets. -/
theorem slot_delete_largest (n m : ℕ → ℕ) (c d a b : ℕ → ℂ)
    (hi : ∀ᶠ j in atTop, 2 ≤ n j ∧ n j < m j) (hm : Tendsto m atTop atTop)
    (F G : ℕ → Polynomial ℂ) (hF : ∀ j, F j = fourSlots (n j) (m j) (c j) (d j) (a j) (b j))
    (hG : ∀ j, G j = fourSlots (n j) (m j) (c j) (d j) (a j) 0)
    (he : escapesDisks F) :
    escapesDisks G ∧ TendstoLocallyUniformly (fun j z => (G j).eval z / (F j).eval z) (fun _ => 1) atTop := by
  have hdiff (j : ℕ) (z : ℂ) :
      (G j).eval z + b j*(hermite (m j)).eval z = (F j).eval z := by
    simp [hF j,hG j,fourSlots,eval_add,eval_mul]
  have bound (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
      ∀ᶠ j in atTop, ∀ z : ℂ, ‖z‖ ≤ K → ‖(G j).eval z/(F j).eval z-1‖ < ε := by
    obtain ⟨R, hR, M, hM⟩ := slot_suppression K ε hK hε
    filter_upwards [he R (hK.trans_lt hR),hi,tendsto_atTop.mp hm M] with j hfree hj hlarge
    have hbnd := hM (n j) (m j) hj.1 hj.2 hlarge (c j) (d j) (a j) (b j) (hF j ▸ hfree)
    rw [← hF j] at hbnd
    intro z hz
    have hn : (F j).eval z≠0 := hfree z (hz.trans hR.le)
    have heq : (G j).eval z/(F j).eval z-1 = -(b j*(hermite (m j)).eval z/(F j).eval z) := by
      field_simp [hn]
      linear_combination hdiff j z
    rw [heq,norm_neg]
    exact hbnd z hz
  constructor
  · intro R hR
    filter_upwards [bound R 1 hR.le one_pos] with j hj
    intro z hz heq
    have h := hj z hz
    simp [heq] at h
  · apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
    intro S hS
    obtain ⟨K,hK,hSK⟩ := hS.isBounded.subset_closedBall_lt 0 (0:ℂ)
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [bound K ε hK.le hε] with j hj
    intro z hz
    change dist 1 ((G j).eval z/(F j).eval z) < ε
    rw [dist_comm,dist_eq_norm]
    exact hj z (by simpa using mem_closedBall.mp (hSK hz))

end Turan
