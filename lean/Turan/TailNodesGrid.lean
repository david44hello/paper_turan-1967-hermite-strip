-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.TailDefs
import Mathlib.Tactic

noncomputable section
namespace Turan

/-- Anchor the grid at the last node before the center. Each open cell to the right
contains a node beyond the center. On the left the zeroth node is the anchor itself. -/
theorem node_pairs_of_occupied_cells (S : Finset ℝ) (w η : ℝ) (N : ℕ)
    (hη : 0 < η) (hη3 : η ≤ 3) (hN : (N : ℝ)*η ≤ 3) (hw : w ∉ S)
    (cell : ∀ a : ℝ, w-3 ≤ a → a+η ≤ w+3 →
      ∃ t ∈ Set.Ioo a (a+η), t ∈ S) :
    ∃ d e : Fin N → ℝ, Function.Injective d ∧ Function.Injective e ∧
      ∀ i, 0 < d i ∧ 0 < e i ∧ w+d i ∈ S ∧ w-e i ∈ S ∧
        d i+e i ≤ (2*(i.val:ℝ)+1)*η := by
  classical
  obtain ⟨p, ⟨hp, hp'⟩, hSp⟩ := cell (w-η) (by linarith) (by linarith)
  let L := S.filter (· < w)
  have hpL : p ∈ L := Finset.mem_filter.mpr ⟨hSp, by linarith⟩
  let q := L.max' ⟨p, hpL⟩
  have hqL : q ∈ L := L.max'_mem _
  obtain ⟨hqS, hqw⟩ := Finset.mem_filter.mp hqL
  have hpq : p ≤ q := L.le_max' _ hpL
  have after_q {x : ℝ} (hx : x ∈ S) (hqx : q < x) : w < x := by
    rcases lt_trichotomy x w with h | rfl | h
    · exact (hqx.not_ge (L.le_max' x (Finset.mem_filter.mpr ⟨hx, h⟩))).elim
    · exact (hw hx).elim
    · exact h
  have bound (i : Fin N) : ((i.val:ℝ)+1)*η ≤ 3 := by
    have hi : (i.val:ℝ)+1 ≤ N := by exact_mod_cast i.isLt
    exact (mul_le_mul_of_nonneg_right hi hη.le).trans hN
  have right (i : Fin N) : ∃ r ∈ S, w < r ∧ q+(i.val:ℝ)*η < r ∧
      r < q+((i.val:ℝ)+1)*η := by
    have hi : 0 ≤ (i.val:ℝ)*η := by positivity
    obtain ⟨r, ⟨ha, hb⟩, hr⟩ := cell (q+(i.val:ℝ)*η)
      (by linarith) (by linarith only [hqw, bound i])
    exact ⟨r, hr, after_q hr (by linarith), ha, by linarith⟩
  have left (i : Fin N) : ∃ l ∈ S, l < w ∧ q-(i.val:ℝ)*η ≤ l ∧
      l < q-(i.val:ℝ)*η+η := by
    by_cases hi : i.val = 0
    · exact ⟨q, hqS, hqw, by simp [hi], by simpa [hi] using hη⟩
    have h1 : (1:ℝ) ≤ i.val := by exact_mod_cast (show 1 ≤ i.val by omega)
    have hηi : η ≤ (i.val:ℝ)*η := by simpa using mul_le_mul_of_nonneg_right h1 hη.le
    obtain ⟨l, ⟨ha, hb⟩, hl⟩ := cell (q-(i.val:ℝ)*η)
      (by linarith only [hp, hpq, bound i]) (by linarith)
    exact ⟨l, hl, by linarith, ha.le, hb⟩
  choose r hrS hrw hra hrb using right
  choose l hlS hlw hla hlb using left
  have jump {i k : Fin N} (h : i < k) : ((i.val:ℝ)+1)*η ≤ (k.val:ℝ)*η :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast h : (i.val:ℝ)+1 ≤ k.val) hη.le
  refine ⟨fun i => r i-w, fun i => w-l i, StrictMono.injective ?_, StrictMono.injective ?_, ?_⟩
  · intro i k hik
    dsimp
    linarith only [hrb i, hra k, jump hik]
  · intro i k hik
    dsimp
    linarith only [hla i, hlb k, jump hik]
  · intro i
    dsimp
    exact ⟨sub_pos.mpr (hrw i), sub_pos.mpr (hlw i), by simpa using hrS i,
      by simpa using hlS i, by linarith only [hrb i, hla i]⟩

end Turan
