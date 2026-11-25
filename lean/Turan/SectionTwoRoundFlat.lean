-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.SectionTwoAlgebraDefs
import Turan.SlotFlat

noncomputable section
open Polynomial Filter
open scoped Topology BigOperators
namespace Turan.SectionTwo

/-- Sort the two higher modes together with their coefficients at each index. -/
private theorem flat_of_unsorted_slots (p r : ℕ → ℕ) (c d a b : ℕ → ℂ)
    (hi : ∀ j, 2 ≤ p j ∧ 2 ≤ r j ∧ p j ≠ r j)
    (hp : Tendsto p atTop atTop)
    (hr : (∃ k, ∀ j, r j = k) ∨ Tendsto r atTop atTop)
    (F : ℕ → Polynomial ℂ) (hF : ∀ j, F j = fourSlots (p j) (r j) (c j) (d j) (a j) (b j))
    (he : escapesDisks F) :
    TendstoLocallyUniformly (fun j z => (F j).eval z / (F j).eval 0) (fun _ => 1) atTop := by
  apply slot_flat_limit (fun j => min (p j) (r j)) (fun j => max (p j) (r j)) c d
    (fun j => if p j ≤ r j then a j else b j) (fun j => if p j ≤ r j then b j else a j)
    _ _ _ F _ he
  · intro j
    obtain ⟨hpj, hrj, hne⟩ := hi j
    omega
  · exact tendsto_atTop_mono (fun j => le_max_left (p j) (r j)) hp
  · rcases hr with ⟨k, hk⟩ | hr
    · exact Or.inl ⟨k, Eventually.of_forall fun j => hk j ▸ min_le_right (p j) (r j)⟩
    · right
      apply tendsto_atTop.mpr
      intro k
      filter_upwards [hp.eventually_ge_atTop k, hr.eventually_ge_atTop k] with j hpj hrj
      exact le_min hpj hrj
  · intro j
    rw [hF j]
    by_cases h : p j ≤ r j
    · simp [h]
    · have h' := le_of_not_ge h
      simp [h, min_eq_right h', max_eq_left h', fourSlots, add_right_comm]

/-- At most four stable slots, including modes zero and one, are flat when their zeros escape. -/
theorem escaping_slot_sum_flat {s : ℕ} (hs : s ∈ Set.Icc 2 4) (q : ℕ → Fin s → ℕ)
    (hq : ∀ j, Function.Injective (q j)) (v₀ v₁ : Fin s)
    (h₀ : ∀ j, q j v₀ = 0) (h₁ : ∀ j, q j v₁ = 1)
    (hstable : ∀ v, (∃ d, ∀ j, q j v = d) ∨ Tendsto (fun j => q j v) atTop atTop)
    (a : ℕ → Fin s → ℂ) (he : escapesDisks (fun j => slotSum (q j) (a j))) :
    TendstoLocallyUniformly (fun j z => (slotSum (q j) (a j)).eval z /
      (slotSum (q j) (a j)).eval 0) (fun _ => 1) atTop := by
  classical
  by_cases hall : ∀ v, ∃ d, ∀ j, q j v = d
  · apply bounded_flat_limit _ he (Finset.univ.sup (q 0))
    apply Eventually.of_forall
    intro j
    apply natDegree_sum_le_of_forall_le
    intro v hv
    obtain ⟨k, hk⟩ := hall v
    have hqj : q j v = q 0 v := (hk j).trans (hk 0).symm
    exact (natDegree_C_mul_le _ _).trans <| (hermite_degree _).1.le.trans <|
      hqj ▸ Finset.le_sup (f := q 0) hv
  obtain ⟨x, hnc⟩ := Classical.not_forall.mp hall
  have hx := (hstable x).resolve_left hnc
  have hx₀ : x ≠ v₀ := fun h => hnc ⟨0, h ▸ h₀⟩
  have hx₁ : x ≠ v₁ := fun h => hnc ⟨1, h ▸ h₁⟩
  have h₁₀ : v₁ ≠ v₀ := by
    intro h
    have h' := h₁ 0
    rw [h, h₀] at h'
    contradiction
  have hhigh (j : ℕ) (y : Fin s) (hy₀ : y ≠ v₀) (hy₁ : y ≠ v₁) : 2 ≤ q j y := by
    have hn₀ := (hq j).ne hy₀
    have hn₁ := (hq j).ne hy₁
    rw [h₀] at hn₀
    rw [h₁] at hn₁
    omega
  let S₀ := Finset.univ.erase v₀
  let S₁ := S₀.erase v₁
  let R := S₁.erase x
  have hv₁ : v₁ ∈ S₀ := by simp [S₀, h₁₀]
  have hxS : x ∈ S₁ := by simp [S₁, S₀, hx₀, hx₁]
  have hcard : R.card ≤ 1 := by
    dsimp only [R, S₁, S₀]
    rw [Finset.card_erase_of_mem hxS, Finset.card_erase_of_mem hv₁,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have := hs.2
    omega
  let term (j : ℕ) (v : Fin s) := C (a j v) * hermite (q j v)
  have hsum (j : ℕ) : slotSum (q j) (a j) =
      C (a j v₀) * hermite 0 + C (a j v₁) * hermite 1 + term j x + ∑ v ∈ R, term j v := by
    change ∑ v, term j v = _
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v₀),
      ← Finset.sum_erase_add _ _ hv₁, ← Finset.sum_erase_add _ _ hxS]
    simp only [term, h₀, h₁, R, S₁, S₀]
    ac_rfl
  by_cases hR : R = ∅
  · apply flat_of_unsorted_slots (fun j => q j x) (fun j => q j x + 1)
      (fun j => a j v₀) (fun j => a j v₁) (fun j => a j x) (fun _ => 0) _ hx _ _ _ he
    · intro j
      have := hhigh j x hx₀ hx₁
      omega
    · exact Or.inr (tendsto_atTop_mono (fun j => Nat.le_succ (q j x)) hx)
    · intro j
      simp [hsum j, hR, term, fourSlots]
  · have hcard' : R.card = 1 := by
      have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hR)
      omega
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcard'
    have hyR : y ∈ R := hy ▸ Finset.mem_singleton_self _
    obtain ⟨hyx, hy₁, hy₀⟩ : y ≠ x ∧ y ≠ v₁ ∧ y ≠ v₀ := by
      simpa [R, S₁, S₀] using hyR
    apply flat_of_unsorted_slots (fun j => q j x) (fun j => q j y)
      (fun j => a j v₀) (fun j => a j v₁) (fun j => a j x) (fun j => a j y)
      _ hx (hstable y) _ _ he
    · exact fun j => ⟨hhigh j x hx₀ hx₁, hhigh j y hy₀ hy₁, (hq j).ne hyx.symm⟩
    · intro j
      simp [hsum j, hy, term, fourSlots]

end Turan.SectionTwo
