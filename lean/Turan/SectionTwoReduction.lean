-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.SectionTwoRoundSelection
import Turan.SectionTwoRoundLimits
import Turan.SectionTwoRoundAlgebra
import Turan.SectionTwoRoundFlat
import Turan.SectionTwoFilterEscape

noncomputable section
open Polynomial Filter Metric
open scoped Topology BigOperators
namespace Turan.SectionTwo

variable {s : ℕ}

private theorem keeps_constant {q : ℕ → Fin s → ℕ} {V A : Finset (Fin s)}
    (hr : removalRound q V A) {v : Fin s} {d : ℕ} (hv : ∀ j, q j v = d) : v ∉ A := by
  intro hrem
  have ht := (removal_index_tendsto hr hrem).eventually_gt_atTop d
  obtain ⟨j,hj⟩ := ht.exists
  simp only [hv,lt_self_iff_false] at hj

private theorem constant_of_empty {q : ℕ → Fin s → ℕ} {V A : Finset (Fin s)}
    (hr : removalRound q V A) (hempty : A = ∅) :
    ∀ v ∈ V, ∃ d, ∀ j, q j v = d := by
  rcases hr.2 with ⟨_,h⟩ | ⟨hne,_,_⟩
  · exact h
  · exact False.elim (hne.ne_empty hempty)

/-- Two nonempty rounds remove both possible slots above degrees zero and one. -/
private theorem constant_after_two (hs : s ≤ 4) {q : ℕ → Fin s → ℕ}
    {A B : Finset (Fin s)} (hrA : removalRound q Finset.univ A)
    (hrB : removalRound q (Finset.univ \ A) B) {v₀ v₁ : Fin s}
    (h₀ : ∀ j, q j v₀ = 0) (h₁ : ∀ j, q j v₁ = 1)
    (hv₀ : v₀ ∈ (Finset.univ \ A) \ B) (hv₁ : v₁ ∈ (Finset.univ \ A) \ B) :
    ∀ v ∈ (Finset.univ \ A) \ B, ∃ d, ∀ j, q j v = d := by
  by_cases ha : A = ∅
  · exact fun v _ => constant_of_empty hrA ha v (Finset.mem_univ _)
  by_cases hb : B = ∅
  · exact fun v hv => constant_of_empty hrB hb v (Finset.mem_sdiff.mp hv).1
  have hne : v₀ ≠ v₁ := by
    rintro rfl
    have he := (h₀ 0).symm.trans (h₁ 0)
    contradiction
  let keep := (Finset.univ \ A) \ B
  have hpair : ({v₀,v₁} : Finset (Fin s)) ⊆ keep := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hv₀
    · exact Finset.mem_singleton.mp hv ▸ hv₁
  have hsize : keep.card ≤ 2 := by
    dsimp only [keep]
    rw [Finset.card_sdiff_of_subset hrB.1, Finset.card_sdiff_of_subset hrA.1,
      Finset.card_univ,Fintype.card_fin]
    have hAp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ha)
    have hBp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hb)
    omega
  have heq := Finset.eq_of_subset_of_card_le hpair
    (hsize.trans_eq (Finset.card_pair_eq_two_iff.mpr hne).symm)
  intro v hv
  have hv' : v ∈ ({v₀,v₁} : Finset (Fin s)) := heq.symm ▸ (show v ∈ keep from hv)
  rcases Finset.mem_insert.mp hv' with rfl | hv'
  · exact ⟨0,h₀⟩
  · simpa only [Finset.mem_singleton.mp hv'] using (show ∃ d, ∀ j, q j v₁ = d from ⟨1,h₁⟩)

private theorem eventual_positive {q : ℕ → Fin s → ℕ} {V A : Finset (Fin s)}
    (h : removalRound q V A) : ∀ᶠ j in atTop, ∀ t ∈ A, 0 < q j t :=
  (eventually_all_finset A).mpr fun _ ht => (removal_index_tendsto h ht).eventually_gt_atTop 0

theorem reduce_to_constant_indices (hs : s ∈ Set.Icc 2 4) (k : ℕ → Fin s → ℕ)
    (hk : ∀ j, Function.Injective (k j)) (v₀ v₁ : Fin s)
    (h₀ : ∀ j, k j v₀ = 0) (h₁ : ∀ j, k j v₁ = 1) :
    ∃ (φ : ℕ → ℕ) (A B : Finset (Fin s)), StrictMono φ ∧
      let q := fun j => k (φ j)
      let keep := (Finset.univ \ A) \ B
      let μ := fun j v => multiplier (q j) A v * multiplier (q j) B v
      removalRound q Finset.univ A ∧ removalRound q (Finset.univ \ A) B ∧
      v₀ ∈ keep ∧ v₁ ∈ keep ∧ (∀ v ∈ keep, ∃ d, ∀ j, q j v = d) ∧
      (∀ v ∈ keep, Tendsto (fun j => μ j v) atTop (𝓝 1)) ∧
      ∀ a : ℕ → Fin s → ℂ, (∀ j v, a j v ≠ 0) →
        let F := fun j => slotSum (q j) (a (φ j))
        let G := fun j => applyFilters (q j) B (applyFilters (q j) A (F j))
        (∀ᶠ j in atTop, G j = ∑ v ∈ keep, C ((μ j v : ℂ)*a (φ j) v) * hermite (q j v)) ∧
        (∀ t : ℕ → ℂ, (∀ v ∈ ({v₀, v₁} : Finset (Fin s)),
          Tendsto (fun j => a (φ j) v / t j) atTop (𝓝 1)) →
          ∀ v ∈ ({v₀, v₁} : Finset (Fin s)),
            Tendsto (fun j => (μ j v : ℂ)*a (φ j) v / t j) atTop (𝓝 1)) ∧
        (escapesDisks F → escapesDisks G) := by
  obtain ⟨φ,A,hφ,first,_⟩ := select_removal_round k Finset.univ
  obtain ⟨ψ,B,hψ,second,hstable⟩ := select_removal_round (fun j => k (φ j)) (Finset.univ \ A)
  let τ := φ ∘ ψ
  let q := fun j => k (τ j)
  let keep := (Finset.univ \ A) \ B
  let μ := fun j v => multiplier (q j) A v * multiplier (q j) B v
  have hA : removalRound q Finset.univ A := removal_round_subsequence first ψ hψ
  have hB : removalRound q (Finset.univ \ A) B := second
  have low₀ (j : ℕ) : q j v₀ = 0 := h₀ (τ j)
  have low₁ (j : ℕ) : q j v₁ = 1 := h₁ (τ j)
  have survive {v : Fin s} {d : ℕ} (h : ∀ j, q j v = d) : v ∈ keep :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, keeps_constant hA h⟩,
      keeps_constant hB h⟩
  have hc := constant_after_two hs.2 hA hB low₀ low₁ (survive low₀) (survive low₁)
  have hμ (v : Fin s) (hv : v ∈ keep) : Tendsto (fun j => μ j v) atTop (𝓝 1) := by
    simpa only [μ,mul_one] using (round_multiplier_limit hA (hc v hv)).mul
      (round_multiplier_limit hB (hc v hv))
  refine ⟨τ,A,B,hφ.comp hψ,hA,hB,survive low₀,survive low₁,hc,hμ,?_⟩
  intro a _
  let F := fun j => slotSum (q j) (a (τ j))
  refine ⟨two_round_expansion q A B (eventual_positive hA) (eventual_positive hB) (fun j => a (τ j)),
    ?_, ?_⟩
  · intro t ht v hv
    have hk' : v ∈ keep := by
      rcases Finset.mem_insert.mp hv with rfl | h
      · exact survive low₀
      · exact Finset.mem_singleton.mp h ▸ survive low₁
    have hm := Complex.continuous_ofReal.continuousAt.tendsto.comp (hμ v hk')
    simpa only [mul_div_assoc, Complex.ofReal_one, one_mul, Function.comp_apply] using
      hm.mul (ht v hv)
  · intro he
    have hf := escaping_slot_sum_flat hs q (fun j => hk (τ j)) v₀ v₁ low₀ low₁ hstable
      (fun j => a (τ j)) he
    exact two_round_escape_of_flat q A B F he hf

#print axioms reduce_to_constant_indices

end Turan.SectionTwo
