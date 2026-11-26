module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.SectionTwoOperators

@[expose] public section

noncomputable section
open Polynomial Filter
open scoped BigOperators
namespace Turan.SectionTwo

private theorem filters_slotSum {s : ℕ} (k : Fin s → ℕ) (V : Finset (Fin s))
    (hV : ∀ t ∈ V, 0 < k t) (a : Fin s → ℂ) :
    applyFilters k V (slotSum k a) =
      slotSum k (fun v => (multiplier k V v : ℂ) * a v) := by
  classical
  have step (μ : ℝ) (hμ : 0 < μ) (b : Fin s → ℂ) :
      realFilter μ (slotSum k b) =
        slotSum k (fun v => ((1 - lambda (k v) / μ : ℝ) : ℂ) * b v) := by
    let F : Polynomial ℂ →+ Polynomial ℂ :=
      { toFun := realFilter μ
        map_zero' := by simp [realFilter, EStar]
        map_add' := by
          intro p r
          simp only [realFilter, EStar_add, mul_add]
          abel }
    change F (∑ v, C (b v) * hermite (k v)) = _
    rw [map_sum, slotSum]
    apply Finset.sum_congr rfl
    intro v _
    change realFilter μ (C (b v) * hermite (k v)) = _
    have h := (single_filter_action μ hμ (k v)).1
    simp only [realFilter, EStar_C_mul, map_mul] at h ⊢
    linear_combination C (b v) * h
  let factor (v t : Fin s) := 1 - lambda (k v) / lambda (k t)
  have aux (l : List (Fin s)) (hl : ∀ t ∈ l, 0 < k t) :
      l.foldr (fun t p => realFilter (lambda (k t)) p) (slotSum k a) =
        slotSum k (fun v => (((l.map (factor v)).prod : ℝ) : ℂ) * a v) := by
    induction l with
    | nil => simp
    | cons t l ih =>
      have ht := hl t List.mem_cons_self
      have hlam : 0 < lambda (k t) := by unfold lambda; positivity
      rw [List.foldr_cons, ih (fun u hu => hl u (List.mem_cons_of_mem _ hu)), step _ hlam]
      simp only [List.map_cons, List.prod_cons, Complex.ofReal_mul, factor, mul_assoc]
  simpa only [applyFilters, multiplier, Finset.prod_map_toList, factor] using
    aux V.toList (by simpa using hV)

/-- Two rounds of filters leave precisely the sum over the slots outside both rounds. -/
theorem two_round_expansion {s : ℕ} (q : ℕ → Fin s → ℕ) (A B : Finset (Fin s))
    (hApos : ∀ᶠ j in atTop, ∀ t ∈ A, 0 < q j t)
    (hBpos : ∀ᶠ j in atTop, ∀ t ∈ B, 0 < q j t) (a : ℕ → Fin s → ℂ) :
    ∀ᶠ j in atTop,
      applyFilters (q j) B (applyFilters (q j) A (slotSum (q j) (a j))) =
        ∑ v ∈ (Finset.univ \ A) \ B,
          C (((multiplier (q j) A v * multiplier (q j) B v : ℝ) : ℂ) * a j v) *
            hermite (q j v) := by
  classical
  filter_upwards [hApos, hBpos] with j hA hB
  rw [filters_slotSum _ A hA, filters_slotSum _ B hB, slotSum]
  simp only [Complex.ofReal_mul, mul_left_comm, mul_assoc]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro v _ hv
  have vanish (V : Finset (Fin s)) (hV : ∀ t ∈ V, 0 < q j t) (hmem : v ∈ V) :
      multiplier (q j) V v = 0 := by
    have hdeg := hV v hmem
    have hlam : 0 < lambda (q j v) := by unfold lambda; positivity
    exact Finset.prod_eq_zero hmem (by simp [hlam.ne'])
  by_cases hvA : v ∈ A
  · simp [vanish A hA hvA]
  · have hvB : v ∈ B := by simpa [Finset.mem_sdiff, hvA] using hv
    simp [vanish B hB hvB]

end Turan.SectionTwo
