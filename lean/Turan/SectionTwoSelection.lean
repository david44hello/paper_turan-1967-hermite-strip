-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.SectionTwoAlgebraDefs

noncomputable section
open Polynomial Filter Metric
open scoped Topology Classical
namespace Turan.SectionTwo

theorem select_escaping_polynomials (P : ℕ → Polynomial ℂ)
    (h : ∀ R : ℝ, 0 < R → ∃ i, ∀ z : ℂ, ‖z‖ < R → (P i).eval z ≠ 0) :
    ∃ i : ℕ → ℕ, (∀ (j : ℕ) (z : ℂ), ‖z‖ < (j : ℝ)+1 → (P (i j)).eval z ≠ 0) ∧
      escapesDisks (fun j => P (i j)) := by
  choose i hi using fun j : ℕ => h ((j : ℝ)+1) (by positivity)
  refine ⟨i, hi, fun R _ => ?_⟩
  obtain ⟨b, hb⟩ := exists_nat_ge R
  filter_upwards [eventually_ge_atTop b] with j hj z hz
  exact hi j z (by linarith [show (b : ℝ) ≤ j by exact_mod_cast hj])

private def stable (u : ℕ → ℕ) : Prop := (∃ d, ∀ j, u j = d) ∨ Tendsto u atTop atTop

private theorem stable_comp {u φ : ℕ → ℕ} (h : stable u) (hφ : StrictMono φ) : stable (u ∘ φ) := by
  rcases h with ⟨d, hd⟩ | ht
  · exact Or.inl ⟨d, fun j => hd (φ j)⟩
  · exact Or.inr (ht.comp hφ.tendsto_atTop)

private theorem stable_subseq (u : ℕ → ℕ) : ∃ φ, StrictMono φ ∧ stable (u ∘ φ) := by
  by_cases h : ∃ d, ∃ᶠ j in atTop, u j = d
  · obtain ⟨d, hd⟩ := h
    obtain ⟨φ, hφ, hval⟩ := extraction_of_frequently_atTop hd
    exact ⟨φ, hφ, Or.inl ⟨d, hval⟩⟩
  refine ⟨id, strictMono_id, Or.inr (tendsto_atTop.mpr fun b => ?_)⟩
  have hn (d : ℕ) : ∀ᶠ j in atTop, u j ≠ d := not_frequently.mp (fun hd => h ⟨d, hd⟩)
  filter_upwards [(eventually_all_finset (Finset.range b)).mpr (fun d _ => hn d)] with j hj
  exact le_of_not_gt fun hlt => hj (u j) (Finset.mem_range.mpr hlt) rfl

private theorem stable_coords {ι : Type*} (S : Finset ι) (u : ℕ → ι → ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ v ∈ S, stable (fun j => u (φ j) v) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨id, strictMono_id, by simp⟩
  | insert v S hv ih =>
    obtain ⟨φ, hφ, hS⟩ := ih
    obtain ⟨ψ, hψ, hv'⟩ := stable_subseq (fun j => u (φ j) v)
    refine ⟨φ ∘ ψ, hφ.comp hψ, fun t ht => ?_⟩
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hv'
    · exact stable_comp (hS t ht) hψ

theorem select_active_slots (k : ℕ → Fin 4 → ℕ) (a : ℕ → Fin 4 → ℂ)
    (hpos : ∀ j, ∃ v, a j v ≠ 0 ∧ 0 < k j v) :
    ∃ (φ : ℕ → ℕ) (V : Finset (Fin 4)) (γ : Fin 4 → ℝ), StrictMono φ ∧
      (∀ j v, v ∈ V ↔ a (φ j) v ≠ 0) ∧
      (∀ v ∈ V, (∃ d, ∀ j, k (φ j) v = d) ∨ Tendsto (fun j => k (φ j) v) atTop atTop) ∧
      ∀ v ∈ V, γ v ∈ Set.Icc 0 1 ∧
        Tendsto (fun j => lambda (k (φ j) v) / lambda (V.sup (k (φ j)))) atTop (𝓝 (γ v)) := by
  let active (j : ℕ) := Finset.univ.filter (fun v => a j v ≠ 0)
  have hf : ∃ᶠ j in atTop, ∃ V : Finset (Fin 4), active j = V :=
    Frequently.of_forall fun j => ⟨_, rfl⟩
  obtain ⟨V, hV⟩ := frequently_exists.mp hf
  obtain ⟨τ, hτ, hfix⟩ := extraction_of_frequently_atTop hV
  obtain ⟨σ, hσ, hstable⟩ := stable_coords V (fun j => k (τ j))
  let ψ := τ ∘ σ
  have hψ : StrictMono ψ := hτ.comp hσ
  have hs (j v) : v ∈ V ↔ a (ψ j) v ≠ 0 := by rw [← hfix (σ j)]; simp [active, ψ]
  let ratio (j : ℕ) (v : Fin 4) := lambda (k (ψ j) v) / lambda (V.sup (k (ψ j)))
  have hr (j v) (hv : v ∈ V) : ratio j v ∈ Set.Icc 0 1 := by
    obtain ⟨t, ht, ht'⟩ := hpos (ψ j)
    have hmax := Finset.le_sup (f := k (ψ j)) ((hs j t).mpr ht)
    have hden : 0 < lambda (V.sup (k (ψ j))) := by
      unfold lambda
      have : 0 < ((V.sup (k (ψ j)) : ℕ) : ℝ) := by exact_mod_cast ht'.trans_le hmax
      positivity
    refine ⟨div_nonneg (by unfold lambda; positivity) hden.le, (div_le_one hden).mpr ?_⟩
    unfold lambda
    gcongr
    exact Finset.le_sup hv
  let x (j : ℕ) (v : Fin 4) : Set.Icc (0 : ℝ) 1 :=
    if hv : v ∈ V then ⟨ratio j v, hr j v hv⟩ else ⟨0, by simp⟩
  obtain ⟨g, φ, hφ, hg⟩ := CompactSpace.tendsto_subseq x
  refine ⟨ψ ∘ φ, V, fun v => (g v).val, hψ.comp hφ, fun j => hs (φ j),
    fun v hv => stable_comp (hstable v hv) hφ, fun v hv => ⟨(g v).property, ?_⟩⟩
  simpa [x, hv, ratio, Function.comp_def] using
    (continuous_subtype_val.tendsto (g v)).comp (tendsto_pi_nhds.mp hg v)

end Turan.SectionTwo
