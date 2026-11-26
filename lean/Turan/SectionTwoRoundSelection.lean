module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.SectionTwoLimitsDefs
public import Mathlib.Topology.Instances.ENat

@[expose] public section

open Filter
open scoped Topology
namespace Turan.SectionTwo

/-- A finite limit in the compact space of extended naturals is eventually attained.
Discard a common initial segment for all such coordinates. -/
private theorem select_index_limits {s : ℕ} (k : ℕ → Fin s → ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ v,
      (∃ d, ∀ j, k (φ j) v = d) ∨ Tendsto (fun j => k (φ j) v) atTop atTop := by
  classical
  let x (j : ℕ) (v : Fin s) : ℕ∞ := k j v
  obtain ⟨g, σ, hσ, hg⟩ := CompactSpace.tendsto_subseq x
  have hfinite (v : Fin s) : ∀ᶠ j in atTop, g v ≠ ⊤ → x (σ j) v = g v := by
    by_cases hv : g v = ⊤
    · simp [hv]
    · have h := tendsto_pi_nhds.mp hg v
      rw [ENat.nhds_eq_pure hv, tendsto_pure] at h
      exact h.mono fun j hj _ => hj
  obtain ⟨τ, hτ, hfix⟩ := extraction_of_eventually_atTop (eventually_all.mpr hfinite)
  refine ⟨σ ∘ τ, hσ.comp hτ, fun v => ?_⟩
  by_cases hv : g v = ⊤
  · right
    have h := tendsto_pi_nhds.mp hg v
    rw [hv, ENat.tendsto_nhds_top_iff_natCast_lt] at h
    apply Tendsto.comp (g := fun j => k (σ j) v) _ hτ.tendsto_atTop
    refine tendsto_atTop.mpr fun b => (h b).mono fun j hj => ?_
    exact le_of_lt (by exact_mod_cast (show (b : ℕ∞) < (k (σ j) v : ℕ∞) from hj))
  · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hv
    refine Or.inl ⟨d, fun j => ?_⟩
    exact_mod_cast (show (k (σ (τ j)) v : ℕ∞) = (d : ℕ∞) from (hfix j v hv).trans hd.symm)

/-- When the active maximum diverges, a fixed maximizing slot has ratio one on
a subsequence. Compactness then supplies simultaneous limits for all active ratios. -/
private theorem select_divergent_round {s : ℕ} (k : ℕ → Fin s → ℕ)
    (active : Finset (Fin s)) (hne : active.Nonempty)
    (htop : Tendsto (fun j => active.sup (k j)) atTop atTop) :
    ∃ (φ : ℕ → ℕ) (A : Finset (Fin s)), StrictMono φ ∧
      removalRound (fun j => k (φ j)) active A := by
  classical
  have hfreq : ∃ᶠ j in atTop, ∃ v, v ∈ active ∧ active.sup (k j) = k j v :=
    Frequently.of_forall fun j => active.exists_mem_eq_sup hne (k j)
  obtain ⟨v, hv⟩ := frequently_exists.mp hfreq
  obtain ⟨σ, hσ, hmax⟩ := extraction_of_frequently_atTop
    (hv.and_eventually (htop.eventually_gt_atTop 0))
  let ratio (j : ℕ) (w : Fin s) := lambda (k (σ j) w) / lambda (active.sup (k (σ j)))
  have hpos (j : ℕ) : 0 < lambda (active.sup (k (σ j))) := by
    unfold lambda
    exact mul_pos (by norm_num) (by exact_mod_cast (hmax j).2)
  have hratio (j w) (hw : w ∈ active) : ratio j w ∈ Set.Icc 0 1 := by
    refine ⟨div_nonneg (by unfold lambda; positivity) (hpos j).le, (div_le_one (hpos j)).mpr ?_⟩
    unfold lambda
    gcongr
    exact Finset.le_sup hw
  let x (j : ℕ) (w : Fin s) : Set.Icc (0 : ℝ) 1 :=
    if hw : w ∈ active then ⟨ratio j w, hratio j w hw⟩ else ⟨0, by simp⟩
  obtain ⟨g, τ, hτ, hg⟩ := CompactSpace.tendsto_subseq x
  have hlim (w) (hw : w ∈ active) : Tendsto (fun j => ratio (τ j) w) atTop (𝓝 (g w).val) := by
    simpa [x, hw, Function.comp_def] using
      (continuous_subtype_val.tendsto (g w)).comp (tendsto_pi_nhds.mp hg w)
  have hvMem := (hmax 0).1.1
  have hone (j) : ratio j v = 1 := by
    simp only [ratio, ← (hmax j).1.2, div_self (hpos j).ne']
  have hgv : (g v).val = 1 := by
    apply tendsto_nhds_unique (hlim v hvMem)
    simpa only [hone] using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ)))
  let A := active.filter fun w => 0 < (g w).val
  refine ⟨σ ∘ τ, A, hσ.comp hτ, Finset.filter_subset .., Or.inr ?_⟩
  refine ⟨⟨v, Finset.mem_filter.mpr ⟨hvMem, by simp [hgv]⟩⟩,
    htop.comp (hσ.comp hτ).tendsto_atTop, fun w => (g w).val, fun w hw => ?_⟩
  exact ⟨hlim w hw, by simp [A, hw]⟩

theorem select_removal_round {s : ℕ} (k : ℕ → Fin s → ℕ) (active : Finset (Fin s)) :
    ∃ (φ : ℕ → ℕ) (A : Finset (Fin s)), StrictMono φ ∧
      removalRound (fun j => k (φ j)) active A ∧
      ∀ v, (∃ d, ∀ j, k (φ j) v = d) ∨ Tendsto (fun j => k (φ j) v) atTop atTop := by
  classical
  obtain ⟨σ, hσ, hs⟩ := select_index_limits k
  by_cases hc : ∀ v ∈ active, ∃ d, ∀ j, k (σ j) v = d
  · exact ⟨σ, ∅, hσ, ⟨Finset.empty_subset _, Or.inl ⟨rfl, hc⟩⟩, hs⟩
  push Not at hc
  obtain ⟨v, hv, hnc⟩ := hc
  have hvtop := (hs v).resolve_left (by simpa using hnc)
  have htop := tendsto_atTop_mono (fun j => Finset.le_sup (f := k (σ j)) hv) hvtop
  obtain ⟨τ, A, hτ, hround⟩ :=
    select_divergent_round (fun j => k (σ j)) active ⟨v, hv⟩ htop
  refine ⟨σ ∘ τ, A, hσ.comp hτ, hround, fun w => ?_⟩
  rcases hs w with ⟨d, hd⟩ | h
  · exact Or.inl ⟨d, fun j => hd (τ j)⟩
  · exact Or.inr (h.comp hτ.tendsto_atTop)

end Turan.SectionTwo
