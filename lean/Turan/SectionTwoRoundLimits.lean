module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.SectionTwoLimitsDefs

@[expose] public section

open Filter
open scoped Topology

namespace Turan.SectionTwo

variable {s : ℕ} {q : ℕ → Fin s → ℕ} {active removed : Finset (Fin s)}

private theorem lambda_tendsto_atTop_iff {u : ℕ → ℕ} :
    Tendsto (fun j => lambda (u j)) atTop atTop ↔ Tendsto u atTop atTop :=
  (tendsto_const_mul_atTop_of_pos (two_pos : 0 < (2 : ℝ))).trans tendsto_natCast_atTop_iff

theorem removal_index_tendsto (hr : removalRound q active removed) {v : Fin s}
    (hv : v ∈ removed) : Tendsto (fun j => q j v) atTop atTop := by
  obtain ⟨hsub, ⟨rfl, _⟩ | ⟨_, hmax, γ, hγ⟩⟩ := hr
  · simp at hv
  · obtain ⟨hratio, hpos⟩ := hγ v (hsub hv)
    exact lambda_tendsto_atTop_iff.mp
      ((lambda_tendsto_atTop_iff.mpr hmax).num (hpos.mp hv) hratio)

theorem round_multiplier_limit (hr : removalRound q active removed) {v : Fin s}
    (hv : ∃ d, ∀ j, q j v = d) :
    Tendsto (fun j => multiplier (q j) removed v) atTop (𝓝 1) := by
  obtain ⟨d, hd⟩ := hv
  have factor (t : Fin s) (ht : t ∈ removed) :
      Tendsto (fun j => 1 - lambda (q j v) / lambda (q j t)) atTop (𝓝 1) := by
    have hden := lambda_tendsto_atTop_iff.mpr (removal_index_tendsto hr ht)
    simpa only [hd, sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (hden.const_div_atTop (lambda d))
  simpa [multiplier] using tendsto_finsetProd removed factor

theorem removal_round_subsequence (hr : removalRound q active removed)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) : removalRound (fun j => q (φ j)) active removed := by
  obtain ⟨hsub, ⟨hempty, hconst⟩ | ⟨hne, hmax, γ, hγ⟩⟩ := hr
  · refine ⟨hsub, Or.inl ⟨hempty, fun v hv => ?_⟩⟩
    obtain ⟨d, hd⟩ := hconst v hv
    exact ⟨d, fun j => hd (φ j)⟩
  · refine ⟨hsub, Or.inr ⟨hne, hmax.comp hφ.tendsto_atTop, γ, fun v hv => ?_⟩⟩
    obtain ⟨hratio, hpos⟩ := hγ v hv
    exact ⟨hratio.comp hφ.tendsto_atTop, hpos⟩

end Turan.SectionTwo
