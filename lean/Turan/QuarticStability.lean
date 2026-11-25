-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Rouche
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Tactic

noncomputable section
open Polynomial Set Metric Filter
open scoped Topology
namespace Turan

/-- Stability of a polynomial zero under jointly continuous variation of the
coefficients, including variation that can increase the degree. -/
theorem nearby_polynomial_root {T : Type*} [TopologicalSpace T]
    (p : T → Polynomial ℂ) (hp : Continuous (fun v : T × ℂ => (p v.1).eval v.2))
    (a : T) (hpa : p a ≠ 0) (z : ℂ) (hz : (p a).eval z=0) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ b in 𝓝 a, ∃ w : ℂ, (p b).eval w=0 ∧ dist w z < ε := by
  classical
  obtain ⟨r,hr,havoid⟩ := (Set.Ioo_infinite hε).exists_notMem_finset
    ((p a).roots.toFinset.image (fun w => dist w z))
  have hfree (v : ℂ) (hv : v ∈ sphere z r) : (p a).eval v ≠ 0 := by
    intro h
    apply havoid
    exact Finset.mem_image.mpr ⟨v, Multiset.mem_toFinset.mpr ((mem_roots hpa).mpr h), mem_sphere.mp hv⟩
  let G := {v : T × ℂ | ‖(p v.1).eval v.2-(p a).eval v.2‖ < ‖(p a).eval v.2‖}
  have hopen : IsOpen G := isOpen_lt (hp.sub ((p a).continuous.comp continuous_snd)).norm
    ((p a).continuous.comp continuous_snd).norm
  have hsub : ({a}:Set T) ×ˢ sphere z r ⊆ G := by
    rintro ⟨v,w⟩ ⟨(rfl : v=a), hw⟩
    simpa [G] using (norm_pos_iff.mpr (hfree w hw))
  obtain ⟨U,V,hU,_,ha,hV,hUV⟩ := generalized_tube_lemma isCompact_singleton (isCompact_sphere z r) hopen hsub
  filter_upwards [hU.mem_nhds (singleton_subset_iff.mp ha)] with b hb
  have hcount := polynomial_rouche (p a) (p b) z r hr.1 (fun w hw => hUV (mk_mem_prod hb (hV hw)))
  have hmem : z ∈ (p a).roots.filter (fun w => dist w z < r) :=
    Multiset.mem_filter.mpr ⟨(mem_roots hpa).mpr hz, by simpa using hr.1⟩
  have hpos : 0 < ((p b).roots.filter (fun w => dist w z < r)).card := by
    rw [hcount]; exact Multiset.card_pos_iff_exists_mem.mpr ⟨z,hmem⟩
  obtain ⟨w,hw⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
  obtain ⟨hroot,hd⟩ := Multiset.mem_filter.mp hw
  exact ⟨w,isRoot_of_mem_roots hroot,hd.trans hr.2⟩

end Turan
