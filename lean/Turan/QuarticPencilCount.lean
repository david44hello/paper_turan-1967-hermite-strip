module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.QuarticPencilDefs
public import Turan.Rouche
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Polynomial Filter Set Metric
open scoped Topology
namespace Turan

private theorem pencil_degree_four (d : ℝ) : (contactPencilPoly d).natDegree = 4 := by
  unfold contactPencilPoly
  compute_degree!

private theorem pencil_disk_stability (a : ℝ) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hfree : ∀ z ∈ sphere c r, (contactPencilPoly a).eval z ≠ 0) :
    ∀ᶠ b in 𝓝 a,
      ((contactPencilPoly b).roots.filter (fun z => dist z c < r)).card =
      ((contactPencilPoly a).roots.filter (fun z => dist z c < r)).card := by
  let G := {x : ℝ × ℂ | ‖(contactPencilPoly x.1).eval x.2 -
    (contactPencilPoly a).eval x.2‖ < ‖(contactPencilPoly a).eval x.2‖}
  have hopen : IsOpen G := by
    apply isOpen_lt
    · simp only [contactPencilPoly_eval]
      fun_prop
    · exact ((contactPencilPoly a).continuous.comp continuous_snd).norm
  have hsub : ({a} : Set ℝ) ×ˢ sphere c r ⊆ G := by
    rintro ⟨v,w⟩ ⟨(rfl : v = a),hw⟩
    simpa [G] using norm_pos_iff.mpr (hfree w hw)
  obtain ⟨U,V,hU,_,ha,hV,hUV⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_sphere c r) hopen hsub
  filter_upwards [hU.mem_nhds (singleton_subset_iff.mp ha)] with b hb
  exact polynomial_rouche _ _ c r hr (fun w hw => hUV (mk_mem_prod hb (hV hw)))

/-- A large disk tangent to the line from the chosen side contains every
root on that side at the base parameter. Its count persists nearby. -/
private theorem pencil_side_lower_bound (a h s : ℝ) (hs : s = 1 ∨ s = -1)
    (hboundary : ∀ z : ℂ, z.im = h → (contactPencilPoly a).eval z ≠ 0) :
    ∀ᶠ b in 𝓝 a,
      ((contactPencilPoly a).roots.filter (fun z => 0 < s * (z.im-h))).card ≤
      ((contactPencilPoly b).roots.filter (fun z => 0 < s * (z.im-h))).card := by
  classical
  let side := fun z : ℂ => s * (z.im-h)
  let size := fun z : ℂ => z.re^2 + (z.im-h)^2
  have hlarge : ∀ᶠ r : ℝ in atTop, ∀ z ∈ (contactPencilPoly a).roots.toFinset,
      size z / (2 * side z) < r :=
    (eventually_all_finset _).2 fun z _ => eventually_gt_atTop _
  obtain ⟨r, hr, hbound⟩ := ((eventually_gt_atTop (0 : ℝ)).and hlarge).exists
  let c : ℂ := ⟨0, h + s*r⟩
  have hdist (z : ℂ) : dist z c ^ 2 = r^2 + size z - 2*r*side z := by
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
    simp only [c, Complex.sub_re, Complex.sub_im, sub_zero, size, side]
    rcases hs with rfl | rfl <;> ring
  have hsize (z : ℂ) : 0 ≤ size z := by dsimp [size]; positivity
  have hinside (z : ℂ) (hz : z ∈ (contactPencilPoly a).roots) (hp : 0 < side z) :
      dist z c < r := by
    have h := (div_lt_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hp)).mp
      (hbound z (Multiset.mem_toFinset.mpr hz))
    apply (sq_lt_sq₀ dist_nonneg hr.le).mp
    linarith only [hdist z, show size z < 2*r*side z by linarith only [h]]
  have hside (z : ℂ) (hz : dist z c < r) : 0 < side z := by
    have hh := (sq_lt_sq₀ dist_nonneg hr.le).mpr hz
    by_contra! hn
    nlinarith only [hh, hdist z, hsize z, mul_nonpos_of_nonneg_of_nonpos hr.le hn]
  have hfree (z : ℂ) (hz : z ∈ sphere c r) : (contactPencilPoly a).eval z ≠ 0 := by
    intro hzero
    have hd := mem_sphere.mp hz
    have hpa := ne_zero_of_natDegree_gt (show 0 < (contactPencilPoly a).natDegree by
      rw [pencil_degree_four]; decide)
    have hne : side z ≠ 0 := mul_ne_zero (by rcases hs with rfl | rfl <;> norm_num)
      (sub_ne_zero.mpr fun he => hboundary z he hzero)
    have hp : 0 < side z := by
      apply lt_of_le_of_ne _ hne.symm
      by_contra! hn
      nlinarith only [hdist z, congrArg (fun x : ℝ => x^2) hd, hsize z, mul_neg_of_pos_of_neg hr hn]
    exact (hinside z ((mem_roots hpa).mpr hzero) hp).ne hd
  filter_upwards [pencil_disk_stability a c r hr hfree] with b hb
  have heq := Multiset.filter_congr (fun z hz => ⟨hside z, hinside z hz⟩)
  calc
    _ = ((contactPencilPoly a).roots.filter (fun z => dist z c < r)).card :=
      congrArg Multiset.card heq.symm
    _ = _ := hb.symm
    _ ≤ _ := Multiset.card_le_card (Multiset.monotone_filter_right _ hside)

/-- A constant-degree pencil with no zero on the boundary line along a parameter
interval has constant root count above the line, with multiplicity. -/
theorem quartic_pencil_count_on_interval (h u v : ℝ) (huv : u ≤ v)
    (hboundary : ∀ d ∈ Icc u v, ∀ z : ℂ, z.im=h → (contactPencilPoly d).eval z ≠ 0) :
    ((contactPencilPoly u).roots.filter (fun z => h<z.im)).card =
      ((contactPencilPoly v).roots.filter (fun z => h<z.im)).card := by
  classical
  let upper (a : Icc u v) := ((contactPencilPoly a).roots.filter (fun z => h < z.im)).card
  let lower (a : Icc u v) := ((contactPencilPoly a).roots.filter (fun z => z.im < h)).card
  have htotal (a : Icc u v) : upper a + lower a = 4 := by
    have hsplit := Multiset.filter_add_not (fun z : ℂ => h < z.im) (contactPencilPoly a).roots
    have heq : (contactPencilPoly a).roots.filter (fun z => ¬ h < z.im) =
        (contactPencilPoly a).roots.filter (fun z => z.im < h) := by
      apply Multiset.filter_congr
      intro z hz
      have hn : z.im ≠ h := fun he => hboundary a a.property z he (isRoot_of_mem_roots hz)
      exact ⟨fun hnlt => lt_of_le_of_ne (le_of_not_gt hnlt) hn, fun hlt => hlt.not_gt⟩
    rw [heq] at hsplit
    calc
      _ = (contactPencilPoly a).roots.card := by
        simpa only [upper, lower, Multiset.card_add] using congrArg Multiset.card hsplit
      _ = 4 := (IsAlgClosed.splits _).natDegree_eq_card_roots.symm.trans (pencil_degree_four a)
  have hloc : IsLocallyConstant upper := by
    apply (IsLocallyConstant.iff_eventually_eq _).2
    intro a
    have hup := pencil_side_lower_bound a h 1 (Or.inl rfl) (hboundary a a.property)
    have hlo := pencil_side_lower_bound a h (-1) (Or.inr rfl) (hboundary a a.property)
    have ht : Tendsto ((↑) : Icc u v → ℝ) (𝓝 a) (𝓝 (a : ℝ)) := continuous_subtype_val.continuousAt
    filter_upwards [ht.eventually hup, ht.eventually hlo] with b hb₁ hb₂
    have hu : upper a ≤ upper b := by simpa only [upper, one_mul, sub_pos] using hb₁
    have hl : lower a ≤ lower b := by simpa only [lower, neg_one_mul, neg_pos, sub_neg] using hb₂
    have ha := htotal a
    have hb := htotal b
    omega
  let : PreconnectedSpace (Icc u v) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  exact hloc.apply_eq_of_preconnectedSpace ⟨u, le_rfl, huv⟩ ⟨v, huv, le_rfl⟩

#print axioms quartic_pencil_count_on_interval

end Turan
