module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.WindingDefs
public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Covering.AddCircle

@[expose] public section

noncomputable section
open Polynomial Set
namespace Turan.Polygon

/-- The argument in (0, 2π]. A vertex on the positive real ray has angle
    2π and belongs to the nonpositive-imaginary side of the crossing test. -/
private def argPos (z : ℂ) : ℝ := (-z).arg + Real.pi

private theorem argPos_coe {z : ℂ} (hz : z ≠ 0) : (argPos z : Real.Angle) = z.arg := by
  rw [argPos, Real.Angle.coe_add, Complex.arg_neg_coe_angle hz, add_assoc,
    ← Real.Angle.coe_add, ← two_mul, Real.Angle.coe_two_pi, add_zero]

private theorem argPos_bounds (z : ℂ) :
    0 < argPos z ∧ argPos z ≤ 2*Real.pi ∧ (argPos z < Real.pi ↔ 0 < z.im) := by
  unfold argPos
  refine ⟨by linarith [Complex.neg_pi_lt_arg (-z)], by linarith [Complex.arg_le_pi (-z)], ?_⟩
  rw [add_lt_iff_neg_right, Complex.arg_neg_iff, Complex.neg_im, neg_lt_zero]

private theorem disk_ne {a c : ℂ} (h : ‖a-c‖ < ‖c‖) : a ≠ 0 ∧ c ≠ 0 := by
  constructor
  · rintro rfl; simp at h
  · rintro rfl; simp only [sub_zero, norm_zero] at h; exact (norm_nonneg a).not_gt h

private theorem disk_re {a c : ℂ} (h : ‖a-c‖ < ‖c‖) : 0 < (a/c).re := by
  have hc := (disk_ne h).2
  have hball : ‖a/c-1‖ < 1 := by
    rw [show a/c-1 = (a-c)/c by rw [sub_div, div_self hc], norm_div,
      div_lt_one (norm_pos_iff.mpr hc)]
    exact h
  have hre := (Complex.abs_re_le_norm (a/c-1)).trans_lt hball
  rw [Complex.sub_re, Complex.one_re, abs_lt] at hre
  linarith [hre.1]

/-- Two points in the same edge disk have a unique relative argument in
    (-π, π), equal to the difference of their arguments relative to the center. -/
private theorem disk_turn {a b c : ℂ} (ha : ‖a-c‖ < ‖c‖) (hb : ‖b-c‖ < ‖c‖) :
    (b/a).arg = (b/c).arg - (a/c).arg ∧ |(b/a).arg| < Real.pi := by
  have half {v : ℂ} (hv : ‖v-c‖ < ‖c‖) :=
    abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (disk_re hv)))
  have h₁ := half ha
  have h₂ := half hb
  have hd : |(b/c).arg - (a/c).arg| < Real.pi := abs_lt.mpr ⟨by linarith, by linarith⟩
  have he : (((b/c).arg - (a/c).arg : ℝ) : Real.Angle) = (b/a).arg := by
    rw [Real.Angle.coe_sub, Complex.arg_div_coe_angle (disk_ne hb).1 (disk_ne ha).2,
      Complex.arg_div_coe_angle (disk_ne ha).1 (disk_ne ha).2,
      Complex.arg_div_coe_angle (disk_ne hb).1 (disk_ne ha).1]
    abel
  have hreal := congrArg Real.Angle.toReal he
  rw [Real.Angle.toReal_coe_eq_self_iff.mpr ⟨(abs_lt.mp hd).1, (abs_lt.mp hd).2.le⟩,
    Complex.arg_coe_angle_toReal_eq_arg] at hreal
  exact ⟨hreal.symm, hreal ▸ hd⟩

private theorem crossing_turn {a b c : ℂ} (ha : ‖a-c‖ < ‖c‖) (hb : ‖b-c‖ < ‖c‖) :
    (b/a).arg = argPos b - argPos a + 2*Real.pi*(rayCross a b : ℝ) := by
  let δ := (b/a).arg
  let det := a.re*b.im - b.re*a.im
  have hδ := abs_lt.mp (disk_turn ha hb).2
  change -Real.pi < δ ∧ δ < Real.pi at hδ
  have hsin : Real.sin δ = det / a.normSq / ‖b/a‖ := by
    rw [Complex.sin_arg, Complex.div_im, ← sub_div, mul_comm b.im a.re]
  have hnorm := norm_pos_iff.mpr (div_ne_zero (disk_ne hb).1 (disk_ne ha).1)
  have hsq := Complex.normSq_pos.mpr (disk_ne ha).1
  have hpos (hd : 0 < δ) : 0 < det := by
    have hs := Real.sin_pos_of_pos_of_lt_pi hd hδ.2
    rwa [hsin, lt_div_iff₀ hnorm, zero_mul, lt_div_iff₀ hsq, zero_mul] at hs
  have hneg (hd : δ < 0) : det < 0 := by
    have hs := Real.sin_neg_of_neg_of_neg_pi_lt hd hδ.1
    rwa [hsin, div_lt_iff₀ hnorm, zero_mul, div_lt_iff₀ hsq, zero_mul] at hs
  have he : (δ : Real.Angle) = ((argPos b - argPos a : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_sub, argPos_coe (disk_ne hb).1, argPos_coe (disk_ne ha).1]
    exact Complex.arg_div_coe_angle (disk_ne hb).1 (disk_ne ha).1
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp he
  obtain ⟨hA, hA', hupA⟩ := argPos_bounds a
  obtain ⟨hB, hB', hupB⟩ := argPos_bounds b
  have hk₁ : -1 ≤ k := by
    by_contra! h
    have hh : (k:ℝ) ≤ -2 := by exact_mod_cast (show k ≤ -2 by omega)
    nlinarith only [Real.pi_pos, hk, hδ.1, hA, hB', mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hh)]
  have hk₂ : k ≤ 1 := by
    by_contra! h
    have hh : (2:ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
    nlinarith only [Real.pi_pos, hk, hδ.2, hA', hB, mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hh)]
  change δ = _
  interval_cases k
  · norm_num at hk
    have au := hupA.mp (by linarith [hδ.1])
    have bl : b.im ≤ 0 := le_of_not_gt (fun h => by linarith [hupB.mpr h, hδ.1])
    have hd := hneg (by linarith)
    have hcross : rayCross a b = -1 := by
      unfold rayCross
      exact (ite_eq_right (fun h => au.not_ge h.1)).trans (ite_eq_left ⟨bl, au, hd⟩)
    rw [hcross]; norm_num; linarith
  · norm_num at hk
    have nup : ¬ (a.im ≤ 0 ∧ 0 < b.im ∧ 0 < det) := by
      rintro ⟨al, bu, h⟩
      have alo := le_of_not_gt (fun h => al.not_gt (hupA.mp h))
      exact (hneg (by linarith [hupB.mpr bu])).not_gt h
    have ndown : ¬ (b.im ≤ 0 ∧ 0 < a.im ∧ det < 0) := by
      rintro ⟨bl, au, h⟩
      have blo := le_of_not_gt (fun h => bl.not_gt (hupB.mp h))
      exact (hpos (by linarith [hupA.mpr au])).not_gt h
    have hcross : rayCross a b = 0 := by
      unfold rayCross
      rw [ite_eq_right nup, ite_eq_right ndown]
    rw [hcross]; norm_num
    linarith
  · norm_num at hk
    have bu := hupB.mp (by linarith [hδ.2])
    have al : a.im ≤ 0 := le_of_not_gt (fun h => by linarith [hupA.mpr h, hδ.2])
    have hd := hpos (by linarith)
    have hcross : rayCross a b = 1 := ite_eq_left ⟨al, bu, hd⟩
    rw [hcross]; norm_num; linarith

private def strip (h : ℝ) : Set ℂ := {z | |z.im| < h}

private theorem convex_strip (h : ℝ) : Convex ℝ (strip h) := by
  have hs : strip h = {z : ℂ | -h < z.im} ∩ {z : ℂ | z.im < h} := by
    ext z
    change |z.im| < h ↔ -h < z.im ∧ z.im < h
    exact abs_lt
  rw [hs]
  exact (convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _)

/-- A nonvanishing polynomial on an open convex set has a continuous
    real argument there, obtained as the imaginary part of a logarithm. -/
private theorem convex_argument (p : Polynomial ℂ) {K : Set ℂ} (hK : Convex ℝ K)
    (ho : IsOpen K) (hne : K.Nonempty) (hfree : ∀ z ∈ K, p.eval z ≠ 0) :
    ∃ F : ℂ → ℝ, ContinuousOn F K ∧ ∀ z ∈ K, (F z : Real.Angle) = (p.eval z).arg := by
  let _ := hK.contractibleSpace hne
  have hsc : IsSimplyConnected K := inferInstanceAs (SimplyConnectedSpace K)
  obtain ⟨L, hL, he⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc ho p.continuousOn
    (fun ⟨z, hz, hzero⟩ => hfree z hz hzero)
  refine ⟨fun z => (L z).im, Complex.continuous_im.comp_continuousOn hL, ?_⟩
  intro z hz
  have hez : Complex.exp (L z) = p.eval z := he hz
  rw [← hez, Complex.arg_exp, Real.Angle.coe_toIocMod]

private def edgePoint (u v : ℂ) (t : ℝ) : ℂ := (1-t) • u + t • v

private theorem eval_disk_bound (e : Polynomial ℂ) (c t : ℂ) (ht : ‖t‖ ≤ 1) :
    ‖e.eval t - c‖ ≤ ‖e.coeff 0-c‖ + ∑ k ∈ e.support.erase 0, ‖e.coeff k‖ := by
  have hexp : e.eval t = e.coeff 0 + ∑ k ∈ e.support.erase 0, e.coeff k*t^k := by
    rw [eval_eq_sum, Polynomial.sum]
    by_cases h : 0 ∈ e.support
    · simpa only [pow_zero, mul_one] using
        (Finset.add_sum_erase e.support (fun k => e.coeff k*t^k) h).symm
    · simp [notMem_support_iff.mp h]
  rw [hexp, add_sub_right_comm]
  refine (norm_add_le ..).trans (add_le_add le_rfl ((norm_sum_le ..).trans ?_))
  exact Finset.sum_le_sum fun i _ => by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) ht)

private theorem edge_disk {p : Polynomial ℂ} {u v A B c : ℂ} (hc : EdgeCheck p u v A B c)
    {t : ℝ} (ht : t ∈ Icc 0 1) : ‖p.eval (edgePoint u v t) - c‖ < ‖c‖ := by
  let e := p.comp (C ((u+v)/2) + C ((v-u)/2)*X)
  let s : ℂ := ((2*t-1 : ℝ):ℂ)
  have hs : ‖s‖ ≤ 1 := by
    rw [show ‖s‖ = |2*t-1| from Complex.norm_real _, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have he : e.eval s = p.eval (edgePoint u v t) := by
    simp only [e, eval_comp, eval_add, eval_mul, eval_C, eval_X]
    congr 1
    dsimp [s, edgePoint, Complex.real_smul]; push_cast; ring
  rw [← he]
  exact (eval_disk_bound e c s hs).trans_lt hc.2.2

/-- Subtracting the local edge argument from the global argument leaves
    a constant on the segment, by uniqueness of lifts through ℝ → ℝ/(2πℤ). -/
private theorem edge_increment {p : Polynomial ℂ} {K : Set ℂ} (hK : Convex ℝ K) {u v A B c : ℂ}
    (hu : u ∈ K) (hv : v ∈ K) (hc : EdgeCheck p u v A B c)
    {F : ℂ → ℝ} (hF : ContinuousOn F K)
    (hphase : ∀ z ∈ K, (F z : Real.Angle) = (p.eval z).arg) :
    F v - F u = (p.eval v/c).arg - (p.eval u/c).arg := by
  have hpath : Continuous (edgePoint u v) := by unfold edgePoint; fun_prop
  have hmem (t) (ht : t ∈ Icc (0:ℝ) 1) : edgePoint u v t ∈ K :=
    hK hu hv (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel ..)
  let D (t : ℝ) := F (edgePoint u v t) - (p.eval (edgePoint u v t)/c).arg
  have hcont : ContinuousOn D (Icc 0 1) :=
    (hF.comp hpath.continuousOn hmem).sub (Complex.continuousOn_arg.comp
      ((p.continuous.comp hpath).div_const c).continuousOn
      (fun t ht => Or.inl (disk_re (edge_disk hc ht))))
  have hangle (t) (ht : t ∈ Icc (0:ℝ) 1) : (D t : Real.Angle) = c.arg := by
    obtain ⟨hp, hc'⟩ := disk_ne (edge_disk hc ht)
    dsimp only [D]
    rw [Real.Angle.coe_sub, hphase _ (hmem _ ht), Complex.arg_div_coe_angle hp hc']
    abel
  have he := (AddCircle.isCoveringMap_coe (2*Real.pi)).constOn_of_comp isPreconnected_Icc
    hcont (fun t ht s hs => (hangle t ht).trans (hangle s hs).symm)
    (right_mem_Icc.mpr zero_le_one) (left_mem_Icc.mpr zero_le_one)
  simp [D, edgePoint] at he
  linarith

private theorem crossing_contradiction (p : Polynomial ℂ) {K : Set ℂ}
    (hK : Convex ℝ K) (ho : IsOpen K) (hfree : ∀ z ∈ K, p.eval z ≠ 0)
    (N : ℕ) (v A c : ℕ → ℂ) (hN : 0 < N) (hvN : v N = v 0) (hAN : A N = A 0)
    (hv : ∀ i ≤ N, v i ∈ K)
    (hedges : ∀ i < N, EdgeCheck p (v i) (v (i+1)) (A i) (A (i+1)) (c i))
    (hwind : 0 < ∑ i ∈ Finset.range N, rayCross (A i) (A (i+1))) : False := by
  obtain ⟨F, hF, hphase⟩ := convex_argument p hK ho ⟨v 0, hv 0 hN.le⟩ hfree
  -- The correction from the actual image to the nominal vertex is independent
  -- of which adjacent edge disk is used to compute it.
  let T (i : ℕ) := F (v i) + (A i / p.eval (v i)).arg - argPos (A i)
  have step (i : ℕ) (hi : i < N) :
      T (i+1) - T i = 2*Real.pi*(rayCross (A i) (A (i+1)) : ℝ) := by
    have hc := hedges i hi
    have hactual := edge_increment hK (hv i hi.le) (hv (i+1) hi) hc hF hphase
    have hsrc : ‖p.eval (v i)-c i‖ < ‖c i‖ := by
      simpa [edgePoint] using edge_disk hc (left_mem_Icc.mpr zero_le_one)
    have htgt : ‖p.eval (v (i+1))-c i‖ < ‖c i‖ := by
      simpa [edgePoint] using edge_disk hc (right_mem_Icc.mpr zero_le_one)
    dsimp only [T]
    linarith only [hactual, (disk_turn hsrc hc.1).1, (disk_turn htgt hc.2.1).1,
      (disk_turn hc.1 hc.2.1).1, crossing_turn hc.1 hc.2.1]
  have hsum : (∑ i ∈ Finset.range N, (T (i+1)-T i)) =
      2*Real.pi*((∑ i ∈ Finset.range N, rayCross (A i) (A (i+1)) : ℤ):ℝ) := by
    rw [Int.cast_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => step i (Finset.mem_range.mp hi)
  rw [Finset.sum_range_sub, show T N = T 0 by simp only [T, hvN, hAN], sub_self] at hsum
  exact (mul_pos Real.two_pi_pos (by exact_mod_cast hwind)).ne hsum

end Turan.Polygon

namespace Turan
open Polygon

theorem polygon_forces_zero (p : Polynomial ℂ) (h : ℝ) (check : PolygonCheck p h) :
    ∃ z : ℂ, p.eval z = 0 ∧ |z.im| < h := by
  obtain ⟨N, v, A, c, hN, hvN, hAN, hv, hedges, hwind⟩ := check
  by_contra! hnone
  exact crossing_contradiction p (convex_strip h) (isOpen_lt Complex.continuous_im.abs continuous_const)
    (fun z hz hzero => (hnone z hzero).not_gt hz) N v A c hN hvN hAN hv hedges hwind

/-- The winding certificate localizes a zero to the compact convex set
    containing the chain, including the case of a zero on its boundary. -/
theorem polygon_forces_zero_in_convex_set (p : Polynomial ℂ) (K : Set ℂ) (hK : Convex ℝ K)
    (hc : IsCompact K) (N : ℕ) (v A center : ℕ → ℂ) (hN : 0 < N)
    (hv : v N = v 0) (hA : A N = A 0) (hk : ∀ i ≤ N, v i ∈ K)
    (he : ∀ i < N, EdgeCheck p (v i) (v (i+1)) (A i) (A (i+1)) (center i))
    (hcros : 0 < ∑ i ∈ Finset.range N, rayCross (A i) (A (i+1))) :
    ∃ z ∈ K, p.eval z = 0 := by
  by_contra! hfree
  have hopen : IsOpen {z : ℂ | p.eval z ≠ 0} := isOpen_ne_fun p.continuous continuous_const
  obtain ⟨δ, hδ, hsafe⟩ := hc.exists_thickening_subset_open hopen (fun z hz => hfree z hz)
  exact crossing_contradiction p (hK.thickening δ) Metric.isOpen_thickening
    (fun _ hz => hsafe hz) N v A center hN hv hA
    (fun i hi => Metric.self_subset_thickening hδ K (hk i hi)) he hcros

private theorem affine_chord_in_disk (A B c : ℂ) (t : ℝ) (ht : t ∈ Icc 0 1)
    (hA : ‖A-c‖ < ‖c‖) (hB : ‖B-c‖ < ‖c‖) :
    ‖(1-t) • A + t • B - c‖ < ‖c‖ := by
  have ha : A ∈ Metric.ball c ‖c‖ := by simpa [Metric.mem_ball,dist_eq_norm] using hA
  have hb : B ∈ Metric.ball c ‖c‖ := by simpa [Metric.mem_ball,dist_eq_norm] using hB
  have h := (convex_ball c ‖c‖) ha hb (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  simpa [Metric.mem_ball,dist_eq_norm] using h

theorem nominal_chord_in_edge_disk (p : Polynomial ℂ) (u v A B c : ℂ)
    (hc : EdgeCheck p u v A B c) (t : ℝ) (ht : t ∈ Icc 0 1) :
    ‖(1-t) • A + t • B - c‖ < ‖c‖ ∧
    ‖p.eval ((1-t) • u + t • v) - c‖ < ‖c‖  := by
  exact ⟨affine_chord_in_disk _ _ _ _ ht hc.1 hc.2.1, edge_disk hc ht⟩

theorem box_center_edge_chord {α : Type*} (K : Set α) (x : α) (hx : x ∈ K)
    (p : α → Polynomial ℂ) (u v c : ℂ)
    (hbox : ∀ a ∈ K, ∀ t ∈ Icc (0:ℝ) 1, ‖(p a).eval ((1-t) • u + t • v)-c‖ < ‖c‖) :
    let A := (p x).eval u
    let B := (p x).eval v
    ‖A-c‖ < ‖c‖ ∧ ‖B-c‖ < ‖c‖ ∧
      ∀ t ∈ Icc (0:ℝ) 1, ‖(1-t) • A + t • B - c‖ < ‖c‖  := by
  dsimp only
  have hu : ‖(p x).eval u - c‖ < ‖c‖ := by
    simpa using hbox x hx 0 (left_mem_Icc.mpr zero_le_one)
  have hv : ‖(p x).eval v - c‖ < ‖c‖ := by
    simpa using hbox x hx 1 (right_mem_Icc.mpr zero_le_one)
  exact ⟨hu,hv,fun t ht => affine_chord_in_disk _ _ _ _ ht hu hv⟩

theorem checked_edges_winding_equality (p : Polynomial ℂ) (N : ℕ) (v A c : ℕ → ℂ)
    (hv : v N = v 0) (ha : A N = A 0)
    (he : ∀ i < N, EdgeCheck p (v i) (v (i+1)) (A i) (A (i+1)) (c i)) :
    let angle := fun i (t : ℝ) => (p.eval ((1-t) • v i + t • v (i+1)) / c i).arg
    (∀ i < N, ContinuousOn (angle i) (Icc 0 1)) ∧
    (∑ i ∈ Finset.range N, (angle i 1 - angle i 0)) =
      2*Real.pi*((∑ i ∈ Finset.range N, rayCross (A i) (A (i+1)) : ℤ):ℝ)  := by
  dsimp only
  constructor
  · intro i hi
    apply Complex.continuousOn_arg.comp
    · exact ((p.continuous.comp (show Continuous (edgePoint (v i) (v (i+1))) by
        unfold edgePoint; fun_prop)).div_const (c i)).continuousOn
    · intro t ht
      exact Or.inl (disk_re (edge_disk (he i hi) ht))
  · let T := fun i => argPos (A i) - (A i / p.eval (v i)).arg
    have step (i : ℕ) (hi : i < N) :
        (p.eval (v (i+1)) / c i).arg - (p.eval (v i) / c i).arg =
          (T (i+1)-T i) + 2*Real.pi*(rayCross (A i) (A (i+1)):ℝ) := by
      have h := he i hi
      have hl : ‖p.eval (v i)-c i‖ < ‖c i‖ := by
        simpa [edgePoint] using edge_disk h (left_mem_Icc.mpr zero_le_one)
      have hr : ‖p.eval (v (i+1))-c i‖ < ‖c i‖ := by
        simpa [edgePoint] using edge_disk h (right_mem_Icc.mpr zero_le_one)
      dsimp only [T]
      linarith only [(disk_turn hl h.1).1, (disk_turn hr h.2.1).1,
        (disk_turn h.1 h.2.1).1, crossing_turn h.1 h.2.1]
    simp only [sub_self,zero_smul,one_smul,zero_add,sub_zero,add_zero]
    rw [Int.cast_sum, Finset.mul_sum]
    calc
      _ = ∑ i ∈ Finset.range N, ((T (i+1)-T i) + 2*Real.pi*(rayCross (A i) (A (i+1)):ℝ)) :=
        Finset.sum_congr rfl fun i hi => step i (Finset.mem_range.mp hi)
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_range_sub, show T N = T 0 by simp [T,hv,ha], sub_self,zero_add]

end Turan
