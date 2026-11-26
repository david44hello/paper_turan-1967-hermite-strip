module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.UpperTailRealEndpoints
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology
namespace Turan.UpperTailReal

theorem compare_j (m n : ℝ) (hm : 450 ≤ m) (hn : n ∈ Icc (m/2) (m-1)) :
    StrictMonoOn lhs (Icc n m) ∧ StrictAntiOn (rhs m n) (Icc n m) ∧
    (rhs m n n < lhs n → rhs m n m < lhs m) := by
  obtain ⟨hlo, hhi⟩ := hn
  have hnpos : 0 < n := by linarith
  have hgap : 0 < m-n := by linarith
  have hmpos : 0 < m := by linarith
  have hnum : 0 < 50000*m^2 := by positivity
  have hleft : StrictMonoOn lhs (Icc n m) := by
    intro x hx y _ hxy
    apply sub_lt_sub_right
    apply mul_lt_mul_of_pos_left _ (by norm_num)
    exact Real.sqrt_lt_sqrt (by linarith [hx.1]) (by linarith)
  have hright : StrictAntiOn (rhs m n) (Icc n m) := by
    intro x hx y hy hxy
    have hxpos := hnpos.trans_le hx.1
    have hypos := hnpos.trans_le hy.1
    apply Real.log_lt_log (div_pos hnum (mul_pos hypos hgap))
    exact div_lt_div_of_pos_left hnum (mul_pos hxpos hgap) (mul_lt_mul_of_pos_right hxy hgap)
  have hnm : n ≤ m := by linarith
  exact ⟨hleft, hright, fun h => (hright.antitoneOn (left_mem_Icc.mpr hnm)
    (right_mem_Icc.mpr hnm) hnm).trans_lt (h.trans_le (hleft.monotoneOn
      (left_mem_Icc.mpr hnm) (right_mem_Icc.mpr hnm) hnm))⟩

private theorem sqrt_linear (x c : ℝ) (hc : 0 < 2*x-c) :
    HasDerivAt (fun t : ℝ => Real.sqrt (2*t-c)) (1/Real.sqrt (2*x-c)) x := by
  apply ((((hasDerivAt_id x).const_mul 2).sub_const c).sqrt hc.ne').congr_deriv
  dsimp
  ring

private def slope (m x : ℝ) := 0.608/Real.sqrt (2*x-11.25) + 1/x - 1/(m-x)

/-- Locally split the logarithm into its two variable factors. The open
interval also gives the first derivative on a neighborhood of either endpoint. -/
private theorem margin_first (m x : ℝ) (hx : 6 < x) (hxm : x < m) :
    HasDerivAt (margin m) (slope m x) x := by
  have hxpos : 0 < x := by linarith
  have hmpos : 0 < m := hxpos.trans hxm
  have hrad := sqrt_linear x 11.25 (by linarith)
  have hbase := ((hrad.const_mul 0.608).sub_const 0.315).sub_const (Real.log (50000*m^2))
  have hd := (hbase.add (Real.hasDerivAt_log hxpos.ne')).add
    (((hasDerivAt_id x).const_sub m).log (sub_ne_zero.mpr hxm.ne'))
  apply (hd.congr_deriv (show _ = slope m x by dsimp [slope]; ring)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx hxm] with t ht
  have htpos : 0 < t := by linarith [ht.1]
  have hgap : 0 < m-t := sub_pos.mpr ht.2
  simp only [margin, lhs, rhs, Real.log_div (by positivity : 50000*m^2 ≠ 0) (mul_pos htpos hgap).ne',
    Real.log_mul htpos.ne' hgap.ne', Pi.add_apply, id_eq]
  ring

theorem margin_second (m n : ℝ) (hm : 450 ≤ m) (hn : n ∈ Icc (m/2) (m-1)) :
    let d₂ := -0.608 / (Real.sqrt (2*n-11.25))^3 - 1/n^2 - 1/(m-n)^2
    HasDerivAt (deriv (margin m)) d₂ n ∧ d₂ < 0 := by
  dsimp only
  obtain ⟨hlo, hhi⟩ := hn
  have hn6 : 6 < n := by linarith
  have hnpos : 0 < n := by linarith
  have hgap : 0 < m-n := by linarith
  have hrad : 0 < 2*n-11.25 := by linarith
  have hs := Real.sqrt_pos.mpr hrad
  constructor
  · have d₁ := (hasDerivAt_const n (0.608:ℝ)).div (sqrt_linear n 11.25 hrad) hs.ne'
    have d₂ := (hasDerivAt_const n (1:ℝ)).div (hasDerivAt_id n) hnpos.ne'
    have d₃ := (hasDerivAt_const n (1:ℝ)).div ((hasDerivAt_id n).const_sub m) hgap.ne'
    apply (((d₁.add d₂).sub d₃).congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [Ioo_mem_nhds hn6 (sub_pos.mp hgap)] with t ht
      exact (margin_first m t ht.1 ht.2).deriv
    · dsimp
      field_simp [hs.ne', hnpos.ne', hgap.ne']
      ring
  · have hneg : -0.608 / (Real.sqrt (2*n-11.25))^3 < 0 := div_neg_of_neg_of_pos (by norm_num) (by positivity)
    linarith only [hneg, show 0 ≤ 1/n^2 by positivity, show 0 ≤ 1/(m-n)^2 by positivity]

theorem minimum_at_an_endpoint (m : ℝ) (hm : 450 ≤ m) :
    StrictConcaveOn ℝ (Icc (m/2) (m-1)) (margin m) ∧
    IsLeast (margin m '' Icc (m/2) (m-1)) (min (margin m (m/2)) (margin m (m-1))) := by
  have hc : StrictConcaveOn ℝ (Icc (m/2) (m-1)) (margin m) := by
    apply strictConcaveOn_of_deriv2_neg' (convex_Icc ..)
    · intro x hx
      exact (margin_first m x (by linarith [hx.1]) (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      obtain ⟨hd, hneg⟩ := margin_second m x hm hx
      exact hd.deriv.trans_lt hneg
  have hle : m/2 ≤ m-1 := by linarith
  have hl := left_mem_Icc.mpr hle
  have hr := right_mem_Icc.mpr hle
  refine ⟨hc, ?_, ?_⟩
  · rcases le_total (margin m (m/2)) (margin m (m-1)) with h | h
    · exact ⟨_, hl, (min_eq_left h).symm⟩
    · exact ⟨_, hr, (min_eq_right h).symm⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hc.concaveOn.min_le_of_mem_Icc hl hr hx

theorem endpoint_derivatives (m : ℝ) (hm : 450 ≤ m) :
    let L := 0.304 / Real.sqrt (m-11.25)
    let R := 0.608 / Real.sqrt (2*m-13.25) - 1/m
    HasDerivAt (fun t => margin t (t/2)) L m ∧ 0 < L ∧
    HasDerivAt rightMinorant R m ∧ 0 < R ∧
    discrim (0.369664 : ℝ) (-2) 13.25 < 0 ∧ 0 < 0.369664*m^2-2*m+13.25 := by
  dsimp only
  have hmpos : 0 < m := by linarith
  have h₁ : 0 < m-11.25 := by linarith
  have h₂ : 0 < 2*m-13.25 := by linarith
  have hq : 0 < 0.369664*m^2-2*m+13.25 := by
    nlinarith only [hm, mul_nonneg (sub_nonneg.mpr hm) hmpos.le]
  refine ⟨?_, by positivity, ?_, ?_, by norm_num [discrim], hq⟩
  · have hd := (((((hasDerivAt_id m).sub_const 11.25).sqrt h₁.ne').const_mul 0.608).sub_const
      0.315).sub_const (Real.log 200000)
    apply (hd.congr_deriv (by dsimp; ring)).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hmpos] with t ht using margin_half_eq t ht.ne'
  · have hd := (((sqrt_linear m 13.25 h₂).const_mul 0.608).sub_const 0.315).sub
      (((hasDerivAt_id m).const_mul 50200).log (by dsimp; positivity))
    apply hd.congr_deriv
    dsimp
    ring
  · apply sub_pos.mpr
    apply (div_lt_div_iff₀ hmpos (Real.sqrt_pos.mpr h₂)).mpr
    rw [one_mul]
    exact (Real.sqrt_lt h₂.le (by positivity)).mpr (by nlinarith only [hq])

theorem endpoint_persistence :
    StrictMonoOn (fun m => margin m (m/2)) (Ici 450) ∧
    StrictMonoOn rightMinorant (Ici 450) := by
  constructor
  · apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · exact fun m hm => (endpoint_derivatives m hm).1.continuousAt.continuousWithinAt
    · intro m hm
      obtain ⟨hd, hpos, _⟩ := endpoint_derivatives m (interior_subset hm)
      exact hpos.trans_eq hd.deriv.symm
  · apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · exact fun m hm => (endpoint_derivatives m hm).2.2.1.continuousAt.continuousWithinAt
    · intro m hm
      obtain ⟨_, _, hd, hpos, _⟩ := endpoint_derivatives m (interior_subset hm)
      exact hpos.trans_eq hd.deriv.symm

theorem global_minimum :
    (450, 225) ∈ domain ∧
    IsLeast ((fun p : ℝ × ℝ => margin p.1 p.2) '' domain) (margin 450 225) ∧
    0.214 < margin 450 225 := by
  have hdom : (450, 225) ∈ domain := by norm_num [domain]
  obtain ⟨hlog, _, hrad, hlog', hdiff, hupper⟩ := left_endpoint 450 le_rfl
  norm_num1 at hlog
  have hcorner : 0.214 < margin 450 225 := by rw [margin, hlog]; linarith
  have hsep : margin 450 225 < rightMinorant 450 := by
    obtain ⟨_, _, _, _, h₁, h₂, _⟩ := right_endpoint 450 le_rfl
    rw [show rightMinorant 450 = lhs 449 - Real.log (50200*450) by norm_num [rightMinorant, lhs]]
    exact hupper.trans ((by norm_num : (0.215:ℝ) < 17.7902-16.9331).trans (sub_lt_sub h₁ h₂))
  refine ⟨hdom, ⟨⟨(450,225), hdom, rfl⟩, ?_⟩, hcorner⟩
  rintro _ ⟨⟨m,n⟩, ⟨hm,hlo,hhi⟩, rfl⟩
  have hleft := endpoint_persistence.1.monotoneOn (self_mem_Ici : (450:ℝ) ∈ Ici 450) hm hm
  have hright := endpoint_persistence.2.monotoneOn (self_mem_Ici : (450:ℝ) ∈ Ici 450) hm hm
  norm_num1 at hleft
  exact (le_min hleft (hsep.le.trans (hright.trans (right_endpoint m hm).2.2.2.1))).trans
    ((minimum_at_an_endpoint m hm).2.2 ⟨n, ⟨hlo, hhi⟩, rfl⟩)

theorem margin_pos (m n : ℝ) (hm : 450 ≤ m) (hn : n ∈ Icc (m/2) (m-1)) :
    0 < margin m n := by
  have h := global_minimum
  exact ((by norm_num : (0:ℝ) < 0.214).trans h.2.2).trans_le
    (h.2.1.2 ⟨(m,n), ⟨hm,hn⟩, rfl⟩)

end Turan.UpperTailReal
