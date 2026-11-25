-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.SectionTwoNormalForm
import Turan.SectionTwoLimitsDefs
import Turan.SlotDerivatives

noncomputable section
open Polynomial Filter Metric Turan.SectionTwo.Expansion
open scoped Topology BigOperators Classical
namespace Turan.SectionTwo
variable {s : ℕ}

private theorem word_div {ι : Type*} (x y : ℂ) (c : ι → ℂ) (J : ℕ → ℂ) (w : List ι)
    (l : ℕ) (b : ℂ) :
    applyWord x y c J w l / b = applyWord x y c (fun i => J i / b) w l := by
  induction w generalizing l with
  | nil => rfl
  | cons t w ih => simp only [applyWord, ← ih]; ring

private theorem word_limit {ι α : Type*} {L : Filter α} {x y : α → ℂ} {c : α → ι → ℂ}
    {J : α → ℕ → ℂ} {g : ι → ℂ} (w : List ι) (l : ℕ) (v : ℂ)
    (hx : Tendsto x L (𝓝 0)) (hy : Tendsto y L (𝓝 0)) (hc : ∀ t, Tendsto (c · t) L (𝓝 (g t)))
    (hJ : ∀ i, l ≤ i → i ≤ l+2*w.length → Tendsto (J · i) L (𝓝 (v^i))) :
    Tendsto (fun j => applyWord (x j) (y j) (c j) (J j) w l) L
      (𝓝 (v^l * (w.map (fun t => v^2+g t)).prod)) := by
  induction w generalizing l with
  | nil => simpa [applyWord] using hJ l le_rfl (by simp)
  | cons t w ih =>
    simp only [List.length_cons] at hJ
    have h0 := ih l (fun i hlo hhi => hJ i hlo (by omega))
    have h1 := ih (l+1) (fun i hlo hhi => hJ i (by omega) (by omega))
    have h2 := ih (l+2) (fun i hlo hhi => hJ i (by omega) (by omega))
    have hm := ((tendsto_const_nhds (x := (2 : ℂ))).mul hx).mul h1
    have hd := (hc t).sub ((tendsto_const_nhds (x := 2*(l : ℂ))).mul hy)
    convert (h2.sub hm).add (hd.mul h0) using 1
    · rfl
    · congr 1
      simp only [List.map_cons, List.prod_cons, mul_zero, zero_mul, sub_zero, pow_add]
      ring

theorem slot_characteristic_equation (hs : s ∈ Set.Icc 2 4) (k : ℕ → Fin s → ℕ)
    (a : ℕ → Fin s → ℂ) (γ : Fin s → ℝ) (Φ : ℂ → ℂ)
    (hω : Tendsto (fun j => frequency (k j)) atTop atTop)
    (hγ : ∀ v, Tendsto (fun j => lambda (k j v) / topLambda (k j)) atTop (𝓝 (γ v)))
    (he : escapesDisks (fun j => slotSum (k j) (a j)))
    (hQ : ∀ l : ℕ, 1 ≤ l → l ≤ 2*s → TendstoLocallyUniformly
      (fun j => jetRatio (frequency (k j)) (slotSum (k j) (a j)) l) (fun z => (Φ z)^l) atTop) :
    ∀ z : ℂ, (∏ v, ((Φ z)^2 + (γ v : ℂ))) = 0 := by
  intro z
  let F (j : ℕ) := slotSum (k j) (a j)
  let ω (j : ℕ) := frequency (k j)
  let J (j i : ℕ) := jetRatio (ω j) (F j) i z
  have hpos := hω.eventually_gt_atTop 0
  have hi : Tendsto (fun j => (ω j : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_zero, ω] using
      (Complex.continuous_ofReal.tendsto 0).comp (tendsto_inv_atTop_zero.comp hω)
  have hx : Tendsto (fun j => z/(ω j : ℂ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using (tendsto_const_nhds (x := z)).mul hi
  have hy : Tendsto (fun j => (topLambda (k j) : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow, ← Complex.ofReal_pow, ω, frequency_sq, zero_pow (by decide : 2 ≠ 0)] using hi.pow 2
  have hc (v) := (Complex.continuous_ofReal.tendsto (γ v)).comp (hγ v)
  have hj (i) (_ : 0 ≤ i) (hi : i ≤ 0+2*(List.finRange s).length) :
      Tendsto (J · i) atTop (𝓝 ((Φ z)^i)) := by
    cases i with
    | zero =>
      apply tendsto_const_nhds.congr'
      filter_upwards [he (‖z‖+1) (by positivity)] with j h
      simp [J, F, jetRatio, scaledJet, h z (by linarith)]
    | succ i => exact (hQ (i+1) (by omega) (by simpa using hi)).tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ z)
  have hlim := word_limit (List.finRange s) 0 (Φ z) hx hy hc hj
  have hzero : ∀ᶠ j in atTop, applyWord (z/(ω j : ℂ)) (topLambda (k j) : ℂ)⁻¹
      (fun v => ((lambda (k j v) / topLambda (k j) : ℝ) : ℂ)) (J j) (List.finRange s) 0 = 0 := by
    filter_upwards [hpos] with j hj
    unfold J jetRatio
    rw [← word_div, ← word_on_jets (k j) _ (F j) z hj]
    change scaledJet (ω j) (annihilator (k j) (slotSum (k j) (a j))) 0 z / _ = 0
    simp [annihilator_slotSum, scaledJet]
  have h := tendsto_nhds_unique (hlim.congr' hzero) tendsto_const_nhds
  simpa [List.prod_ofFn, ← List.ofFn_id, List.finRange] using h

private theorem power_word (p : Polynomial ℂ) (ω : ℝ) (hω : 0 < ω) (z : ℂ) (d l : ℕ) :
    scaledJet ω (((fun q : Polynomial ℂ => C (2/(ω : ℂ)^2)*EStar q)^[d]) p) l z =
      applyWord (z/(ω : ℂ)) ((ω^2 : ℝ) : ℂ)⁻¹ (fun _ : Unit => 0)
        (fun i => scaledJet ω p i z) (List.replicate d ()) l := by
  induction d generalizing l with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply', List.replicate_succ, applyWord]
    have hform (q : Polynomial ℂ) : C (2/(ω : ℂ)^2)*EStar q = scaledShift (ω^2) 0 q := by
      simp [scaledShift, div_eq_mul_inv, Complex.ofReal_pow, mul_assoc, mul_comm, mul_left_comm, map_ofNat]
    rw [hform, scaledJet_shift _ hω, ih, ih, ih]
    simp

theorem scaled_operator_power_limit (F : ℕ → Polynomial ℂ) (ω : ℕ → ℝ)
    (hω : Tendsto ω atTop atTop) (he : escapesDisks F)
    (hQ : ∀ l : ℕ, 1 ≤ l →
      TendstoLocallyUniformly (fun j => jetRatio (ω j) (F j) l) (fun _ => 0) atTop)
    (d : ℕ) (hd : 1 ≤ d) :
    TendstoLocallyUniformly
      (fun j z => (((fun p : Polynomial ℂ => C (2/(ω j : ℂ)^2)*EStar p)^[d])
        (F j)).eval z / (F j).eval z) (fun _ => 0) atTop := by
  apply (locally_to_const _ _).mpr
  intro z
  let L := (atTop : Filter ℕ) ×ˢ 𝓝 z
  have hpos := hω.eventually_gt_atTop 0
  have hi : Tendsto (fun p : ℕ × ℂ => (ω p.1 : ℂ)⁻¹) L (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_zero] using
      ((Complex.continuous_ofReal.tendsto 0).comp (tendsto_inv_atTop_zero.comp hω)).comp tendsto_fst
  have hx : Tendsto (fun p : ℕ × ℂ => p.2 / (ω p.1 : ℂ)) L (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_snd.mul hi
  have hy : Tendsto (fun p : ℕ × ℂ => ((ω p.1 ^ 2 : ℝ) : ℂ)⁻¹) L (𝓝 0) := by
    simpa only [Complex.ofReal_pow, inv_pow, zero_pow (by decide : 2 ≠ 0)] using hi.pow 2
  let J (p : ℕ × ℂ) (i : ℕ) := jetRatio (ω p.1) (F p.1) i p.2
  have hJ (i : ℕ) (_ : 0 ≤ i) (_ : i ≤ 0+2*(List.replicate d ()).length) :
      Tendsto (J · i) L (𝓝 ((0 : ℂ)^i)) := by
    cases i with
    | zero =>
      apply tendsto_const_nhds.congr'
      filter_upwards [tendsto_fst.eventually (he (‖z‖+1) (by positivity)),
        tendsto_snd.eventually (Metric.ball_mem_nhds z zero_lt_one)] with p hp hball
      have hnorm := norm_sub_norm_le p.2 z
      have hd := mem_ball_iff_norm.mp hball
      have hne := hp p.2 (by linarith)
      simp [J, jetRatio, scaledJet, hne]
    | succ i => simpa [J,L] using (locally_to_const _ _).mp (hQ _ (by omega)) z
  have h := word_limit (List.replicate d ()) 0 (0 : ℂ) hx hy
    (fun _ : Unit => (tendsto_const_nhds (x := (0 : ℂ)) (f := L))) hJ
  simp only [pow_zero, zero_pow (by decide : 2 ≠ 0), zero_add, List.map_replicate,
    List.prod_replicate, zero_pow (by omega : d ≠ 0), one_mul] at h
  refine h.congr' ?_
  filter_upwards [tendsto_fst.eventually hpos] with p hp
  unfold J jetRatio
  rw [← word_div, ← power_word _ _ hp]
  simp [scaledJet]

end Turan.SectionTwo
