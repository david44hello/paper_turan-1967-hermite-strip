module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.SlotDefs

@[expose] public section

noncomputable section
open Polynomial Filter Metric
open scoped Topology
namespace Turan

private theorem normalized_eval_product (p : Polynomial ℂ) (h₀ : p.eval 0 ≠ 0) (z : ℂ) :
    p.eval z / p.eval 0 = (p.roots.map (fun w => 1 - z/w)).prod := by
  have hp : p ≠ 0 := fun h => h₀ (by simp [h])
  have hsplit := (IsAlgClosed.splits p).eval_eq_prod_roots
  rw [hsplit z, hsplit 0, mul_div_mul_left _ _ (leadingCoeff_ne_zero.mpr hp),
    ← Multiset.prod_map_div]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro w hw
  have hw₀ : w ≠ 0 := by
    rintro rfl
    exact h₀ (isRoot_of_mem_roots hw)
  change (z-w)/(0-w) = 1-z/w
  field_simp
  ring

/-- Adding one factor changes the product error by at most
`(1+d)` times the preceding error plus `d`. -/
private theorem root_product_bound (s : Multiset ℂ) (z : ℂ) (d : ℝ) (hd : 0 ≤ d)
    (h : ∀ w ∈ s, ‖z/w‖ ≤ d) :
    ‖(s.map (fun w => 1-z/w)).prod - 1‖ ≤ (1+d)^s.card - 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons w s ih =>
    let P := (s.map (fun u => 1-z/u)).prod
    have hw := h w (Multiset.mem_cons_self ..)
    have hP : ‖P-1‖ ≤ (1+d)^s.card-1 := ih (fun u hu => h u (Multiset.mem_cons_of_mem hu))
    have hfac : ‖1-z/w‖ ≤ 1+d := (norm_sub_le ..).trans (by rw [norm_one]; linarith)
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    change ‖(1-z/w)*P-1‖ ≤ _
    calc
      _ = ‖(1-z/w)*(P-1)-z/w‖ := by congr 1; ring
      _ ≤ ‖(1-z/w)*(P-1)‖ + ‖z/w‖ := norm_sub_le ..
      _ ≤ (1+d)*((1+d)^s.card-1)+d := by
        rw [norm_mul]
        exact add_le_add (mul_le_mul hfac hP (norm_nonneg _) (by linarith)) hw
      _ = _ := by rw [pow_succ]; ring

theorem bounded_flat_limit (F : ℕ → Polynomial ℂ) (he : escapesDisks F) (B : ℕ)
    (hB : ∀ᶠ j in atTop, (F j).natDegree ≤ B) :
    TendstoLocallyUniformly (fun j z => (F j).eval z / (F j).eval 0) (fun _ => 1) atTop := by
  apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
  intro S hS
  obtain ⟨K, hK, hSK⟩ := hS.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hlim : Tendsto (fun i : ℕ => (1 + K/(i : ℝ))^B - 1) atTop (𝓝 0) := by
    simpa only [add_zero, one_pow, sub_self] using
      (((tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_const_div_atTop_nhds_zero_nat K)).pow B
        |>.sub_const 1)
  obtain ⟨N, hN, hsmall⟩ := ((eventually_gt_atTop (0 : ℕ)).and (hlim.eventually_lt_const hε)).exists
  have hR : 0 < (N : ℝ) := by exact_mod_cast hN
  filter_upwards [he N hR, hB] with j hj hdeg
  intro z hz
  have h₀ : (F j).eval 0 ≠ 0 := hj 0 (by simp)
  have hzK : ‖z‖ ≤ K := by simpa using mem_closedBall.mp (hSK hz)
  have hd : 0 ≤ K/(N : ℝ) := by positivity
  have hquot (w : ℂ) (hw : w ∈ (F j).roots) : ‖z/w‖ ≤ K/(N : ℝ) := by
    have hout : (N : ℝ) < ‖w‖ :=
      lt_of_not_ge (fun h => hj w h (isRoot_of_mem_roots hw))
    rw [norm_div]
    exact div_le_div₀ hK.le hzK hR hout.le
  change dist 1 ((F j).eval z / (F j).eval 0) < ε
  rw [dist_comm, dist_eq_norm, normalized_eval_product _ h₀]
  exact (root_product_bound _ z _ hd hquot).trans_lt <| lt_of_le_of_lt
    (sub_le_sub_right (pow_le_pow_right₀ (by linarith : 1 ≤ 1+K/(N : ℝ))
      ((card_roots' _).trans hdeg)) 1) hsmall

end Turan
