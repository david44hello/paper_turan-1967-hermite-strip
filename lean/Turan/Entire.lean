module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Rouche
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Complex.RemovableSingularity

@[expose] public section

noncomputable section
open Metric Polynomial Set
namespace Turan

/-- On the unit circle, deleting the dominant term leaves a sum of norm at most s. -/
private theorem series_boundary (f : ℂ → ℂ) (a : ℕ → ℂ) (l : ℕ)
    (ha : ∀ z : ℂ, HasSum (fun k => a k*z^k) (f z)) (s : ℝ)
    (hs : HasSum (fun k => if k=l then 0 else ‖a k‖) s) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖f z - a l*z^l‖ ≤ s := by
  have h := (ha z).sub (hasSum_ite_eq l (a l*z^l))
  apply h.norm_le_of_bounded hs
  intro k
  by_cases hk : k=l
  · subst k; simp
  · simp [hk, norm_pow, hz]

private theorem unit_disk_roots (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hb : ∀ z ∈ sphere (0:ℂ) 1, f z ≠ 0) :
    ∃ roots : Multiset ℂ, ∀ z : ℂ, (roots.count z : ℕ∞) =
      if ‖z‖ < 1 then analyticOrderAt f z else 0 := by
  classical
  let K := closedBall (0:ℂ) 1
  have h₁ : f 1 ≠ 0 := hb 1 (by simp)
  have hK : AnalyticOnNhd ℂ f K := fun z _ => hf.analyticAt z
  have hfin := (isCompact_closedBall (0:ℂ) 1).finite_sdiff_of_mem_codiscreteWithin
    (hK.preimage_zero_mem_codiscreteWithin h₁ (by simp [K]) (isConnected_closedBall zero_le_one))
  let S := hfin.toFinset
  have hS (z : ℂ) : z ∈ S ↔ ‖z‖ < 1 ∧ f z = 0 := by
    change z ∈ hfin.toFinset ↔ _
    simp only [Set.Finite.mem_toFinset, Set.mem_sdiff, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff, not_not, mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨hz, he⟩
      exact ⟨hz.lt_of_ne (fun h => hb z (by simpa using h) he), he⟩
    · exact fun h => ⟨h.1.le, h.2⟩
  have hfiniteOrder (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
    intro h
    have hf0 := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z hf.analyticAt).mp h
    exact h₁ (congrFun hf0 1)
  refine ⟨∑ w ∈ S, Multiset.replicate (analyticOrderNatAt f w) w, ?_⟩
  intro z
  simp only [Multiset.count_sum', Multiset.count_replicate, Finset.sum_ite_eq']
  by_cases hz : z ∈ S
  · simp [hz, (hS z).mp hz |>.1, hfiniteOrder]
  · simp only [hz, ↓reduceIte, Nat.cast_zero]
    split_ifs with hin
    · exact ((hf.analyticAt z).analyticOrderAt_eq_zero.mpr (fun he => hz ((hS z).mpr ⟨hin, he⟩))).symm
    · rfl

private theorem log_deriv_integrable (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hb : ∀ z ∈ sphere (0:ℂ) 1, f z ≠ 0) :
    CircleIntegrable (fun z => deriv f z / f z) 0 1 :=
  ((continuous_iff_continuousAt.mpr (fun z => (hf.analyticAt z).deriv.continuousAt)).continuousOn.div
    hf.continuous.continuousOn hb).circleIntegrable zero_le_one

/-- Remove each occurrence of a zero using the entire divided difference at that zero. -/
private theorem integral_counts (roots : Multiset ℂ) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hb : ∀ z ∈ sphere (0:ℂ) 1, f z ≠ 0)
    (hc : ∀ z : ℂ, (roots.count z : ℕ∞) = if ‖z‖ < 1 then analyticOrderAt f z else 0) :
    (∮ z in C(0, 1), deriv f z / f z) = 2*Real.pi*Complex.I*(roots.card : ℂ) := by
  classical
  induction roots using Multiset.induction_on generalizing f with
  | empty =>
    have hn (z : ℂ) (hz : z ∈ closedBall (0:ℂ) 1) : f z ≠ 0 := by
      rcases lt_or_eq_of_le (mem_closedBall.mp hz) with hin | heq
      · apply (hf.analyticAt z).analyticOrderAt_eq_zero.mp
        simpa [show ‖z‖ < 1 by simpa using hin] using (hc z).symm
      · exact hb z heq
    have hd : DifferentiableOn ℂ (fun z => deriv f z / f z) (closedBall (0:ℂ) 1) :=
      (show Differentiable ℂ (deriv f) from fun z => (hf.analyticAt z).deriv.differentiableAt).differentiableOn.div
        hf.differentiableOn hn
    simpa using (hd.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero zero_le_one
  | cons w roots ih =>
    have hmem : ‖w‖ < 1 := by
      by_contra h
      simpa [h] using hc w
    have hfw : f w = 0 := by
      apply (hf.analyticAt w).analyticOrderAt_ne_zero.mp
      rw [← show ((w ::ₘ roots).count w : ℕ∞) = analyticOrderAt f w by simpa [hmem] using hc w]
      simp
    let g := dslope f w
    have hg : Differentiable ℂ g := differentiableOn_univ.mp
      ((Complex.differentiableOn_dslope (by simp : (Set.univ : Set ℂ) ∈ nhds w)).mpr hf.differentiableOn)
    have hfac : f = (fun z => z-w)*g := by
      funext z
      simpa [g, hfw, smul_eq_mul] using (sub_smul_dslope f w z).symm
    have hgb (z : ℂ) (hz : z ∈ sphere (0:ℂ) 1) : g z ≠ 0 :=
      right_ne_zero_of_mul (show (z-w)*g z ≠ 0 by simpa only [hfac, Pi.mul_apply] using hb z hz)
    have hcount (z : ℂ) : (roots.count z : ℕ∞) = if ‖z‖ < 1 then analyticOrderAt g z else 0 := by
      have h := hc z
      rw [hfac, analyticOrderAt_mul (f := fun z => z-w) (by fun_prop) (hg.analyticAt z)] at h
      rcases eq_or_ne z w with rfl | hzw
      · rw [ite_eq_left hmem]
        apply ENat.add_left_injective_of_ne_top (n := 1) (by simp)
        simpa [hmem, add_comm] using h
      · simpa only [Multiset.count_cons_of_ne hzw, analyticOrderAt_id_sub_const_of_ne hzw,
          zero_add] using h
    have hw : w ∈ ball (0:ℂ) 1 := by simpa using hmem
    calc
      (∮ z in C(0, 1), deriv f z / f z) =
          ∮ z in C(0, 1), (z-w)⁻¹ + deriv g z / g z := by
        apply circleIntegral.integral_congr zero_le_one
        intro z hz
        have hzw : z-w ≠ 0 := sub_ne_zero.mpr fun he => by
          subst z
          have : ‖w‖ = 1 := by simpa using hz
          exact hmem.ne this
        have hder := ((hasDerivAt_id z).sub_const w).mul (hg z).hasDerivAt
        change HasDerivAt ((fun z => z-w)*g) (1*g z+(z-w)*deriv g z) z at hder
        change deriv f z / f z = (z-w)⁻¹ + deriv g z / g z
        rw [hfac, hder.deriv]
        change (1*g z+(z-w)*deriv g z) / ((z-w)*g z) = _
        field_simp [hzw, hgb z hz]
      _ = (∮ z in C(0, 1), (z-w)⁻¹) + ∮ z in C(0, 1), deriv g z / g z :=
        circleIntegral.integral_add (by simpa [circleIntegrable_sub_inv_iff] using hmem.ne)
          (log_deriv_integrable g hg hgb)
      _ = _ := by
        rw [circleIntegral.integral_sub_inv_of_mem_ball hw, ih g hg hgb hcount]
        simp [mul_add, add_comm]

/-- On the boundary the quotient lies in the domain of the principal logarithm. -/
private theorem integral_compare (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hdom : ∀ z ∈ sphere (0:ℂ) 1, ‖f z-g z‖ < ‖g z‖) :
    (∮ z in C(0, 1), deriv f z / f z) = ∮ z in C(0, 1), deriv g z / g z := by
  have hgb (z : ℂ) (hz : z ∈ sphere (0:ℂ) 1) : g z ≠ 0 :=
    norm_pos_iff.mp ((norm_nonneg _).trans_lt (hdom z hz))
  have hfb (z : ℂ) (hz : z ∈ sphere (0:ℂ) 1) : f z ≠ 0 := by
    intro h
    simpa [h] using hdom z hz
  apply sub_eq_zero.mp
  rw [← circleIntegral.integral_sub (log_deriv_integrable f hf hfb) (log_deriv_integrable g hg hgb)]
  apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt
    (f := fun z => Complex.log (f z / g z)) zero_le_one
  intro z hz
  have hg0 := hgb z hz
  have hf0 := hfb z hz
  have hslit : f z / g z ∈ Complex.slitPlane := by
    apply Complex.ball_one_subset_slitPlane
    rw [mem_ball, dist_eq_norm, show f z / g z - 1 = (f z - g z) / g z by
      rw [sub_div, div_self hg0], norm_div, div_lt_one (norm_pos_iff.mpr hg0)]
    exact hdom z hz
  have hlog := (Complex.hasDerivAt_log hslit).comp z
    (((hf z).hasDerivAt).div (hg z).hasDerivAt hg0)
  apply hlog.hasDerivWithinAt.congr_deriv
  field_simp [hg0, hf0]

/-- A dominant Taylor coefficient counts all zeros in the open unit disk with their analytic multiplicities. -/
theorem dominant_entire_term (f : ℂ → ℂ) (a : ℕ → ℂ) (l : ℕ) (hl : 1 ≤ l)
    (hf : Differentiable ℂ f) (ha : ∀ z : ℂ, HasSum (fun k => a k*z^k) (f z))
    (s : ℝ) (hs : HasSum (fun k => if k=l then 0 else ‖a k‖) s) (hd : s < ‖a l‖) :
    ∃ roots : Multiset ℂ, roots.card = l ∧ ∀ z : ℂ,
      (roots.count z : ℕ∞) = if ‖z‖ < 1 then analyticOrderAt f z else 0 := by
  let p := monomial l (a l)
  have hdom (z : ℂ) (hz : z ∈ sphere (0:ℂ) 1) : ‖f z-p.eval z‖ < ‖p.eval z‖ := by
    have hnorm : ‖z‖ = 1 := by simpa using hz
    simpa only [p, eval_monomial, norm_mul, norm_pow, hnorm, one_pow, mul_one] using
      (series_boundary f a l ha s hs z hnorm).trans_lt hd
  have hb (z : ℂ) (hz : z ∈ sphere (0:ℂ) 1) : f z ≠ 0 := by
    intro h
    simpa [h] using hdom z hz
  have hal : a l ≠ 0 := by
    intro h
    have := hdom 1 (by simp)
    simp [p, h] at this
    exact (norm_nonneg _).not_gt this
  obtain ⟨roots, hc⟩ := unit_disk_roots f hf hb
  refine ⟨roots, ?_, hc⟩
  have he := integral_compare f (fun z => p.eval z) hf p.differentiable hdom
  simp only [funext (fun z => (p.hasDerivAt z).deriv)] at he
  rw [integral_counts roots f hf hb hc, polynomial_argument_principle p 0 1 zero_lt_one
    (fun z hz => norm_pos_iff.mp ((norm_nonneg _).trans_lt (hdom z hz)))] at he
  have hcount : (p.roots.filter (fun z => dist z 0 < 1)).card = l := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hl)
    simp [p, roots_monomial hal, Multiset.filter_nsmul, Multiset.filter_singleton]
  rw [hcount] at he
  have hperiod : (2*Real.pi*Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  exact_mod_cast mul_left_cancel₀ hperiod he

end Turan
