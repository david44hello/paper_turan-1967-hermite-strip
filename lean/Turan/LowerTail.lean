-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.LargeCircle
import Turan.LowerComparison
import Turan.Trinomial
import Turan.Recover
import Turan.TailUpper
import Turan.Vertical

noncomputable section
open Metric
namespace Turan

theorem large_mode_small_coefficient (n m : ℕ) (hm : 450 ≤ m) (hn : 2 ≤ n)
    (hhalf : 2*n ≤ m) (a b : ℂ) (hs : emptyStrip (normalizedFamily n m a b) (87/100)) :
    ‖b‖ ≤ 20*Real.sqrt m*Real.exp (-(197/1000)*(m:ℝ))*(1+‖a‖) := by
  obtain ⟨x, hlo, hhi, hx, hbound⟩ := large_mode_circle m hm
  let M := Real.sqrt (m:ℝ)
  let E := 20*M*Real.exp (-(197/1000)*(m:ℝ))
  have hm' : (450:ℝ) ≤ m := by exact_mod_cast hm
  have hM : 0 < M := Real.sqrt_pos.mpr (by linarith)
  have hM20 : 20 ≤ M := by nlinarith [Real.sq_sqrt (show 0 ≤ (m:ℝ) by positivity), hM.le]
  have hr : 0 < 1/M := by positivity
  have psiDiff (j : ℕ) : Differentiable ℂ (psi j) := (hermite j).differentiable.div_const _
  by_contra! hb
  have dom (z : ℂ) (hz : z ∈ sphere (x:ℂ) (1/M)) :
      ‖normalizedFamily n m a b z - b*psi m z‖ < ‖b*psi m z‖ := by
    obtain ⟨hnorm, hbase⟩ := large_mode_comparisons n m hm hhalf x hlo hhi hbound z
      (by simpa only [mem_sphere, dist_eq_norm] using hz)
    have hpos : 0 < ‖psi m z‖ := by
      by_contra! he
      rw [le_antisymm he (norm_nonneg _), mul_zero] at hbase
      exact (norm_nonneg _).not_gt hbase
    change E*(1+‖a‖) < ‖b‖ at hb
    simp only [normalizedFamily, add_sub_cancel_right, norm_mul]
    have hb' := mul_lt_mul_of_pos_right hb hpos
    have ha' := mul_le_mul_of_nonneg_left hnorm.le (norm_nonneg a)
    calc
      _ ≤ ‖1+2*z‖ + ‖a*psi n z‖ := norm_add_le _ _
      _ < _ := by rw [norm_mul]; dsimp [E,M] at hb'; nlinarith only [hbase, ha', hb']
  obtain ⟨z, hz, hzero⟩ := circle_comparison (F := normalizedFamily n m a b)
    (P := fun z => b*psi m z) hr (by unfold normalizedFamily; fun_prop (disch := solve_by_elim))
    ((psiDiff m).const_mul b).differentiableOn
    ⟨(x:ℂ), mem_ball_self hr, by simp [hx]⟩ dom
  apply (hs z ?_) hzero
  apply disk_in_strip _ _ _ _ _ (ball_subset_closedBall hz)
  simp only [Complex.ofReal_im, abs_zero, zero_add]
  apply (div_lt_iff₀ hM).mpr
  linarith

theorem large_lower_index_gap (check : TrinomialDiskCheck) (n m : ℕ) (hm : 450 ≤ m)
    (hn : 2 ≤ n) (hhalf : 2*n ≤ m) (a b : ℂ) :
    ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| < 87/100 := by
  let A := scaleCoeff n a
  let B := scaleCoeff m b
  let F := normalizedFamily n m A B
  by_contra! outside
  have hs : emptyStrip F (87/100) := by
    intro z hz hzero
    exact (not_le_of_gt hz) (outside z (by simpa [F,A,B,rescale_family] using hzero))
  obtain ⟨c,hc,hre,him⟩ := lemma_ten_given check n hn A
  obtain ⟨hnz, _, ha⟩ := lemma_eleven n m hm hn hhalf A B c hs hc hre him
  have hF : 0 < ‖F c‖ := norm_pos_iff.mpr hnz
  have hfact : F c = B*psi m c := by simp [F, normalizedFamily, hc]
  have hB := large_mode_small_coefficient n m hm hn hhalf A B hs
  have hψ := lemma_twelve m (by omega) c hre him
  have hm' : (450:ℝ) ≤ m := by exact_mod_cast hm
  have hmp : 0 < (m:ℝ) := by linarith
  have hpow : Real.sqrt m * (m:ℝ)^((9:ℝ)/2) = (m:ℝ)^5 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hmp]
    norm_num
  have hh := mul_le_mul hB hψ (norm_nonneg _) (by positivity)
  change 1+‖A‖ < 110000*(m:ℝ)^((9:ℝ)/2) * ‖F c‖ at ha
  have hbig := mul_lt_mul_of_pos_right ha (show
      0 < 20*Real.sqrt m*Real.exp (-(197/1000)*(m:ℝ)) *
        Real.exp (8+76/100*Real.sqrt (2*(m:ℝ))) by positivity)
  have hdec := mul_lt_mul_of_pos_right (tail_decay m hm') hF
  rw [← norm_mul, ← hfact] at hh
  rw [show 8+76/100*Real.sqrt (2*(m:ℝ))-197/1000*m =
      -(197/1000)*(m:ℝ)+(8+76/100*Real.sqrt (2*(m:ℝ))) by ring, Real.exp_add, ← hpow] at hdec
  nlinarith only [hdec, hh, hbig]

theorem lemma_eight_given (check : TrinomialDiskCheck) (n m : ℕ) (hn : 2 ≤ n)
    (hm : 450 ≤ m) (hnm : n < m) (a b : ℂ) :
    ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| < 87/100 := by
  rcases le_total (2*n) m with hlo | hhi
  · exact large_lower_index_gap check n m hm hn hlo a b
  · exact large_upper_index_gap n m hm hhi hnm a b

end Turan
