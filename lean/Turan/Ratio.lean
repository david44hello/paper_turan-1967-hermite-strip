module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.RatioTail
public import Turan.ChartReduction

@[expose] public section

noncomputable section
open Polynomial Metric
namespace Turan.Ratio

/-- On the high disk the retained monomial strictly dominates the other ten
terms, both analytic remainders, and the gauged affine term. -/
private theorem high_root (i j : ℕ) (χ t : ℂ) (x r W : ℝ) (k : ℕ)
    (hr : 0 < r) (hs : r < 87/100) (hk : 1 ≤ k) (hk' : k ≤ 10)
    (hi : circleQ i x (2*r) ≤ 36) (hj : circleQ j x (2*r) ≤ 36) (ht : ‖t‖ ≤ W)
    (cert : let c := fun l => gaugedJet i x r l + χ*gaugedJet j x r l
      (∑ l ∈ (Finset.range 11).erase k, ‖c l‖) + omittedTail i x r + ‖χ‖*omittedTail j x r +
        W*(|1+2*x|+2*r)*2^(⌈3*(|x| *r+r^2/2)/2⌉ : ℤ) < ‖c k‖) :
    ∃ z : ℂ, (chartPoly (ratioMode i) (ratioMode j) χ t).eval z = 0 ∧ |z.im| < 87/100 := by
  let c (l : ℕ) := gaugedJet i x r l + χ*gaugedJet j x r l
  let F (v : ℂ) := weight x r v * (chartPoly (ratioMode i) (ratioMode j) χ t).eval (point x r v)
  let partialSum (d : ℕ) (v : ℂ) := ∑ l ∈ Finset.range 11, gaugedJet d x r l*v^l
  have dom (v : ℂ) (hv : v ∈ sphere (0:ℂ) 1) : ‖F v - c k*v^k‖ < ‖c k*v^k‖ := by
    have hu : ‖v‖ = 1 := by simpa using mem_sphere.mp hv
    let rest := ∑ l ∈ (Finset.range 11).erase k, c l*v^l
    have he : rest + c k*v^k = partialSum i v + χ*partialSum j v := by
      rw [show rest + c k*v^k = ∑ l ∈ Finset.range 11, c l*v^l from
        Finset.sum_erase_add _ _ (Finset.mem_range.mpr (by omega))]
      simp [c, partialSum, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
    have hrest : ‖rest‖ ≤ ∑ l ∈ (Finset.range 11).erase k, ‖c l‖ := by
      simpa [rest, norm_mul, norm_pow, hu] using
        norm_sum_le ((Finset.range 11).erase k) (fun l => c l*v^l)
    let E (d : ℕ) := mode d x r v - partialSum d v
    let A := weight x r v * (1+2*point x r v)
    have hdecomp : F v - c k*v^k = rest + E i + χ*E j + t*A := by
      simp only [F, chartPoly, eval_add, eval_mul, eval_C, eval_one, eval_ofNat, eval_X, E, A, mode]
      linear_combination -he
    have hsum : ‖rest + E i + χ*E j + t*A‖ ≤ ‖rest‖+‖E i‖+‖χ*E j‖+‖t*A‖ :=
      (norm_add_le ..).trans (add_le_add
        ((norm_add_le ..).trans (add_le_add (norm_add_le ..) le_rfl)) le_rfl)
    rw [hdecomp, norm_mul (c k), norm_pow, hu, one_pow, mul_one]
    apply hsum.trans_lt
    rw [norm_mul, norm_mul]
    apply lt_of_le_of_lt _ cert
    rw [mul_assoc W]
    exact add_le_add (add_le_add (add_le_add hrest (mode_tail _ _ _ hr hi _ hu))
      (mul_le_mul_of_nonneg_left (mode_tail _ _ _ hr hj _ hu) (norm_nonneg χ)))
      (mul_le_mul ht (affine_bound _ _ hr _ hu) (norm_nonneg _) ((norm_nonneg t).trans ht))
  obtain ⟨v, hv, hzero⟩ := circle_comparison zero_lt_one
    (F := F) (P := fun v => c k*v^k)
    (by unfold F weight point; fun_prop) (by fun_prop)
    ⟨0, mem_ball_self zero_lt_one, by simp [zero_pow (by omega : k ≠ 0)]⟩ dom
  have hz := (mul_eq_zero.mp hzero).resolve_left (Complex.exp_ne_zero _)
  have hdis : point x r v ∈ closedBall (x:ℂ) r := by
    rw [mem_closedBall, dist_eq_norm]
    simpa [point, norm_mul, abs_of_pos hr] using
      mul_le_of_le_one_right hr.le (mem_ball_zero_iff.mp hv).le
  exact ⟨_, hz, disk_in_strip _ _ _ _ (by simpa using hs) hdis⟩

theorem chart_upper (n m i j : ℕ) (check : RatioCertificate n m)
    (hij : (i=n ∧ j=m) ∨ (i=m ∧ j=n)) (χ t : ℂ) (hχ : ‖χ‖ ≤ 1) (him : 0 ≤ χ.im) :
    ∃ z : ℂ, (chartPoly (ratioMode i) (ratioMode j) χ t).eval z = 0 ∧ |z.im| < 87/100 := by
  obtain ⟨X₀, R, U, k, hR, hU, hk, hk', hs, hs₀, hi, hj, cert⟩ := check i j hij χ hχ him
  let x : ℝ := X₀/256
  let r : ℝ := R/256
  let r₀ : ℝ := U/256
  by_contra! hfree
  have hcap := affine_chart_cap (ratioMode i) (ratioMode j) χ t r₀
    (by dsimp [r₀]; positivity) hs₀ (fun z hz hzero => (hfree z hzero).not_gt hz)
  obtain ⟨z, hz, hzi⟩ := high_root i j χ t x r _ k (by dsimp [r]; positivity)
    hs hk hk' hi hj hcap cert
  exact (hfree z hz).not_gt hzi

end Turan.Ratio

namespace Turan

/-- The pointwise upper-half-disk certificate covers both orders of the modes
and every pair of complex coefficients. -/
theorem ratio_certificate_gap (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m)
    (check : RatioCertificate n m) (a b : ℂ) :
    ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| < 87/100 := by
  apply high_chart_reduction n m (ratioMode n) (ratioMode m) (Ratio.modeScale n)
    (Ratio.modeScale m) (Ratio.scale_ne n) (Ratio.scale_ne m) (Ratio.ratioMode_eq n)
    (Ratio.ratioMode_eq m) _ a b
  intro U V hUV χ κ hχ him
  rcases hUV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Ratio.chart_upper n m n m check (.inl ⟨rfl,rfl⟩) χ κ hχ him
  · exact Ratio.chart_upper n m m n check (.inr ⟨rfl,rfl⟩) χ κ hχ him

end Turan
