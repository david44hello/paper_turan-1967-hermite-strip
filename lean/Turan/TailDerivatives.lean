-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.TailGrowth
import Turan.TailLog

namespace Turan

theorem lemma_fourteen (n m : ℕ) (hm : 450 ≤ m) (hhalf : m ≤ 2*n) (hnm : n < m)
    (a b : ℂ) (hs : emptyStrip (normalizedFamily n m a b) (87/100))
    (z : ℂ) (hz : |z.im| ≤ 7/11) (l : ℕ) (hl : 1 ≤ l) (hl' : l ≤ 4) :
    ‖iteratedDeriv l (normalizedFamily n m a b) z / normalizedFamily n m a b z‖ ≤
      (11 * omega m z)^l := by
  have hΩ : 30 ≤ omega m z := by
    unfold omega
    apply Real.le_sqrt_of_sq_le
    have : (450:ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [sq_nonneg z.re]
  have hΩ₀ : 0 < omega m z := by linarith
  obtain ⟨M,hM,hB,w,hw,hdouble⟩ := tailGrowth_doubling n m hm hhalf hnm a b hs z hz
  apply tailLog_deriv_bound _ hΩ₀ hM _ hB (by simpa [Metric.mem_closedBall,dist_eq_norm] using hw)
    (by convert hdouble using 1 <;> norm_num) l hl hl'
  · unfold normalizedFamily psi
    fun_prop
  · intro v hv
    apply hs
    have hnorm : ‖v-z‖ ≤ 7 / omega m z := by simpa [Metric.mem_closedBall,dist_eq_norm] using hv
    have hab := (Complex.abs_im_le_norm (v-z)).trans hnorm
    rw [Complex.sub_im] at hab
    have hrs : (7:ℝ) / omega m z ≤ 7 / 30 := by gcongr
    have ht := abs_add_le (v.im-z.im) z.im
    rw [sub_add_cancel] at ht
    linarith

end Turan
