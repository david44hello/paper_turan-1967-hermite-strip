module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Small45Sextic
public import Turan.Small45Product

@[expose] public section

namespace Turan.Small45

/-- The rational model, corrected for the four isolated node positions. -/
theorem factor_bound (w : ℂ) (hw : 17/20 ≤ |w.im|) (l r u v : ℝ)
    (hl : -20.11 < l ∧ l < -20.09) (hr : -1/125000 < r ∧ r < 0)
    (hu : 0.43 < u ∧ u < 0.45) (hv : 2.46 < v ∧ v < 2.48) :
    (‖w-(l:ℂ)‖/‖w-(r:ℂ)‖)^2*(‖w-(u:ℂ)‖/‖w-(v:ℂ)‖) < 240 := by
  let d (s : ℝ) := ‖w-(s:ℂ)‖
  have hd (s : ℝ) : 0 < d s := lt_of_lt_of_le (by norm_num : (0:ℝ) < 17/20)
    (hw.trans (by simpa [d] using Complex.abs_im_le_norm (w-(s:ℂ))))
  have hs (s : ℝ) : (d s)^2 = (w.re-s)^2+w.im^2 := by
    change ‖w-(s:ℂ)‖^2 = _
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply,pow_two]
  have model : (d (-20.10))^2*d 0.44 < 225*(d 0)^2*d 2.47 := by
    apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    simp only [mul_pow,hs,sub_neg_eq_add,sub_zero]
    exact model_sextic _ _ hw
  let k : ℝ := 86/85
  let j : ℝ := 1+1/106250
  have close (s t : ℝ) (h : |s-t| ≤ 0.01) : d s ≤ k*d t := by
    convert real_node_dist_le w s t 0.01 (17/20) (by norm_num) hw h using 1
    norm_num [d,k]
  have hL := close l (-20.10) (abs_le.mpr ⟨by linarith [hl.1],by linarith [hl.2]⟩)
  have hU := close u 0.44 (abs_le.mpr ⟨by linarith [hu.1],by linarith [hu.2]⟩)
  have hV := close 2.47 v (abs_le.mpr ⟨by linarith [hv.2],by linarith [hv.1]⟩)
  have hR : d 0 ≤ j*d r := by
    convert real_node_dist_le w 0 r (1/125000) (17/20) (by norm_num) hw
      (abs_le.mpr ⟨by linarith [hr.2],by linarith [hr.1]⟩) using 1
    norm_num [d,j]
  change (d l/d r)^2*(d u/d v) < 240
  rw [div_pow, div_mul_div_comm]
  apply (div_lt_iff₀ (mul_pos (pow_pos (hd _) _) (hd _))).mpr
  calc
    d l ^ 2 * d u ≤ (k*d (-20.10))^2*(k*d 0.44) := by gcongr
    _ = k^3*(d (-20.10)^2*d 0.44) := by ring
    _ ≤ k^3*(225*d 0^2*d 2.47) := by gcongr
    _ ≤ k^3*(225*(j*d r)^2*(k*d v)) := by gcongr
    _ = (225*k^4*j^2)*(d r^2*d v) := by ring
    _ < 240*(d r^2*d v) := by
      exact mul_lt_mul_of_pos_right (by norm_num [k,j]) (mul_pos (pow_pos (hd _) _) (hd _))

end Turan.Small45
