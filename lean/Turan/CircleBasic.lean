-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.ScaledFamily
import Turan.Circles
import Turan.CircleMinimum
import Turan.RealZeros
import Turan.Rouche

noncomputable section
open Polynomial Metric
open scoped ComplexConjugate
namespace Turan

private def point (x r : ℝ) (v : ℂ) : ℂ := x + r*v

private theorem point_dist (x r : ℝ) (hr : 0 ≤ r) (v : ℂ) :
    ‖point x r v - (x:ℂ)‖ = r*‖v‖ := by
  simp [point, abs_of_nonneg hr]

private theorem jet_eval (j : ℕ) (x r : ℝ) (v : ℂ) :
    (circleJet j x r).eval v = (scaledMode j).eval (point x r v) := by
  simp [circleJet, eval_comp, eval_add, eval_mul, point]

/-- A mode's first coefficient is real because the center and radius are real. -/
private theorem pivot_coeff (j : ℕ) (x r : ℝ) :
    (circlePivot j x r : ℂ) = (circleJet j x r).coeff 1 := by
  have hH (i : ℕ) : (hermite i).map (starRingEnd ℂ) = hermite i := by
    induction i using Nat.twoStepInduction with
    | zero => simp [hermite]
    | one => simp [hermite, Polynomial.map_ofNat]
    | more i ih ih' =>
      rw [hermite]
      simp [nsmul_eq_mul, ih, ih', Polynomial.map_ofNat]
  have hjet : (circleJet j x r).map (starRingEnd ℂ) = circleJet j x r := by
    simp [circleJet, scaledMode, Polynomial.map_comp, hH, map_ofNat]
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff 1) hjet
  exact Complex.conj_eq_iff_re.mp (by simpa only [coeff_map] using hc)

private theorem norm_eval_sum_le (p : Polynomial ℂ) (s : Finset ℕ) (v : ℂ) (hv : ‖v‖ = 1) :
    ‖∑ k ∈ s, p.coeff k*v^k‖ ≤ ∑ k ∈ s, ‖p.coeff k‖ := by
  simpa [norm_mul, norm_pow, hv] using norm_sum_le s (fun k => p.coeff k*v^k)

private theorem mode_bound (j : ℕ) (x r : ℝ) (v : ℂ) (hv : ‖v‖ = 1) :
    ‖(scaledMode j).eval (point x r v)‖ ≤ circleMass j x r := by
  rw [← jet_eval, eval_eq_sum]
  exact norm_eval_sum_le _ _ v hv

private theorem mode_remainder (j : ℕ) (x r : ℝ) (v : ℂ) (hv : ‖v‖ = 1) :
    ‖(scaledMode j).eval (point x r v) - (circlePivot j x r : ℂ)*v‖ ≤
      circleMass j x r - |circlePivot j x r| := by
  let p := circleJet j x r
  have hpivot : ‖p.coeff 1‖ = |circlePivot j x r| := by
    rw [← pivot_coeff]; exact Complex.norm_real _
  rw [← jet_eval, pivot_coeff, ← hpivot]
  change ‖p.eval v - p.coeff 1*v‖ ≤ (∑ k ∈ p.support, ‖p.coeff k‖) - ‖p.coeff 1‖
  by_cases h : 1 ∈ p.support
  · have he := Finset.sum_erase_add p.support (fun k => p.coeff k*v^k) h
    have hn := Finset.sum_erase_add p.support (fun k => ‖p.coeff k‖) h
    simp only [pow_one] at he
    rw [eval_eq_sum, Polynomial.sum, ← he, add_sub_cancel_right, ← hn, add_sub_cancel_right]
    exact norm_eval_sum_le p _ v hv
  · have hz : p.coeff 1 = 0 := notMem_support_iff.mp h
    simpa [hz, eval_eq_sum, Polynomial.sum] using norm_eval_sum_le p p.support v hv

private theorem affine_bound (x r : ℝ) (hr : 0 ≤ r) (v : ℂ) (hv : ‖v‖ = 1) :
    ‖1+2*point x r v‖ ≤ |1+2*x| + 2*r := by
  rw [show 1+2*point x r v = ((1+2*x : ℝ):ℂ) + 2*(r:ℂ)*v by push_cast; unfold point; ring]
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat,
    abs_of_nonneg hr, hv, mul_one] using
    norm_add_le ((1+2*x : ℝ):ℂ) (2*(r:ℂ)*v)

/-- A comparison function with an interior zero must fail strict dominance somewhere on the circle. -/
private theorem disk_boundary_witness (n m : ℕ) (a b : ℂ) (x r : ℝ) (hr : 0 < r)
    (hs : ∀ z ∈ ball (x:ℂ) r, scaledFamily n m a b z ≠ 0)
    (P : ℂ → ℂ) (hP : Differentiable ℂ P) (hz : ∃ v ∈ ball (0:ℂ) 1, P v = 0) :
    ∃ v : ℂ, ‖v‖ = 1 ∧ ‖P v‖ ≤ ‖scaledFamily n m a b (point x r v) - P v‖ := by
  by_contra! h
  let F := fun v => scaledFamily n m a b (point x r v)
  have hF : Differentiable ℂ F := by unfold F scaledFamily point; fun_prop
  obtain ⟨v, hv, hzero⟩ := circle_comparison zero_lt_one hF.differentiableOn hP.differentiableOn hz
    (fun v hv => h v (by simpa using mem_sphere.mp hv))
  apply hs _ _ hzero
  rw [mem_ball, dist_eq_norm, point_dist x r hr.le]
  exact mul_lt_of_lt_one_right hr (by simpa using (mem_ball.mp hv))

private theorem boundary_witness (n m : ℕ) (a b : ℂ) (x r : ℝ) (hr : 0 < r) (ht : r < 87/100)
    (hs : emptyStrip (scaledFamily n m a b) (87/100))
    (P : ℂ → ℂ) (hP : Differentiable ℂ P) (hz : ∃ v ∈ ball (0:ℂ) 1, P v = 0) :
    ∃ v : ℂ, ‖v‖ = 1 ∧ ‖P v‖ ≤ ‖scaledFamily n m a b (point x r v) - P v‖  := by
  apply disk_boundary_witness n m a b x r hr _ P hP hz
  intro z hz
  exact hs z (disk_in_strip _ _ _ _ (by simpa using ht) (ball_subset_closedBall hz))

private theorem scaled_eval (j : ℕ) (z : ℂ) :
    (scaledMode j).eval z = (((128:ℝ)^j : ℝ):ℂ)*(hermite j).eval z := by
  simp [scaledMode, eval_mul]

private theorem bracket_root (j : ℕ) (x r : ℝ) (hr : 0 < r) (hb : bracketed j x r) :
    ∃ v ∈ ball (0:ℂ) 1, (scaledMode j).eval (point x r v) = 0 := by
  simp only [bracketed, scaled_eval, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hb
  have hsign : ((hermite j).eval ((x-r:ℝ):ℂ)).re * ((hermite j).eval ((x+r:ℝ):ℂ)).re < 0 := by
    by_contra! h
    exact hb.not_ge (by
      rw [mul_mul_mul_comm]
      exact mul_nonneg (by positivity) h)
  obtain ⟨y, hy, hzero⟩ := hermite_zero_of_sign_change j (x-r) (x+r) (by linarith) hsign
  refine ⟨((y-x)/r : ℝ), ?_, ?_⟩
  · rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    exact ⟨(lt_div_iff₀ hr).mpr (by linarith [hy.1]), (div_lt_iff₀ hr).mpr (by linarith [hy.2])⟩
  · rw [show point x r (((y-x)/r:ℝ):ℂ) = (y:ℂ) by
          unfold point; norm_cast; field_simp; ring, scaled_eval, hzero, mul_zero]

private theorem endpoint_bound (j : ℕ) (x r : ℝ) (hr : 0 < r) (v : ℂ) (hv : ‖v‖ = 1) :
    circleEndMin j x r ≤ ‖(scaledMode j).eval (point x r v)‖ := by
  apply real_rooted_circle _ _ _ _ hr _ (by rw [point_dist x r hr.le, hv, mul_one])
  intro w hw
  rw [scaled_eval] at hw
  exact (hermite_real_simple j w ((mul_eq_zero.mp hw).resolve_left (by
    exact_mod_cast (show (128:ℝ)^j ≠ 0 by positivity)))).1

private theorem affine_cut (n m : ℕ) (a b : ℂ) (x r : ℝ) (hr : 0 < r) (ht : r < 87/100)
    (hs : emptyStrip (scaledFamily n m a b) (87/100)) (hx : x = -1/2) :
    2*r ≤ ‖a‖*circleMass n x r + ‖b‖*circleMass m x r := by
  have hlin (v : ℂ) : 1+2*point x r v = 2*(r:ℂ)*v := by
    rw [hx]; unfold point; push_cast; ring
  obtain ⟨v, hv, hw⟩ := boundary_witness n m a b x r hr ht hs
    (fun v => 1 + 2*point x r v) (by unfold point; fun_prop)
    ⟨0, mem_ball_self zero_lt_one, by rw [hlin]; ring⟩
  change ‖1+2*point x r v‖ ≤ _ at hw
  rw [show scaledFamily n m a b (point x r v) - (1+2*point x r v) =
       a*(scaledMode n).eval (point x r v) + b*(scaledMode m).eval (point x r v) by
       unfold scaledFamily; ring, hlin] at hw
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    hv, mul_one] at hw
  refine hw.trans ((norm_add_le _ _).trans ?_)
  simp only [norm_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (mode_bound n x r v hv) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left (mode_bound m x r v hv) (norm_nonneg _))

private theorem bracket_cut (n m : ℕ) (a b : ℂ) (x r : ℝ) (hr : 0 < r) (ht : r < 87/100)
    (hs : emptyStrip (scaledFamily n m a b) (87/100)) (hb : bracketed n x r) :
    ‖a‖*circleEndMin n x r ≤ (|1+2*x|+2*r) + ‖b‖*circleMass m x r := by
  obtain ⟨u, hu, hzero⟩ := bracket_root n x r hr hb
  obtain ⟨v, hv, hw⟩ := boundary_witness n m a b x r hr ht hs
    (fun v => a*(scaledMode n).eval (point x r v)) (by unfold point; fun_prop)
    ⟨u, hu, by simp [hzero]⟩
  change ‖a*(scaledMode n).eval (point x r v)‖ ≤ _ at hw
  rw [show scaledFamily n m a b (point x r v) - a*(scaledMode n).eval (point x r v) =
      (1+2*point x r v) + b*(scaledMode m).eval (point x r v) by unfold scaledFamily; ring,
    norm_mul] at hw
  refine (mul_le_mul_of_nonneg_left (endpoint_bound n x r hr v hv) (norm_nonneg a)).trans
    (hw.trans ((norm_add_le _ _).trans ?_))
  rw [norm_mul]
  exact add_le_add (affine_bound x r hr.le v hv)
    (mul_le_mul_of_nonneg_left (mode_bound m x r v hv) (norm_nonneg b))

theorem circle_joint_cut_on_disk (n m : ℕ) (a b : ℂ) (x r s t : ℝ) (hr : 0 < r)
    (hs : ∀ z ∈ ball (x:ℂ) r, scaledFamily n m a b z ≠ 0)
    (horient : 0 ≤ (a*star b).re * circlePivot n x r * circlePivot m x r)
    (hσ : 0 ≤ s) (hτ : 0 ≤ t) (hst : s^2+t^2 ≤ 1) :
    ‖a‖*(s*|circlePivot n x r| - (circleMass n x r - |circlePivot n x r|)) +
    ‖b‖*(t*|circlePivot m x r| - (circleMass m x r - |circlePivot m x r|)) ≤ |1+2*x|+2*r  := by
  let d := circlePivot n x r
  let e := circlePivot m x r
  let L := a*(d:ℂ) + b*(e:ℂ)
  have hproj := circle_coefficient_bound a b d e s t horient hσ hτ hst
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs] at hproj
  obtain ⟨v, hv, hw⟩ := disk_boundary_witness n m a b x r hr hs (fun v => L*v)
    (by fun_prop) ⟨0, mem_ball_self zero_lt_one, mul_zero L⟩
  change ‖L*v‖ ≤ ‖scaledFamily n m a b (point x r v) - L*v‖ at hw
  let R (j : ℕ) := (scaledMode j).eval (point x r v) - (circlePivot j x r:ℂ)*v
  have hid : scaledFamily n m a b (point x r v) - L*v = 1+2*point x r v + a*R n + b*R m := by
    unfold scaledFamily L d e R
    ring
  rw [norm_mul, hv, mul_one, hid] at hw
  have hub : ‖L‖ ≤ |1+2*x|+2*r + ‖a‖*(circleMass n x r - |d|) +
      ‖b‖*(circleMass m x r - |e|) := by
    refine hw.trans ?_
    grw [norm_add_le, norm_add_le]
    simp only [norm_mul]
    exact add_le_add (add_le_add (affine_bound x r hr.le v hv)
      (mul_le_mul_of_nonneg_left (mode_remainder n x r v hv) (norm_nonneg a)))
      (mul_le_mul_of_nonneg_left (mode_remainder m x r v hv) (norm_nonneg b))
  change s*(‖a‖*|d|)+t*(‖b‖*|e|) ≤ ‖L‖ at hproj
  change ‖a‖*(s*|d| - (circleMass n x r - |d|)) + ‖b‖*(t*|e| - (circleMass m x r - |e|)) ≤ _
  linarith only [hproj, hub]

private theorem joint_cut (n m : ℕ) (a b : ℂ) (x r s t : ℝ)
    (hr : 0 < r) (ht : r < 87/100) (hs : emptyStrip (scaledFamily n m a b) (87/100))
    (horient : 0 ≤ (a*star b).re * circlePivot n x r * circlePivot m x r)
    (hσ : 0 ≤ s) (hτ : 0 ≤ t) (hst : s^2+t^2 ≤ 1) :
    ‖a‖*(s*|circlePivot n x r| - (circleMass n x r - |circlePivot n x r|)) +
    ‖b‖*(t*|circlePivot m x r| - (circleMass m x r - |circlePivot m x r|)) ≤ |1+2*x|+2*r := by
  apply circle_joint_cut_on_disk n m a b x r s t hr _ horient hσ hτ hst
  intro z hz
  exact hs z (disk_in_strip _ _ _ _ (by simpa using ht) (ball_subset_closedBall hz))

/-- Every affine, single-mode, or joint first-coefficient circle row gives its claimed cut. -/
theorem circle_basic_cut (w : CircleRow) (n m : ℕ) (a b : ℂ) (sign : ℝ)
    (hs : emptyStrip (scaledFamily n m a b) (87/100)) (hphase : 0 ≤ sign*(a*star b).re)
    (hsign : sign=-1 ∨ sign=1) (hv : w.valid n m sign)
    (hk : w.test=.affine ∨ w.test=.low ∨ w.test=.high ∨ w.test=.joint) :
    w.cut n m ‖a‖ ‖b‖ := by
  rcases hk with h | h | h | h <;> simp only [CircleRow.valid, CircleRow.cut, h] at hv ⊢
  · obtain ⟨hr, ht, hx⟩ := hv.resolve_left (by decide)
    exact affine_cut n m a b w.x w.r hr ht hs hx
  · obtain ⟨hr, ht, hb⟩ := hv.resolve_left (by decide)
    exact bracket_cut n m a b w.x w.r hr ht hs hb
  · obtain ⟨hr, ht, hb⟩ := hv.resolve_left (by decide)
    have hswap : scaledFamily m n b a = scaledFamily n m a b := by
      funext z; unfold scaledFamily; ring
    exact bracket_cut m n b a w.x w.r hr ht (hswap.symm ▸ hs) hb
  · obtain ⟨hr, ht, hst, hde⟩ := hv.resolve_left (by decide)
    apply joint_cut n m a b w.x w.r _ _ hr ht hs _ (by positivity) (by positivity)
    · have hcast : (w.s:ℝ)^2+(w.t:ℝ)^2 ≤ 100 := by exact_mod_cast hst
      linarith only [hcast]
    · have horient := mul_nonneg hphase hde
      rcases hsign with rfl | rfl <;> linarith only [horient]

end Turan
