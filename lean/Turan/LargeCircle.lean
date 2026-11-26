module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.LargeCircleEnergy
public import Turan.LargeCircleSine
public import Turan.CircleMinimum

@[expose] public section

open Set
namespace Turan

/-- Apply sine comparison in either direction from a real zero. -/
private theorem endpoint_lower (m : ℕ) (x d : ℝ) (hd : d ≠ 0) (hz : psi m x = 0)
    (hslope : 1 / 4 < |(deriv (phi m) x).re|)
    (hq : ∀ t ∈ Icc 0 1, (2 * (m : ℝ) + 1 - (x + d*t)^2) * d^2 ≤ 1/4) :
    |d| / 5 < ‖phi m ((x + d : ℝ) : ℂ)‖ := by
  let y (u : ℝ) := (phi m u).re
  let v (u : ℝ) := (deriv (phi m) u).re
  let D := d * v x
  have hD : D ≠ 0 := mul_ne_zero hd (abs_pos.mp (lt_trans (by norm_num) hslope))
  let U (t : ℝ) := y (x + d*t) / D
  let V (t : ℝ) := v (x + d*t) * d / D
  obtain ⟨hy, hv⟩ := largeCircle_real_ode m
  have hlin (t : ℝ) : HasDerivAt (fun r => x + d*r) d t := by
    simpa using ((hasDerivAt_id t).const_mul d).const_add x
  have hU (t : ℝ) : HasDerivAt U (V t) t :=
    (((hy _).comp t (hlin t)).div_const D)
  have hV (t : ℝ) : HasDerivAt V (-((2*(m:ℝ)+1-(x+d*t)^2)*d^2) * U t) t := by
    convert ((((hv _).comp t (hlin t)).mul_const d).div_const D) using 1
    dsimp [U, y]
    ring
  have hu0 : U 0 = 0 := by simp [U, y, phi, hz]
  have hv0 : V 0 = 1 := by simpa [V, D, mul_comm] using div_self hD
  have hsin := largeCircle_sine hU hV hu0 hv0 hq
  have hs : 4 / 5 < 2 * Real.sin (1/2) := by
    linarith [Real.sin_gt_sub_cube (by norm_num : (0 : ℝ) < 1/2)]
  have hb : 4/5 < |U 1| := (hs.trans_le hsin).trans_le (le_abs_self _)
  have hvx : 1/4 < |v x| := hslope
  have hprod := mul_lt_mul_of_pos_right hb (abs_pos.mpr hD)
  have hid : U 1 * D = y (x+d) := by simp [U, hD]
  rw [← abs_mul, hid] at hprod
  have hDabs : |D| = |d| * |v x| := abs_mul _ _
  rw [hDabs] at hprod
  apply lt_of_lt_of_le _ (Complex.abs_re_le_norm _)
  change |d| / 5 < |y (x + d)|
  nlinarith only [hprod, mul_lt_mul_of_pos_left hvx (abs_pos.mpr hd)]

theorem large_mode_circle (m : ℕ) (hm : 450 ≤ m) :
    ∃ x : ℝ, Real.sqrt (9*(m:ℝ)/5) ≤ x ∧
      x ≤ Real.sqrt (9*(m:ℝ)/5) + 3*Real.pi/Real.sqrt m ∧ psi m x = 0 ∧
      ∀ z : ℂ, ‖z - (x:ℂ)‖ = 1/Real.sqrt m → 1/(5*Real.sqrt m) < ‖phi m z‖ := by
  let s := Real.sqrt (m : ℝ)
  let a := Real.sqrt (9 * (m : ℝ) / 5)
  have hM : (450 : ℝ) ≤ m := by exact_mod_cast hm
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs2 : s^2 = (m : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a^2 = 9 * (m : ℝ) / 5 := Real.sq_sqrt (by positivity)
  have haLo : (4/3) * s ≤ a := (sq_le_sq₀ (by positivity) ha).mp (by nlinarith only [hs2, ha2, hM])
  have haHi : a ≤ (27/20) * s := (sq_le_sq₀ ha (by positivity)).mp (by nlinarith only [hs2, ha2, hM])
  have hw : 3 * Real.pi / s ≤ s / 45 := (div_le_iff₀ hs).mpr (by nlinarith [Real.pi_lt_d2])
  have hQ (t : ℝ) (ht : t ∈ Icc a (a + 3 * Real.pi / s)) :
      (m : ℝ) / 9 < 2 * (m : ℝ) + 1 - t^2 := by
    have ht0 := ha.trans ht.1
    have ht1 : t ≤ (27/20 + 1/45) * s := by linarith [ht.2]
    have ht2 := (sq_le_sq₀ ht0 (by positivity)).mpr ht1
    nlinarith only [hs2, hM, ht2]
  have hwidth : Real.pi / (s / 3) = 3 * Real.pi / s := by ring
  obtain ⟨x, hx, hz⟩ := hermite_sturm_interval m a (s / 3) (by positivity) (fun t ht => by
    rw [hwidth] at ht
    have h := hQ t (Ioo_subset_Icc_self ht)
    nlinarith only [h, hs2])
  rw [hwidth] at hx
  have hsl := largeCircle_slope m hm x (ha.trans hx.1.le) (hQ x (Ioo_subset_Icc_self hx)) hz
  have hr : 0 < 1 / s := by positivity
  have hrHi : 1 / s ≤ s / 450 := (div_le_iff₀ hs).mpr (by nlinarith only [hM, hs2])
  have endpoints (d : ℝ) (hd : |d| = 1 / s) : 1/(5*s) < ‖phi m ((x+d : ℝ) : ℂ)‖ := by
    have hd0 := abs_pos.mp (hd.symm ▸ hr)
    have hd2 : (m : ℝ) * d^2 = 1 := by
      rw [← hs2, ← sq_abs d, hd]
      field_simp
    have bound (t : ℝ) (ht : t ∈ Icc 0 1) :
        (2*(m:ℝ)+1-(x+d*t)^2)*d^2 ≤ 1/4 := by
      have hdt : |d*t| ≤ 1/s := by
        rw [abs_mul, hd, abs_of_nonneg ht.1]
        exact mul_le_of_le_one_right hr.le ht.2
      have hlo : (133/100)*s ≤ x+d*t := by linarith [hx.1, neg_le_of_abs_le hdt]
      have hsq := (sq_le_sq₀ (by positivity) ((by positivity : 0 ≤ (133/100)*s).trans hlo)).mpr hlo
      have hcoef : 2*(m:ℝ)+1-(x+d*t)^2 ≤ m/4 := by nlinarith only [hM, hs2, hsq]
      nlinarith only [mul_le_mul_of_nonneg_right hcoef (sq_nonneg d), hd2]
    have h := endpoint_lower m x d hd0 hz hsl bound
    rwa [hd, show (1/s)/5 = 1/(5*s) by ring] at h
  refine ⟨x, hx.1.le, hx.2.le, hz, fun z hz' => ?_⟩
  let p := Polynomial.C ((Real.sqrt (2^m * (m.factorial : ℝ)) : ℂ)⁻¹) * hermite m
  have hp (w : ℂ) : p.eval w = psi m w := by simp [p, psi, div_eq_inv_mul]
  have hmin := real_rooted_weighted_circle p (fun w hw => (psi_real_simple m w (hp w ▸ hw)).1)
    x (1/s) hr z hz'
  dsimp only at hmin
  simp only [hp] at hmin
  change min ‖phi m ((x - 1 / s : ℝ) : ℂ)‖ ‖phi m ((x + 1 / s : ℝ) : ℂ)‖ ≤ ‖phi m z‖ at hmin
  apply lt_of_lt_of_le (lt_min ?_ ?_) hmin
  · simpa only [← sub_eq_add_neg] using endpoints (-(1/s)) (by rw [abs_neg, abs_of_pos hr])
  · exact endpoints (1/s) (abs_of_pos hr)

end Turan
