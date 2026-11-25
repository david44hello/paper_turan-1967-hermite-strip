-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.QuinticTrig

noncomputable section
namespace Turan

private structure InRectangle (w : ℂ) : Prop where
  re_lt : |w.re| < 4 / 5
  im_le : 87 / 100 ≤ w.im
  im_lt : w.im < 1

private theorem angleDen_pos (X s : ℝ) (w : ℂ)
    (hs₀ : 1/2 < s) (hs₁ : s < 511/1000) (hh : 87/100 ≤ |w.im|) :
    0 < (w.re-X)^2 + w.im^2 - s^2 := by
  have hs2 := (sq_lt_sq₀ (by linarith : 0 ≤ s) (by norm_num)).2 hs₁
  have hy2 := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 87/100) (abs_nonneg _)).2 hh
  rw [sq_abs] at hy2
  nlinarith only [hs2, hy2, sq_nonneg (w.re-X)]

/-- Step 3. Inverting the angle inequality confines an upper root to a rectangle. -/
private theorem angle_rectangle (X s : ℝ) (w : ℂ) (hX : |X| < 1/2)
    (hs₀ : 1/2 < s) (hs₁ : s < 511/1000) (hh : 87/100 ≤ |w.im|)
    (hangle : Real.arctan (45/28) < qAngle X s w) : InRectangle w := by
  have hD := angleDen_pos X s w hs₀ hs₁ hh
  have ht := (lt_div_iff₀ hD).mp (Real.arctan_lt_arctan_iff.mp hangle)
  have hy : 0 < w.im := by
    have hnum : 0 < 2*s*w.im := lt_trans (mul_pos (by norm_num) hD) ht
    exact pos_of_mul_pos_right hnum (by linarith)
  rw [abs_of_pos hy] at hh
  have hs2 := (sq_lt_sq₀ (by linarith : 0 ≤ s) (by norm_num)).2 hs₁
  have hsy := mul_lt_mul_of_pos_right hs₁ hy
  have hdist : (w.re-X)^2 < (3/10 : ℝ)^2 := by
    nlinarith only [ht, hsy, hs2, hh, sq_nonneg (w.im-87/100)]
  have hx := abs_lt.mp (abs_lt_of_sq_lt_sq hdist (by norm_num))
  refine ⟨abs_lt.mpr ⟨?_, ?_⟩, hh, ?_⟩
  · linarith only [hx.1, (abs_lt.mp hX).1]
  · linarith only [hx.2, (abs_lt.mp hX).2]
  · nlinarith only [ht, hs2, hsy, sq_nonneg (w.re-X), sq_nonneg (w.im-1)]

private theorem square_bounds (w : ℂ) (A B : ℝ) (hx : |w.re| < A) (hy : |w.im| < B) :
    (w^2).re < A^2 ∧ |(w^2).im| < 2*A*B := by
  have hx2 := (sq_lt_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hx.le)).2 hx
  rw [sq_abs] at hx2
  have hxy := mul_lt_mul_of_nonneg hx hy (abs_nonneg _) (abs_nonneg _)
  constructor
  · simp only [pow_two, Complex.mul_re]
    nlinarith only [hx2, sq_nonneg w.im]
  · rw [show (w^2).im = 2*(w.re*w.im) by simp [pow_two, Complex.mul_im]; ring,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul]
    linarith only [hxy]

private theorem InRectangle.im_abs_lt {w : ℂ} (hw : InRectangle w) : |w.im| < 1 := by
  rw [abs_of_nonneg (by linarith only [hw.im_le])]
  exact hw.im_lt

/-- Step 4. The discriminant of the remaining pair bounds its vertical separation. -/
private theorem vertical_separation (a b c u v : ℂ)
    (ha : InRectangle a) (hb : InRectangle b) (hc : InRectangle c)
    (hz : a+b+c+u+v = 0) (hz2 : a^2+b^2+c^2+u^2+v^2 = 10) :
    |u.im-v.im| < 4 := by
  have hpair : u+v = -(a+b+c) := by linear_combination hz
  have hd : (u-v)^2 = 20-2*(a^2+b^2+c^2)-(a+b+c)^2 := by
    calc
      _ = 2*(u^2+v^2)-(u+v)^2 := by ring
      _ = _ := by rw [hpair]; linear_combination 2*hz2
  obtain ⟨ar, ai⟩ := square_bounds a _ _ ha.re_lt ha.im_abs_lt
  obtain ⟨br, bi⟩ := square_bounds b _ _ hb.re_lt hb.im_abs_lt
  obtain ⟨cr, ci⟩ := square_bounds c _ _ hc.re_lt hc.im_abs_lt
  have hx : |(a+b+c).re| < 12/5 := by
    simp only [Complex.add_re]
    linarith only [abs_add_le (a.re+b.re) c.re, abs_add_le a.re b.re,
      ha.re_lt, hb.re_lt, hc.re_lt]
  have hy : |(a+b+c).im| < 3 := by
    simp only [Complex.add_im]
    linarith only [abs_add_le (a.im+b.im) c.im, abs_add_le a.im b.im,
      ha.im_abs_lt, hb.im_abs_lt, hc.im_abs_lt]
  obtain ⟨sr, si⟩ := square_bounds (a+b+c) _ _ hx hy
  have hdr := congrArg Complex.re hd
  have hdi := congrArg Complex.im hd
  simp only [Complex.sub_re, Complex.mul_re, show (20 : ℂ).re = 20 from rfl,
    show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl,
    zero_mul, sub_zero, Complex.add_re] at hdr
  simp only [Complex.sub_im, Complex.mul_im, show (20 : ℂ).im = 0 from rfl,
    show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl,
    zero_mul, add_zero, Complex.add_im] at hdi
  have hR : 10 < ((u-v)^2).re := by linarith only [ar, br, cr, sr, hdr]
  have hI : |((u-v)^2).im| < 24 := by
    obtain ⟨aiLo, aiHi⟩ := abs_lt.mp ai
    obtain ⟨biLo, biHi⟩ := abs_lt.mp bi
    obtain ⟨ciLo, ciHi⟩ := abs_lt.mp ci
    obtain ⟨siLo, siHi⟩ := abs_lt.mp si
    exact abs_lt.mpr ⟨by linarith only [hdi, aiHi, biHi, ciHi, siHi],
      by linarith only [hdi, aiLo, biLo, ciLo, siLo]⟩
  simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.sub_im] at hR
  have hdx : 3 < |u.re-v.re| := by
    apply (sq_lt_sq₀ (by norm_num) (abs_nonneg _)).mp
    rw [sq_abs]
    nlinarith only [hR, sq_nonneg (u.im-v.im)]
  rw [show ((u-v)^2).im = 2*((u.re-v.re)*(u.im-v.im)) by
    simp [pow_two, Complex.mul_im]; ring,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul] at hI
  nlinarith only [hI, mul_le_mul_of_nonneg_right hdx.le (abs_nonneg (u.im-v.im))]

private structure InLowerBox (w : ℂ) : Prop where
  re_lt : |w.re| < 9/2
  im_lo : -(213/100) < w.im
  im_hi : w.im ≤ -(87/100)

/-- The imaginary moment puts both remaining roots below the axis. Their combined
height then bounds the real second moment. -/
private theorem lower_boxes (a b c u v : ℂ)
    (ha : InRectangle a) (hb : InRectangle b) (hc : InRectangle c)
    (hu : 87/100 ≤ |u.im|) (hv : 87/100 ≤ |v.im|)
    (hz : a+b+c+u+v = 0) (hz2 : a^2+b^2+c^2+u^2+v^2 = 10) :
    InLowerBox u ∧ InLowerBox v := by
  have hsep := abs_lt.mp (vertical_separation a b c u v ha hb hc hz hz2)
  have him := congrArg Complex.im hz
  simp only [Complex.add_im, Complex.zero_im] at him
  have hu0 : u.im < 0 := by
    by_contra! h
    rw [abs_of_nonneg h] at hu
    linarith only [ha.im_le, hb.im_le, hc.im_le, hu, him, hsep.2]
  have hv0 : v.im < 0 := by
    by_contra! h
    rw [abs_of_nonneg h] at hv
    linarith only [ha.im_le, hb.im_le, hc.im_le, hv, him, hsep.1]
  rw [abs_of_neg hu0] at hu
  rw [abs_of_neg hv0] at hv
  have hheight : -3 < u.im+v.im := by linarith only [him, ha.im_lt, hb.im_lt, hc.im_lt]
  have hulo : -(213/100) < u.im := by linarith only [hheight, hv]
  have hvlo : -(213/100) < v.im := by linarith only [hheight, hu]
  have hlower₂ : u.im^2+v.im^2 < (213/100)*3 := by
    nlinarith only [mul_lt_mul_of_neg_right hulo hu0, mul_lt_mul_of_neg_right hvlo hv0,
      hheight]
  have hre := congrArg Complex.re hz2
  simp only [Complex.add_re, pow_two, Complex.mul_re, show (10 : ℂ).re = 10 from rfl] at hre
  have hreal₂ : u.re^2+v.re^2 < 20 := by
    nlinarith only [hre, hlower₂, (sq_lt_one_iff_abs_lt_one _).2 ha.im_abs_lt,
      (sq_lt_one_iff_abs_lt_one _).2 hb.im_abs_lt, (sq_lt_one_iff_abs_lt_one _).2 hc.im_abs_lt,
      sq_nonneg a.re, sq_nonneg b.re, sq_nonneg c.re]
  constructor
  · refine ⟨abs_lt_of_sq_lt_sq ?_ (by norm_num), hulo, by linarith only [hu]⟩
    nlinarith only [hreal₂, sq_nonneg v.re]
  · refine ⟨abs_lt_of_sq_lt_sq ?_ (by norm_num), hvlo, by linarith only [hv]⟩
    nlinarith only [hreal₂, sq_nonneg u.re]

private theorem lower_angle (X s : ℝ) (w : ℂ) (hX : |X| < 1/2)
    (hs₀ : 1/2 < s) (hs₁ : s < 511/1000) (hh : 87/100 ≤ |w.im|)
    (hw : InLowerBox w) : qAngle X s w < -Real.arctan (1/35) := by
  have hdist : (w.re-X)^2 < (5 : ℝ)^2 := by
    obtain ⟨hxlo, hxhi⟩ := abs_lt.mp hX
    obtain ⟨hrlo, hrhi⟩ := abs_lt.mp hw.re_lt
    exact sq_lt_sq' (by linarith only [hrlo, hxhi]) (by linarith only [hrhi, hxlo])
  have hy2 : w.im^2 < (213/100 : ℝ)^2 :=
    sq_lt_sq' hw.im_lo (by linarith only [hw.im_hi])
  rw [qAngle, ← Real.arctan_neg, Real.arctan_lt_arctan_iff, div_lt_iff₀ (angleDen_pos X s w hs₀ hs₁ hh)]
  nlinarith only [hdist, hy2, hw.im_hi, sq_nonneg s,
    mul_lt_mul_of_neg_right hs₀ (show w.im < 0 by linarith only [hw.im_hi])]

/-- Steps 3–6 of the quintic strip argument. A triple carrying more than π forces
the remaining two signed angles to bring the total strictly below π. -/
theorem quintic_angle_contradiction (X s : ℝ) (z : Fin 5 → ℂ)
    (hX : |X| < 1/2) (hs₀ : 1/2 < s) (hs₁ : s < 511/1000)
    (hh : ∀ i, 87/100 ≤ |(z i).im|) (hz : ∑ i, z i = 0) (hz2 : ∑ i, z i ^ 2 = 10)
    (hsort : Antitone (fun i => qAngle X s (z i)))
    (hsum : Real.pi ≤ ∑ i, qAngle X s (z i))
    (htop : Real.pi < qAngle X s (z 0) + qAngle X s (z 1) + qAngle X s (z 2)) :
    False := by
  have hcap (i : Fin 5) : qAngle X s (z i) < Real.arctan (9/5) :=
    (abs_lt.mp (qAngle_abs_lt X s (z i) hs₀ hs₁ (hh i))).2
  have hthird : Real.arctan (45/28) < qAngle X s (z 2) := by
    rw [quintic_rectangle_angle]
    linarith only [htop, hcap 0, hcap 1]
  have hrect (i : Fin 5) (hi : i ≤ 2) : InRectangle (z i) :=
    angle_rectangle X s (z i) hX hs₀ hs₁ (hh i) (hthird.trans_le (hsort hi))
  simp only [Fin.sum_univ_ofNat] at hz hz2 hsum
  obtain ⟨hu, hv⟩ := lower_boxes _ _ _ _ _ (hrect 0 (by decide)) (hrect 1 (by decide))
    (hrect 2 le_rfl) (hh 3) (hh 4) hz hz2
  linarith only [hsum, hcap 0, hcap 1, hcap 2, quintic_triple_angle,
    lower_angle X s (z 3) hX hs₀ hs₁ (hh 3) hu,
    lower_angle X s (z 4) hX hs₀ hs₁ (hh 4) hv]

end Turan
