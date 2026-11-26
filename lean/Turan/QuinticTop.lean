module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.QuinticAngle
public import Mathlib.Tactic

@[expose] public section

namespace Turan

private lemma sum_shifted_product (f g : Fin 4 → ℝ) (a b : ℝ) :
    ∑ i, (f i + a) * (g i + b) =
      (∑ i, f i * g i) + (∑ i, f i) * b + a * (∑ i, g i) + 4*a*b := by
  simp only [add_mul, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- Centering the four upper coordinates gives the projection estimate for the
real part `t` of the fifth root, whose imaginary part is `-Y`. -/
private lemma fifth_real_sq (x y : Fin 4 → ℝ) (t Y : ℝ)
    (hx : ∑ i, x i = -t) (hy : ∑ i, y i = Y) (hY : 0 < Y)
    (hy₀ : ∀ i, 0 ≤ y i) (hxy : ∑ i, x i * y i = t*Y)
    (hnorm : (∑ i, x i ^ 2) + t^2 = 10 + (∑ i, y i ^ 2) + Y^2) :
    t^2 ≤ 3 + 3/5 * ∑ i, y i ^ 2 := by
  let S := ∑ i, y i ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg (y i))
  have hSY : S ≤ Y^2 := hy ▸ Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hy₀ i)
  have hdot : ∑ i, (x i + t/4) * (y i + (-Y/4)) = 5*t*Y/4 := by
    rw [sum_shifted_product, hx, hy, hxy]
    ring
  have hxx : ∑ i, (x i + t/4)^2 = 10 + S + Y^2 - 5*t^2/4 := by
    simp_rw [pow_two, sum_shifted_product, hx, ← sq]
    linarith only [hnorm]
  have hyy : ∑ i, (y i + (-Y/4))^2 = S - Y^2/4 := by
    simp_rw [pow_two, sum_shifted_product, hy, ← sq]
    dsimp only [S]
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => x i + t/4) (fun i => y i + (-Y/4))
  rw [hdot, hxx, hyy] at hcs
  apply (mul_le_mul_iff_of_pos_right (show 0 < S + Y^2 by positivity)).mp
  nlinarith only [hcs, mul_nonneg (sub_nonneg.mpr hSY)
    (show 0 ≤ 25 + S + Y^2 by positivity)]

private lemma four_upper_tail (X s : ℝ) (z : Fin 5 → ℂ)
    (hX : |X| < 1/2) (hs₀ : 1/2 < s) (hs₁ : s < 511/1000)
    (hz : ∑ i, z i = 0) (hz2 : ∑ i, z i ^ 2 = 10)
    (hupper : ∀ i : Fin 4, 0 < (z i.castSucc).im)
    (hsort : Antitone (fun i => qAngle X s (z i)))
    (hD : ∀ i, 0 < ((z i).re-X)^2 + (z i).im^2 - s^2) :
    qAngle X s (z 3) + qAngle X s (z 4) < 0 := by
  let x (i : Fin 4) := (z i.castSucc).re
  let y (i : Fin 4) := (z i.castSucc).im
  let t := (z 4).re
  let Y := -(z 4).im
  let S := ∑ i, y i ^ 2
  let D (i : Fin 5) := ((z i).re-X)^2 + (z i).im^2 - s^2
  rw [Fin.sum_univ_castSucc] at hz hz2
  have hxz := congrArg Complex.re hz
  have hyz := congrArg Complex.im hz
  simp only [Complex.add_re, Complex.re_sum, Complex.zero_re] at hxz
  simp only [Complex.add_im, Complex.im_sum, Complex.zero_im] at hyz
  have hx : ∑ i, x i = -t := eq_neg_of_add_eq_zero_left hxz
  have hy : ∑ i, y i = Y := eq_neg_of_add_eq_zero_left hyz
  have hY : 0 < Y := hy ▸ Finset.sum_pos (fun i _ => hupper i) Finset.univ_nonempty
  have hre := congrArg Complex.re hz2
  have him := congrArg Complex.im hz2
  have sqRe (w : ℂ) : (w^2).re = w.re^2 - w.im^2 := by rw [pow_two, Complex.mul_re]; ring
  have sqIm (w : ℂ) : (w^2).im = w.re*w.im + w.re*w.im := by rw [pow_two, Complex.mul_im]; ring
  simp only [Complex.add_re, Complex.re_sum, sqRe, Finset.sum_sub_distrib,
    show (10 : ℂ).re = 10 from rfl] at hre
  simp only [Complex.add_im, Complex.im_sum, sqIm, Finset.sum_add_distrib,
    show (10 : ℂ).im = 0 from rfl] at him
  rw [show Fin.last 4 = (4 : Fin 5) from rfl] at hre him
  have hnorm : (∑ i, x i ^ 2) + t^2 = 10 + S + Y^2 := by
    dsimp only [x, t, S, y, Y]
    linarith only [hre]
  have hxy : ∑ i, x i * y i = t * Y := by
    dsimp only [x, y, t, Y]
    linarith only [him]
  have hproj := fifth_real_sq x y t Y hx hy hY (fun i => (hupper i).le) hxy hnorm
  have hdiff : (∑ i : Fin 4, D i.castSucc) - D 4 =
      10 + 2*S - 2*t^2 + 4*X*t + 3*X^2 - 3*s^2 := by
    have hshift := sum_shifted_product x x (-X) (-X)
    simp only [← sq, hx] at hshift
    change (∑ i, ((x i - X)^2 + y i^2 - s^2)) - ((t-X)^2 + (z 4).im^2 - s^2) = _
    simp only [Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_eq_add_neg]
    change (∑ i, (x i + -X)^2) + S + 4*(-s^2) + -((t + -X)^2 + (z 4).im^2 + -s^2) = _
    rw [hshift]
    dsimp only [Y] at hnorm
    linarith only [hnorm]
  have hXsq : X^2 < (1/2 : ℝ)^2 := by
    have h := abs_lt.mp hX
    nlinarith only [mul_pos (sub_pos.mpr h.2) (show 0 < 1/2 + X by linarith [h.1])]
  have hssq : s^2 < (511/1000 : ℝ)^2 := by
    nlinarith only [mul_pos (sub_pos.mpr hs₁) (show 0 < 511/1000 + s by linarith)]
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg (y i))
  change t^2 ≤ 3 + 3/5*S at hproj
  have hlt : D 4 < ∑ i : Fin 4, D i.castSucc := by
    nlinarith only [hdiff, hproj, hXsq, hssq, hS, sq_nonneg (t+4*X)]
  by_contra! htail
  have hcomp (i : Fin 4) : Y * D i.castSucc ≤ y i * D 4 := by
    have hi : i.castSucc ≤ (3 : Fin 5) := Fin.le_last i
    have ha : -qAngle X s (z 4) ≤ qAngle X s (z i.castSucc) := by
      linarith only [htail, hsort hi]
    change -Real.arctan (2*s*(z 4).im / D 4) ≤ Real.arctan (2*s*y i / D i.castSucc) at ha
    rw [← Real.arctan_neg, ← neg_div] at ha
    have hc := (div_le_div_iff₀ (hD 4) (hD i.castSucc)).mp (Real.arctan_le_arctan_iff.mp ha)
    apply (mul_le_mul_iff_of_pos_left (show 0 < 2*s by linarith)).mp
    dsimp only [Y]
    linarith only [hc]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcomp i)
  rw [← Finset.mul_sum, ← Finset.sum_mul, hy] at hsum
  exact (not_le_of_gt hlt) ((mul_le_mul_iff_of_pos_left hY).mp hsum)

/-- For decreasing signed angles with sum at least π, the first three
already have sum strictly greater than π. -/
theorem quintic_top_three (X s : ℝ) (z : Fin 5 → ℂ)
    (hX : |X| < 1/2) (hs₀ : 1/2 < s) (hs₁ : s < 511/1000)
    (hh : ∀ i, 87/100 ≤ |(z i).im|) (hz : ∑ i, z i = 0)
    (hz2 : ∑ i, z i ^ 2 = 10)
    (hsort : Antitone (fun i => qAngle X s (z i)))
    (hsum : Real.pi ≤ ∑ i, qAngle X s (z i)) :
    Real.pi < qAngle X s (z 0) + qAngle X s (z 1) + qAngle X s (z 2) := by
  have hD (i : Fin 5) : 0 < ((z i).re-X)^2 + (z i).im^2 - s^2 := by
    have h := hh i
    have hs : s < |(z i).im| := by linarith
    nlinarith only [sq_abs (z i).im, sq_nonneg ((z i).re-X),
      mul_pos (sub_pos.mpr hs) (show 0 < |(z i).im| + s by linarith)]
  have htail : qAngle X s (z 3) + qAngle X s (z 4) < 0 := by
    by_cases h : qAngle X s (z 3) < 0
    · linarith only [h, hsort (show (3 : Fin 5) ≤ 4 by decide)]
    · apply four_upper_tail X s z hX hs₀ hs₁ hz hz2 _ hsort hD
      intro i
      have hi : i.castSucc ≤ (3 : Fin 5) := Fin.le_last i
      have ha := (le_of_not_gt h).trans (hsort hi)
      have hnum : 0 ≤ 2*s*(z i.castSucc).im := by
        simpa only [zero_mul] using (le_div_iff₀ (hD i.castSucc)).mp (Real.arctan_nonneg.mp ha)
      have hy := (mul_nonneg_iff_of_pos_left (show 0 < 2*s by linarith)).mp hnum
      have habs := hh i.castSucc
      rw [abs_of_nonneg hy] at habs
      linarith
  norm_num [Fin.sum_univ_succ] at hsum
  linarith only [hsum, htail]

end Turan
