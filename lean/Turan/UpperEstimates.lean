-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.ProjectedMode
import Turan.CompactnessTools
import Mathlib.Analysis.Complex.ExponentialBounds
import Turan.TailGrowthSystem
import Turan.TailStripWeight
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

noncomputable section
open Polynomial Metric
namespace Turan.UpperEstimates


theorem shifted_operators_commute (p : Polynomial ℂ) (j k : ℂ) :
    EStar (EStar p + C k*p) + C j*(EStar p+C k*p) =
    EStar (EStar p + C j*p) + C k*(EStar p+C j*p) := by
  simp only [EStar, derivative_add, derivative_C_mul]
  ring

def affineZero (n m : ℕ) : ℝ := -1/(2*(1-1/(n:ℝ))*(1-1/(m:ℝ)))

private def gain (n : ℕ) : ℝ := 1-1/(n:ℝ)

private theorem gain_pos {j : ℕ} (hj : 2 ≤ j) : 0 < gain j := by
  have h : (2:ℝ) ≤ j := by exact_mod_cast hj
  exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))

private theorem gain_cast (j : ℕ) : (gain j : ℂ) = 1-1/(j:ℂ) := by simp [gain]

private theorem gain_prod (n m j k : ℕ) (h : (j=n ∧ k=m) ∨ (j=m ∧ k=n)) :
    gain n*gain m = gain k*gain j := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> ring

theorem affine_factorization (n m j j' : ℕ) (hm : 450 ≤ m) (hh : m ≤ 2*n) (hnm : n < m)
    (hj : (j=n ∧ j'=m) ∨ (j=m ∧ j'=n)) (z : ℂ) :
    let x := affineZero n m
    let P := 1+2*(1-1/(n:ℂ))*(1-1/(m:ℂ))*z
    let P' := 1+2*(1-1/(j':ℂ))*z
    |x| ≤ 1/(1-1/(m:ℝ)) ∧ 1/(1-1/(m:ℝ)) ≤ 450/449 ∧
    (P = 0 ↔ z = (x:ℂ)) ∧ P = 2*(1-1/(j':ℂ))*(1-1/(j:ℂ))*(z-x) ∧
    P'-P = 2*(1-1/(j':ℂ))*z/j ∧
    (z ≠ (x:ℂ) → projectedRatio n m j' z - 1 = z/(((j:ℂ)-1)*(z-x))) := by
  let x := affineZero n m
  let G := 2*gain n*gain m
  have hn : (2:ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hM : (450:ℝ) ≤ m := by exact_mod_cast hm
  have hn₁ : 1/2 ≤ gain n := by
    have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) hn
    unfold gain
    linarith
  have hgm := gain_pos (show 2 ≤ m by omega)
  have hG : 0 < G := mul_pos (by linarith only [hn₁] : 0 < 2*gain n) hgm
  have hx : G*x = -1 := by change G*(-1/G) = -1; field_simp
  have hgc : ((G:ℂ)*x) = -1 := by exact_mod_cast hx
  have hfactor : 1+2*(1-1/(n:ℂ))*(1-1/(m:ℂ))*z = (G:ℂ)*(z-x) := by
    have h : (G:ℂ) = 2*(1-1/(n:ℂ))*(1-1/(m:ℂ)) := by simp [G, gain_cast]
    rw [← h]; linear_combination hgc
  have hGj : (G:ℂ) = 2*(1-1/(j':ℂ))*(1-1/(j:ℂ)) := by
    dsimp [G]; rw [mul_assoc, gain_prod n m j j' hj]; simp [gain_cast, mul_assoc]
  have hj₀ : (j:ℂ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> omega)
  have hj₁ : (j:ℂ)-1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (show j ≠ 1 by rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> omega)
  have hdiff : (1+2*(1-1/(j':ℂ))*z) - (1+2*(1-1/(n:ℂ))*(1-1/(m:ℂ))*z) =
      2*(1-1/(j':ℂ))*z/j := by
    have h : 2*(1-1/(n:ℂ))*(1-1/(m:ℂ)) = (G:ℂ) := by simp [G, gain_cast]
    rw [h,hGj]; ring
  dsimp only
  refine ⟨?_, ?_, ?_, hfactor.trans (by rw [hGj]), hdiff, ?_⟩
  · change |-1/G| ≤ 1/gain m
    rw [abs_div, abs_of_pos hG]
    norm_num only [abs_neg, abs_one]
    apply one_div_le_one_div_of_le hgm
    exact le_mul_of_one_le_left hgm.le (by linarith only [hn₁])
  · apply (div_le_iff₀ hgm).mpr
    have hi := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 450) hM
    unfold gain
    linarith
  · rw [hfactor, mul_eq_zero, sub_eq_zero, or_iff_right (by exact_mod_cast hG.ne')]
  · intro hz
    have hd : (G:ℂ)*(z-x) ≠ 0 := mul_ne_zero (by exact_mod_cast hG.ne') (sub_ne_zero.mpr hz)
    unfold projectedRatio
    rw [hfactor, div_sub_one hd, ← hfactor, hdiff, hfactor]
    have heq : (G:ℂ)*(j:ℂ) = 2*(1-1/(j':ℂ))*((j:ℂ)-1) := by rw [hGj]; field_simp
    apply (div_eq_div_iff hd (mul_ne_zero hj₁ (sub_ne_zero.mpr hz))).mpr
    field_simp
    linear_combination -z*(z-(x:ℂ))*heq

theorem projection_strict_lines (n m j j' : ℕ) (hm : 450 ≤ m) (hh : m ≤ 2*n) (hnm : n < m)
    (hj : (j=n ∧ j'=m) ∨ (j=m ∧ j'=n)) (z : ℂ) (hz : |z.im| = 7/11) :
    let x := affineZero n m
    let Q := projectedRatio n m j' z
    7/11 ≤ ‖z-(x:ℂ)‖ ∧ ‖z/(z-x)‖ ≤ 1+|x|/(7/11) ∧
    1+|x|/(7/11) ≤ 1+(450/449)*(11/7) ∧ (1+(450/449)*(11/7):ℝ) < 2.575 ∧
    ‖Q-1‖ < 5/(j:ℝ) ∧ ‖Q‖ < 1+5/(j:ℝ) ∧ 1+5/(j:ℝ) ≤ 46/45 := by
  let x := affineZero n m
  let Q := projectedRatio n m j' z
  obtain ⟨hx,hM,_,_,_,hid⟩ := affine_factorization n m j j' hm hh hnm hj z
  have hdist : 7/11 ≤ ‖z-(x:ℂ)‖ := by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero, hz] using Complex.abs_im_le_norm (z-(x:ℂ))
  have hpos : 0 < ‖z-(x:ℂ)‖ := by linarith
  have hratio : ‖z/(z-x)‖ ≤ 1+|x|/(7/11) := by
    rw [norm_div]
    have ht := norm_add_le (z-(x:ℂ)) (x:ℂ)
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] at ht
    calc
      _ ≤ (‖z-(x:ℂ)‖+|x|)/‖z-(x:ℂ)‖ := by gcongr
      _ = 1+|x|/‖z-(x:ℂ)‖ := by rw [add_div, div_self hpos.ne']
      _ ≤ _ := by gcongr
  have hbudget : 1+|x|/(7/11) ≤ 1+(450/449)*(11/7) := by linarith only [hx.trans hM]
  have hjR : (225:ℝ) ≤ j := by
    exact_mod_cast (show 225 ≤ j by rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> omega)
  have hjpos : (0:ℝ) < j := by linarith
  have hj₁ : 0 < (j:ℝ)-1 := by linarith
  have hQ : ‖Q-1‖ < 5/(j:ℝ) := by
    change ‖projectedRatio n m j' z-1‖ < _
    rw [hid (sub_ne_zero.mp (norm_pos_iff.mp hpos)), show z/(((j:ℂ)-1)*(z-x)) =
      (z/(z-x))/(((j:ℝ)-1:ℝ):ℂ) by push_cast; simp [div_eq_mul_inv, mul_assoc], norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hj₁]
    apply (div_lt_div_iff₀ hj₁ hjpos).mpr
    have h := hratio.trans_lt (hbudget.trans_lt (by norm_num : (1+(450/449)*(11/7):ℝ) < 2.575))
    nlinarith only [mul_lt_mul_of_pos_right h hjpos,hjR]
  refine ⟨hdist,hratio,hbudget,by norm_num,hQ,?_,?_⟩
  · have h := norm_add_le (Q-1) 1
    rw [sub_add_cancel, norm_one] at h
    linarith only [h, hQ]
  · have h : 5/(j:ℝ) ≤ 5/225 := by gcongr
    linarith

def stripPi (m : ℕ) (z : ℂ) : ℂ :=
  (TailStrip.weightBase m z / (Real.sqrt (2*(m:ℝ)):ℂ))^4

private theorem frequency_lower (m : ℕ) (hm : 450 ≤ m) : 30 ≤ Real.sqrt (2*(m:ℝ)) := by
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  have : 450 ≤ (m:ℝ) := by exact_mod_cast hm
  linarith

theorem strip_weight_zero (m : ℕ) (hm : 450 ≤ m) (z : ℂ) :
    let s := Real.sqrt (2*(m:ℝ))
    stripPi m z = (1 - 4*Complex.I*z/(s:ℂ))^4 ∧
    (stripPi m z = 0 ↔ z = -Complex.I*(s:ℂ)/4) ∧
    (-Complex.I*(s:ℂ)/4).im ≤ -7.5 := by
  let s := Real.sqrt (2*(m:ℝ))
  have hs : 30 ≤ s := frequency_lower m hm
  have hs0 : (s:ℂ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by linarith)
  have hpi : stripPi m z = (1-4*Complex.I*z/(s:ℂ))^4 := by
    unfold stripPi TailStrip.weightBase
    change (((s:ℂ)-4*Complex.I*z)/s)^4 = _
    rw [sub_div, div_self hs0]
  have hroot : 4*Complex.I*(-Complex.I*(s:ℂ)/4) = (s:ℂ) := by
    ring_nf
    simp [Complex.I_sq]
  refine ⟨hpi, ?_, ?_⟩
  · rw [hpi, pow_eq_zero_iff (by decide : 4 ≠ 0), sub_eq_zero, eq_div_iff hs0, one_mul]
    constructor
    · intro h
      exact mul_left_cancel₀ (mul_ne_zero (by norm_num : (4:ℂ) ≠ 0) Complex.I_ne_zero) (h.symm.trans hroot.symm)
    · rintro rfl
      exact hroot.symm
  · change (-Complex.I*(s:ℂ)/4).im ≤ _
    simp [Complex.mul_im]
    linarith

theorem strip_weight_lower (m : ℕ) (hm : 450 ≤ m) (z : ℂ) (hz : |z.im| ≤ 7/11) :
    let s := Real.sqrt (2*(m:ℝ))
    let W := omega m z
    let γ := 4*(7/11)/s
    let v := 1 - 4*Complex.I*z/(s:ℂ)
    γ ≤ 14/165 ∧ ‖v‖^2 = (1+4*z.im/s)^2 + 16*z.re^2/(2*(m:ℝ)) ∧
    (1-γ)^2*W^2/(2*(m:ℝ)) ≤ ‖v‖^2 ∧
    (151/165)^4 * W^4/(4*(m:ℝ)^2) ≤ ‖stripPi m z‖ := by
  let s := Real.sqrt (2*(m:ℝ))
  let W := omega m z
  let γ := 4*(7/11)/s
  let v := 1-4*Complex.I*z/(s:ℂ)
  have hs : 30 ≤ s := frequency_lower m hm
  have hspos : 0 < s := by linarith
  have hM : 450 ≤ (m:ℝ) := by exact_mod_cast hm
  have hs2 : s^2 = 2*(m:ℝ) := Real.sq_sqrt (by positivity)
  have hW : W^2 = 2*(m:ℝ)+16*z.re^2 := Real.sq_sqrt (by positivity)
  have hγ : γ ≤ 14/165 := (div_le_iff₀ hspos).mpr (by linarith only [hs])
  have hγ0 : 0 ≤ γ := by dsimp [γ]; positivity
  have hbase : ‖v‖^2 = (1+4*z.im/s)^2 + 16*z.re^2/(2*(m:ℝ)) := by
    rw [← hs2, Complex.sq_norm, Complex.normSq_apply]
    simp [v, Complex.mul_re, Complex.mul_im]
    ring
  have hy : 1-γ ≤ 1+4*z.im/s := by
    obtain ⟨hl, _⟩ := abs_le.mp hz
    change 1-4*(7/11)/s ≤ _
    rw [sub_eq_add_neg, ← neg_div]
    gcongr
    linarith
  have hc : 0 ≤ 1-γ := by linarith
  have hsquare : (1-γ)^2 ≤ 1 := by
    simpa using (sq_le_sq₀ hc zero_le_one).mpr (by linarith : 1-γ ≤ 1)
  have hlow : (1-γ)^2*W^2/(2*(m:ℝ)) ≤ ‖v‖^2 := by
    rw [hbase, hW, mul_add, add_div, mul_div_cancel_right₀ _ (by positivity : 2*(m:ℝ) ≠ 0)]
    apply add_le_add ((sq_le_sq₀ hc (hc.trans hy)).mpr hy)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_of_le_one_left (by positivity : 0 ≤ 16*z.re^2) hsquare
  have hconst : (151/165)^2*W^2/(2*(m:ℝ)) ≤ ‖v‖^2 := by
    refine le_trans ?_ hlow
    gcongr
    linarith
  refine ⟨hγ,hbase,hlow,?_⟩
  calc
    _ = ((151/165)^2*W^2/(2*(m:ℝ)))^2 := by dsimp only [W]; ring
    _ ≤ (‖v‖^2)^2 := (sq_le_sq₀ (by positivity) (by positivity)).mpr hconst
    _ = ‖stripPi m z‖ := by rw [(strip_weight_zero m hm z).1, norm_pow]; dsimp [v,s]; ring

theorem line_operator_quotients (m : ℕ) (hm : 450 ≤ m) (z : ℂ) (hz : |z.im| = 7/11)
    (p : Polynomial ℂ) (hp : p.eval z ≠ 0)
    (hd : ∀ k : ℕ, 1 ≤ k → k ≤ 4 →
      ‖(derivative^[k] p).eval z / p.eval z‖ ≤ (11*omega m z)^k) :
    let W := omega m z
    let C₂ := (11:ℝ)^4/4 + 11^3*0.272 + 11^2*(0.272^2+1/900) + 11*0.272/900
    ‖z‖/W ≤ 1/4+7/330 ∧ (1/4+7/330:ℝ) < 0.272 ∧
    ‖(EStar p).eval z / p.eval z‖ ≤ (11*W)^2/2+11*‖z‖*W ∧
    (11*W)^2/2+11*‖z‖*W < (60.5+11*0.272)*W^2 ∧ (60.5+11*0.272)*W^2 < 64*W^2 ∧
    ‖(EStar (EStar p)).eval z / p.eval z‖ ≤ C₂*W^4 ∧ C₂*W^4 < 4035*W^4 := by
  let W := omega m z
  let d := fun k : ℕ => (derivative^[k] p).eval z / p.eval z
  have hM : 450 ≤ (m:ℝ) := by exact_mod_cast hm
  have hW : W^2 = 2*(m:ℝ)+16*z.re^2 := Real.sq_sqrt (by positivity)
  have hW0 : 0 ≤ W := Real.sqrt_nonneg _
  have hlarge : 900 ≤ W^2 := by nlinarith only [hW,hM,sq_nonneg z.re]
  have hW30 : 30 ≤ W := by nlinarith only [hlarge,hW0]
  have hWpos : 0 < W := by linarith
  have hx : |z.re| ≤ W/4 := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs]; nlinarith only [hW,hM]
  have hzW : ‖z‖/W ≤ 1/4+7/330 := by
    apply (div_le_iff₀ hWpos).mpr
    have h := Complex.norm_le_abs_re_add_abs_im z
    rw [hz] at h
    linarith only [h,hx,hW30]
  have hz' : ‖z‖ < 0.272*W :=
    (div_lt_iff₀ hWpos).mp (hzW.trans_lt (by norm_num))
  have h1 : ‖d 1‖ ≤ 11*W := by simpa only [d,W,pow_one] using hd 1 (by decide) (by decide)
  have h2 : ‖d 2‖ ≤ (11*W)^2 := hd 2 (by decide) (by decide)
  have h3 : ‖d 3‖ ≤ (11*W)^3 := hd 3 (by decide) (by decide)
  have h4 : ‖d 4‖ ≤ (11*W)^4 := hd 4 (by decide) (by decide)
  have e1 : (EStar p).eval z / p.eval z = d 2/2-z*d 1 := by
    simp [EStar,d,eval_mul,eval_sub]
    field_simp [hp]
  have e2 : (EStar (EStar p)).eval z / p.eval z =
      d 4/4 - z*d 3 + (z^2-1)*d 2 + z*d 1 := by
    simp only [EStar, derivative_sub, derivative_add, derivative_mul, derivative_C, zero_mul,
      zero_add, derivative_X, one_mul, eval_sub, eval_add, eval_mul, eval_X, eval_C]
    dsimp [d, Function.iterate_succ_apply]
    ring
  have hz2 : ‖z^2-1‖ ≤ (0.272*W)^2+1 := by
    refine (norm_sub_le ..).trans ?_
    rw [norm_pow, norm_one]
    gcongr
  have hlow := mul_le_mul_of_nonneg_right hlarge (sq_nonneg W)
  refine ⟨hzW,by norm_num,?_,?_,?_,?_,?_⟩
  · rw [e1]; refine (norm_sub_le ..).trans ?_
    rw [norm_div, norm_mul, Complex.norm_ofNat]
    change _ ≤ (11*W)^2/2+11*‖z‖*W
    nlinarith only [h2,mul_le_mul_of_nonneg_left h1 (norm_nonneg z)]
  · change (11*W)^2/2+11*‖z‖*W < _
    nlinarith only [mul_lt_mul_of_pos_right hz' hWpos]
  · change (60.5+11*0.272)*W^2 < 64*W^2
    nlinarith only [hlarge]
  · rw [e2]
    grw [norm_add_le,norm_add_le,norm_sub_le]
    simp only [norm_mul,norm_div,Complex.norm_ofNat]
    calc
      _ ≤ (11*W)^4/4 + 0.272*W*(11*W)^3 + ((0.272*W)^2+1)*(11*W)^2 + 0.272*W*(11*W) := by gcongr
      _ ≤ _ := by change _ ≤ _*W^4; nlinarith only [hlow]
  · change _ * W^4 < 4035*W^4
    apply mul_lt_mul_of_pos_right _ (pow_pos hWpos _)
    norm_num

/-- Maximum modulus of a polynomial on the closed disk in the scaled variable. -/
def diskNorm (p : Polynomial ℂ) (r : ℝ) : ℝ :=
  sSup ((fun t : ℂ => ‖p.eval t‖) '' closedBall 0 r)

private theorem eval_le_diskNorm (p : Polynomial ℂ) {r : ℝ} {t : ℂ} (ht : ‖t‖ ≤ r) :
    ‖p.eval t‖ ≤ diskNorm p r :=
  le_csSup ((isCompact_closedBall (0:ℂ) r).bddAbove_image p.continuous.norm.continuousOn)
    ⟨t, by simpa using ht, rfl⟩

private theorem diskNorm_le (p : Polynomial ℂ) {r B : ℝ} (hr : 0 ≤ r)
    (h : ∀ t : ℂ, ‖t‖ ≤ r → ‖p.eval t‖ ≤ B) : diskNorm p r ≤ B := by
  unfold diskNorm
  refine csSup_le ?_ ?_
  · exact ⟨‖p.eval 0‖, 0, mem_closedBall_self hr, rfl⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact h t (by simpa using ht)

private theorem diskNorm_nonneg (p : Polynomial ℂ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ diskNorm p r :=
  (norm_nonneg (p.eval 0)).trans (eval_le_diskNorm p (by simpa using hr))

private theorem diskNorm_pos (p : Polynomial ℂ) (hp : p ≠ 0) {r : ℝ} (hr : 0 < r) :
    0 < diskNorm p r := by
  by_contra! h
  apply hp
  apply eq_zero_of_infinite_isRoot
  apply (infinite_of_mem_nhds (0:ℂ) (closedBall_mem_nhds _ hr)).mono
  intro t ht
  exact norm_le_zero_iff.mp ((eval_le_diskNorm p (by simpa using ht)).trans h)

theorem radial_state (S : TailGrowthSystem) (t : ℂ) (ht : ‖t‖ ≤ 7) :
    ‖S.state t‖ ≤ Real.exp (1.75*‖t‖)*‖S.state 0‖ := by
  exact S.radial_state_le t ht

theorem half_radius_filter (S : TailGrowthSystem) (i : Fin 4) (r : ℝ)
    (hr : 1/2 ≤ r) (hr' : r ≤ 7) :
    let p := S.P i
    let B := diskNorm p r
    let C₁ : ℝ := 8+2*0.56+1
    diskNorm p.derivative (r-1/2) ≤ 2*B ∧
    diskNorm p.derivative.derivative (r-1/2) ≤ 8*B ∧
    diskNorm (S.P (i.val+1)) (r-1/2) ≤ C₁*B ∧
    (0 < B → C₁*B < 11*B) := by
  let p := S.P i
  let B := diskNorm p r
  have hB : 0 ≤ B := diskNorm_nonneg p (by linarith)
  have hrad : 0 ≤ r-1/2 := by linarith
  have hjet (t : ℂ) (ht : ‖t‖ ≤ r-1/2) :
      ‖p.derivative.eval t‖ ≤ 2*B ∧ ‖p.derivative.derivative.eval t‖ ≤ 8*B := by
    apply TailGrowthSystem.cauchy_half
    intro w hw
    apply eval_le_diskNorm
    have hdist := mem_sphere_iff_norm.mp hw
    have htri := norm_add_le (w-t) t
    rw [sub_add_cancel, hdist] at htri
    linarith
  refine ⟨diskNorm_le _ hrad (fun t ht => (hjet t ht).1),
    diskNorm_le _ hrad (fun t ht => (hjet t ht).2), diskNorm_le _ hrad ?_, ?_⟩
  · intro t ht
    obtain ⟨h₁,h₂⟩ := hjet t ht
    have h₀ : ‖p.eval t‖ ≤ B := eval_le_diskNorm _ (by linarith)
    have ha := mul_le_mul (S.drift t (by linarith)) h₁ (norm_nonneg _) (by norm_num)
    have hc := mul_le_mul (S.diagonal i i.isLt) h₀ (norm_nonneg _) zero_le_one
    rw [S.step i i.isLt]
    change ‖p.derivative.derivative.eval t-S.A t*p.derivative.eval t + S.c i*p.eval t‖ ≤ _
    grw [norm_add_le, norm_sub_le]
    simp only [norm_mul]
    linarith only [h₂, ha, hc]
  · intro h; linarith

theorem state_center_sharp (S : TailGrowthSystem) (h : S.P 0 ≠ 0) :
    let B := diskNorm (S.P 0) 2
    (∀ i : Fin 4, let R := 2-(i.val:ℝ)/2
      diskNorm (S.P i) R ≤ 11^i.val*B ∧
      ‖(S.P i).derivative.eval 0‖ ≤ 11^i.val*B/R) ∧
    (2*11^3/1.75 : ℝ) = 10648/7 ∧
    ‖S.state 0‖ ≤ (10648/7)*B ∧ (10648/7)*B < 1600*B := by
  let B := diskNorm (S.P 0) 2
  have hB : 0 < B := diskNorm_pos _ h (by norm_num)
  have stages (i : ℕ) (hi : i ≤ 3) :
      diskNorm (S.P i) (2-(i:ℝ)/2) ≤ 11^i*B := by
    induction i with
    | zero => simp [B]
    | succ i ih =>
      have hi' : (i:ℝ) ≤ 2 := by exact_mod_cast (show i ≤ 2 by omega)
      have hstep := (half_radius_filter S ⟨i, by omega⟩ (2-(i:ℝ)/2)
        (by linarith) (by linarith [Nat.cast_nonneg (α:=ℝ) i])).2.2.1
      rw [Nat.cast_succ, show 2-((i:ℝ)+1)/2 = 2-i/2-1/2 by ring]
      apply hstep.trans
      calc
        _ ≤ 11*(11^i*B) := mul_le_mul (by norm_num) (ih (by omega))
          (diskNorm_nonneg _ (by linarith)) (by norm_num)
        _ = _ := by ring
  have hcenter (i : Fin 4) :
      let R := 2-(i.val:ℝ)/2
      diskNorm (S.P i) R ≤ 11^i.val*B ∧ ‖(S.P i).derivative.eval 0‖ ≤ 11^i.val*B/R := by
    have hi : (i.val:ℝ) ≤ 3 := by exact_mod_cast (show i.val ≤ 3 by omega)
    have hR : 0 < 2-(i.val:ℝ)/2 := by linarith
    have hiB := stages i.val (by omega)
    refine ⟨hiB, ?_⟩
    have hder := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := 0) hR (S.P i).differentiable.diffContOnCl
      (fun z hz => (eval_le_diskNorm (S.P i) (by simpa using (mem_sphere.mp hz).le)).trans hiB)
    simpa only [Polynomial.deriv] using hder
  refine ⟨hcenter, by norm_num, ?_, by change (10648/7)*B < 1600*B; linarith⟩
  apply pi_norm_le_iff_of_nonneg (by positivity) |>.mpr
  intro i
  obtain ⟨hs,hd⟩ := hcenter i
  have hi : (i.val:ℝ) ≤ 3 := by exact_mod_cast (show i.val ≤ 3 by omega)
  have hR : 1/2 ≤ 2-(i.val:ℝ)/2 := by linarith
  have hval := (eval_le_diskNorm (S.P i) (t:=0) (by simp; linarith : ‖(0:ℂ)‖ ≤ 2-(i.val:ℝ)/2)).trans hs
  have hp : (11:ℝ)^i.val ≤ 1331 := by
    calc _ ≤ (11:ℝ)^3 := pow_le_pow_right₀ (by norm_num) (show i.val ≤ 3 by omega)
         _ = _ := by norm_num
  have hpB := mul_le_mul_of_nonneg_right hp hB.le
  have hd' : ‖(S.P i).derivative.eval 0‖ ≤ (1331*B)/(1/2) :=
    hd.trans (div_le_div₀ (by positivity) hpB (by norm_num) hR)
  apply norm_prod_le_iff.mpr
  change ‖(S.P i).eval 0‖ ≤ _ ∧ ‖(S.P i).derivative.eval 0 * (((4/7:ℝ):ℂ))‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4/7)]
  constructor <;> linarith only [hval, hpB, hd', hB]

def upsilon (S : TailGrowthSystem) (t : ℂ) : ℝ :=
  Real.log ((Real.exp 12.25 * ‖S.state 0‖) / ‖(S.P 0).eval t‖)

theorem harmonic_majorant (S : TailGrowthSystem)
    (hf : ∀ t : ℂ, ‖t‖ ≤ 7 → (S.P 0).eval t ≠ 0) :
    0 < Real.exp 12.25 * ‖S.state 0‖ ∧
    InnerProductSpace.HarmonicOnNhd (upsilon S) (closedBall 0 7) ∧
    ∀ t : ℂ, ‖t‖ ≤ 7 → 0 ≤ upsilon S t := by
  let p := S.P 0
  let M := Real.exp 12.25 * ‖S.state 0‖
  have hM : 0 < M := mul_pos (Real.exp_pos _)
    ((norm_pos_iff.mpr (hf 0 (by simp))).trans_le (S.value_le_state 0 0))
  refine ⟨hM, ?_, ?_⟩
  · intro z hz
    have hp : p.eval z ≠ 0 := hf z (by simpa using hz)
    have hlog := (p.differentiable.analyticAt z).harmonicAt_log_norm hp
    have h := (InnerProductSpace.harmonicAt_const (Real.log M)).sub hlog
    apply (InnerProductSpace.harmonicAt_congr_nhds (f₁ := upsilon S) (f₂ :=
      (fun _ : ℂ => Real.log M) - (fun t => Real.log ‖p.eval t‖)) ?_).mpr h
    filter_upwards [p.continuousAt.eventually_ne hp] with t ht
    exact Real.log_div hM.ne' (norm_ne_zero_iff.mpr ht)
  · intro z hz
    apply Real.log_nonneg
    apply (one_le_div₀ (norm_pos_iff.mpr (hf z hz))).mpr
    exact S.radial z hz

theorem centered_comparison (S : TailGrowthSystem)
    (hf : ∀ t : ℂ, ‖t‖ ≤ 7 → (S.P 0).eval t ≠ 0)
    (t₁ : ℂ) (ht : ‖t₁‖ ≤ 2) (hmax : ‖(S.P 0).eval t₁‖ = diskNorm (S.P 0) 2) :
    upsilon S t₁ < 12.25 + Real.log 1600 ∧
    upsilon S 0 ≤ (9/5)*upsilon S t₁ ∧ (9/5)*upsilon S t₁ < 35.34 := by
  let B := diskNorm (S.P 0) 2
  have hp : S.P 0 ≠ 0 := by
    intro h
    have hzero := hf 0 (by simp)
    simp [h] at hzero
  have hB : 0 < B := diskNorm_pos _ hp (by norm_num)
  have hs := (state_center_sharp S hp).2.2
  have hstate : ‖S.state 0‖ < 1600*B := hs.1.trans_lt hs.2
  have hlog : upsilon S t₁ < 12.25 + Real.log 1600 := by
    rw [upsilon, hmax]
    have h : Real.exp 12.25 * ‖S.state 0‖ / B < Real.exp 12.25 * 1600 := by
      apply (div_lt_iff₀ hB).mpr
      simpa only [mul_assoc] using mul_lt_mul_of_pos_left hstate (Real.exp_pos 12.25)
    have hpos := (harmonic_majorant S hf).1
    have he := Real.log_lt_log (div_pos hpos hB) h
    simpa only [Real.log_mul (Real.exp_pos _).ne' (by norm_num : (1600:ℝ) ≠ 0), Real.log_exp] using he
  obtain ⟨_, hh, hnonneg⟩ := harmonic_majorant S hf
  have ht₁ : t₁ ∈ ball (0:ℂ) 7 := by rw [mem_ball, dist_zero_right]; linarith
  have hhar := (harnack_disk (upsilon S) 0 t₁ 7
    (hh.mono closure_ball_subset_closedBall).harmonicContOnCl
    (fun w hw => hnonneg w (by simpa using (mem_sphere.mp hw).le)) ht₁).1
  rw [sub_zero] at hhar
  have hfrac : 5/9 ≤ (7-‖t₁‖)/(7+‖t₁‖) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hnum : Real.log 1600 < 7.378 := by
    rw [show (1600:ℝ) = 2^6*5^2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]
    linarith only [Real.log_two_lt_d9, Real.log_five_lt_d9]
  refine ⟨hlog, ?_, ?_⟩
  · linarith only [hhar, mul_le_mul_of_nonneg_right hfrac (hnonneg 0 (by simp))]
  · linarith only [hlog, hnum]

end Turan.UpperEstimates
