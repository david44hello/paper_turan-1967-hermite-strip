-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.TailStripCore
import Turan.ProjectedMode

noncomputable section
open Set
namespace Turan.UpperTailStrip

theorem quotient_analytic (n m j : ℕ) (a b z : ℂ) (hz : |z.im| < 87/100)
    (hF : normalizedFamily n m a b z ≠ 0) :
    AnalyticAt ℂ (modeQuotient n m j a b) z := by
  have hpsi (k : ℕ) : AnalyticAt ℂ (psi k) z := ((hermite k).differentiable.analyticAt z).div_const
  apply AnalyticAt.div _ _ hF
  · exact analyticAt_const.mul (hpsi j)
  · unfold normalizedFamily
    exact ((analyticAt_const.add (analyticAt_const.mul analyticAt_id)).add (analyticAt_const.mul (hpsi n))).add
      (analyticAt_const.mul (hpsi m))

def affineDen (n m : ℕ) (z : ℂ) : ℂ :=
  1+2*(1-1/(n:ℂ))*(1-1/(m:ℂ))*z

def affinePole (n m : ℕ) : ℝ := -1/(2*(1-1/(n:ℝ))*(1-1/(m:ℝ)))

private def scale (n m : ℕ) : ℝ := 2*(1-1/(n:ℝ))*(1-1/(m:ℝ))

private theorem factor_pos (n : ℕ) (hn : 2 ≤ n) : 0 < 1-1/(n:ℝ) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))

private theorem scale_pos (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) : 0 < scale n m :=
  mul_pos (mul_pos (by norm_num) (factor_pos n hn)) (factor_pos m hm)

private theorem den_factor (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (z : ℂ) :
    affineDen n m z = (scale n m : ℂ)*(z-(affinePole n m : ℂ)) := by
  have hne : (scale n m : ℂ) ≠ 0 := by exact_mod_cast (scale_pos n m hn hm).ne'
  change _ = (scale n m : ℂ)*(z-((-1/scale n m : ℝ):ℂ))
  push_cast
  have he : affineDen n m z = 1+(scale n m : ℂ)*z := by simp [affineDen, scale]
  rw [he]
  field_simp
  ring

theorem affine_zero (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m) (z : ℂ) :
    (affineDen n m z = 0 ↔ z = (affinePole n m : ℂ)) ∧
    (z.im ≠ 0 → affineDen n m z ≠ 0) := by
  have hne : (scale n m : ℂ) ≠ 0 := by exact_mod_cast (scale_pos n m hn (by omega)).ne'
  have he : affineDen n m z = 0 ↔ z = (affinePole n m : ℂ) := by
    rw [den_factor n m hn (by omega), mul_eq_zero, or_iff_right hne, sub_eq_zero]
  exact ⟨he, fun him hz => him ((congrArg Complex.im (he.mp hz)).trans rfl)⟩

private theorem pole_abs (j k : ℕ) (hj : 225 ≤ j) (hk : 225 ≤ k) : |affinePole j k| ≤ 1 := by
  have quarter (i : ℕ) (hi : 225 ≤ i) : 3/4 ≤ 1-1/(i:ℝ) := by
    have hi' : (225:ℝ) ≤ i := by exact_mod_cast hi
    have := (div_le_iff₀ (show 0 < (i:ℝ) by linarith)).mpr (show 1 ≤ (1/4:ℝ)*i by linarith)
    linarith
  have h := mul_le_mul (quarter j hj) (quarter k hk) (by norm_num) (factor_pos j (by omega)).le
  have hs := scale_pos j k (by omega) (by omega)
  change |(-1:ℝ)/scale j k| ≤ 1
  rw [abs_div, abs_neg, abs_one, abs_of_pos hs, div_le_one hs]
  dsimp [scale]
  linarith

private theorem ratio_identity (j k : ℕ) (hj : 225 ≤ j) (hk : 225 ≤ k) (z : ℂ)
    (hx : z-(affinePole j k : ℂ) ≠ 0) : projectedRatio j k k z-1 =
      z/(((j:ℂ)-1)*(z-(affinePole j k : ℂ))) := by
  have hJ : (j:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hJ' : (j:ℂ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show j ≠ 1 by omega))
  have hK : (k:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hs : (scale j k : ℂ) ≠ 0 := by exact_mod_cast (scale_pos j k (by omega) (by omega)).ne'
  have hden : affineDen j k z ≠ 0 := by rw [den_factor j k (by omega) (by omega)]; exact mul_ne_zero hs hx
  change (1+2*(1-1/(k:ℂ))*z)/(affineDen j k z)-1 = _
  rw [div_sub_one hden, div_eq_div_iff hden (mul_ne_zero hJ' hx)]
  have hsub : 1+2*(1-1/(k:ℂ))*z-affineDen j k z = 2*(1-1/(k:ℂ))*z/j := by unfold affineDen; ring
  rw [hsub, den_factor j k (by omega) (by omega)]
  simp only [scale, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_div,
    Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_ofNat]
  field_simp

theorem named_ratio_line (n m j j' : ℕ) (hm : 450 ≤ m) (hh : m ≤ 2*n) (hnm : n < m)
    (hj : (j=n ∧ j'=m) ∨ (j=m ∧ j'=n)) (z : ℂ) (hz : |z.im| = TailStrip.height) :
    projectedRatio n m j' z - 1 = z / (((j:ℂ)-1)*(z-(affinePole n m : ℂ))) ∧
    ‖projectedRatio n m j' z - 1‖ < 2.59/(j:ℝ) ∧
    ‖projectedRatio n m j' z - 1‖ < 5/(j:ℝ) ∧
    ‖projectedRatio n m j' z‖ < 1+5/(j:ℝ) ∧ 1+5/(j:ℝ) ≤ 46/45 := by
  let x := affinePole n m
  have hj' : (225:ℝ) ≤ j := by exact_mod_cast (show 225 ≤ j by rcases hj with h|h <;> omega)
  have hdist : 7/11 ≤ ‖z-(x:ℂ)‖ := by simpa [hz] using Complex.abs_im_le_norm (z-(x:ℂ))
  have hx : z-(x:ℂ) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hdist)
  have he : projectedRatio n m j' z - 1 = z / (((j:ℂ)-1)*(z-(x:ℂ))) := by
    rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ratio_identity _ _ (by omega) (by omega) _ hx
    · have hswap : affinePole j' j = affinePole j j' := by unfold affinePole; ring
      have hq : projectedRatio j' j j' z = projectedRatio j j' j' z := by unfold projectedRatio; ring
      dsimp [x] at hx ⊢
      rw [hswap] at hx
      rw [hswap,hq]
      exact ratio_identity _ _ (by omega) (by omega) _ hx
  have hjpos : 0 < (j:ℝ) := by linarith
  have hj1 : 0 < (j:ℝ)-1 := by linarith
  have hzn := norm_add_le (z-(x:ℂ)) (x:ℂ)
  rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] at hzn
  have hnorm : ‖(j:ℂ)-1‖ = (j:ℝ)-1 := by
    change ‖((j:ℝ):ℂ)-((1:ℝ):ℂ)‖ = _
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg hj1.le]
  have hratio : ‖projectedRatio n m j' z-1‖ < 2.59/(j:ℝ) := by
    rw [he,norm_div,norm_mul,hnorm,div_mul_eq_div_div_swap]
    calc
      _ ≤ 2.575/((j:ℝ)-1) := by
        gcongr
        apply (div_le_iff₀ (norm_pos_iff.mpr hx)).mpr
        have := pole_abs n m (by omega) (by omega)
        change |x| ≤ 1 at this
        linarith
      _ < _ := (div_lt_div_iff₀ hj1 hjpos).mpr (by linarith)
  have h5 := hratio.trans (div_lt_div_of_pos_right (by norm_num : (2.59:ℝ)<5) hjpos)
  have ht := norm_add_le (projectedRatio n m j' z-1) 1
  rw [sub_add_cancel, norm_one] at ht
  refine ⟨he,hratio,h5,by linarith, ?_⟩
  have h := (div_le_iff₀ hjpos).mpr (show 5 ≤ (1/45:ℝ)*j by linarith)
  linarith

end Turan.UpperTailStrip
