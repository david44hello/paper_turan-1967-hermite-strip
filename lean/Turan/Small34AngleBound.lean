-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Small34Angles
import Turan.Small34Branch
import Turan.Small34Sign

noncomputable section
open Real Complex Set Filter
open scoped ComplexConjugate Topology
namespace Turan

private def weighted (a b c d e f : ℝ) (z : ℂ) : ℝ :=
  5*small34Angle a b z - 4*small34Angle c d z + 2*small34Angle e f z

private def rounded (a b c d e f x y : ℝ) : ℂ :=
  small34Z a b x y ^ 5 * conj (small34Z c d x y)^4 * small34Z e f x y ^ 2

private theorem pair_eq (l r : ℝ) (z : ℂ) :
    small34Z l r z.re z.im = ((r:ℂ)-z)*conj ((l:ℂ)-z) := by
  have h (t : ℝ) : (((z.re-t:ℝ):ℂ) + z.im*I) = -((t:ℂ)-z) := by
    apply Complex.ext <;> simp [Complex.sub_re,Complex.sub_im] <;> ring
  have j (t : ℝ) : (((z.re-t:ℝ):ℂ) - z.im*I) = conj (-((t:ℂ)-z)) := by
    rw [← h t]; simp [sub_eq_add_neg]
  rw [small34Z,h r,j l,map_neg,neg_mul_neg]

private theorem weighted_arg (a b c d e f : ℝ) (z : ℂ) (hy : 0 < z.im) :
    (weighted a b c d e f z : Angle) = ((rounded a b c d e f z.re z.im).arg : Angle) := by
  have ne (r : ℝ) : (r:ℂ)-z ≠ 0 := by intro h; rw [← sub_eq_zero.mp h] at hy; simpa using hy
  have nc (l : ℝ) : conj ((l:ℂ)-z) ≠ 0 :=
    (map_ne_zero_iff _ (starRingEnd ℂ).injective).mpr (ne l)
  have hn (l r : ℝ) : small34Z l r z.re z.im ≠ 0 := by
    rw [pair_eq]; exact mul_ne_zero (ne r) (nc l)
  have ha (l r : ℝ) : (small34Angle l r z : Angle) = ((small34Z l r z.re z.im).arg : Angle) := by
    rw [small34Angle_arg_quotient l r z hy.ne',pair_eq,Complex.arg_div_coe_angle (ne _) (ne _),
      Complex.arg_mul_coe_angle (ne _) (nc l),Complex.arg_conj_coe_angle,sub_eq_add_neg]
  have coe_mul (n : ℕ) (t : ℝ) : (((n:ℝ)*t : ℝ) : Angle) = n • (t:Angle) := by
    rw [← nsmul_eq_mul, Angle.coe_nsmul]
  unfold rounded weighted
  rw [Complex.arg_mul_coe_angle (by simp [hn]) (by simp [hn]),
    Complex.arg_mul_coe_angle (by simp [hn]) (by simp [hn]),
    Complex.arg_pow_coe_angle,Complex.arg_pow_coe_angle,Complex.arg_pow_coe_angle,
    Complex.arg_conj_coe_angle,Angle.coe_add,Angle.coe_sub,
    show (5:ℝ) = ((5:ℕ):ℝ) by norm_num,
    show (4:ℝ) = ((4:ℕ):ℝ) by norm_num,
    show (2:ℝ) = ((2:ℕ):ℝ) by norm_num,
    coe_mul,coe_mul,coe_mul,ha,ha,ha]
  abel

private theorem rounded_bounds (a b c d e f y q : ℝ) (hy : 0 < y) (hq : 0 < q)
    (h : ∀ x, 0 < (rounded a b c d e f x y).re-q*(rounded a b c d e f x y).im) (x : ℝ) :
    arctan (1/q)-π < weighted a b c d e f ⟨x,y⟩ ∧ weighted a b c d e f ⟨x,y⟩ < arctan (1/q) := by
  have limit (t : ℝ) : Tendsto (fun u : ℝ => arctan ((t-u)/y)) atTop (𝓝 (-(π/2))) := by
    apply (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atBot).comp
    apply Tendsto.atBot_div_const hy
    exact tendsto_atBot.mpr (fun k => eventually_atTop.mpr ⟨t-k, fun u hu => by linarith⟩)
  have zero (l r : ℝ) : Tendsto (fun u : ℝ => small34Angle l r ⟨u,y⟩) atTop (𝓝 0) := by
    simpa [small34Angle] using (limit r).sub (limit l)
  apply small34_branch_between (fun u => weighted a b c d e f ⟨u,y⟩) (arctan (1/q))
    (arctan_pos.mpr (by positivity)) (by linarith [arctan_lt_pi_div_two (1/q),pi_pos])
    (by unfold weighted small34Angle; dsimp; fun_prop) _ _ x
  · simpa [weighted] using (((zero a b).const_mul 5).sub ((zero c d).const_mul 4)).add
      ((zero e f).const_mul 2)
  · intro u
    exact small34_sin_sign _ _ _ hq (weighted_arg a b c d e f ⟨u,y⟩ hy) (h u)

private theorem weighted_mono (z : ℂ) (hy : 0 < z.im) {a b c d e f A B C D E F : ℝ}
    (ha : A ≤ a) (hb : b ≤ B) (hc : c ≤ C) (hd : D ≤ d) (he : E ≤ e) (hf : f ≤ F) :
    weighted a b c d e f z ≤ weighted A B C D E F z := by
  have mono (x y : ℝ) (h : x ≤ y) :
      arctan ((x-z.re)/z.im) ≤ arctan ((y-z.re)/z.im) :=
    arctan_strictMono.monotone (div_le_div_of_nonneg_right (by linarith) hy.le)
  unfold weighted small34Angle
  linarith only [mono _ _ ha,mono _ _ hb,mono _ _ hc,mono _ _ hd,mono _ _ he,mono _ _ hf]

theorem small34_weighted_bound (l₁ r₁ l₂ r₂ l₃ r₃ : ℝ)
    (hl₁ : l₁ ∈ Icc (-1.311446) (-1.311445)) (hr₁ : r₁ ∈ Icc (-0.096252) (-0.096251))
    (hl₂ : l₂ ∈ Icc (-1.553003) (-1.553002)) (hr₂ : r₂ ∈ Icc 1.794300 1.794301)
    (hl₃ : l₃ ∈ Icc (-0.308319) (-0.308318)) (hr₃ : r₃ ∈ Icc 2.074717 2.074718)
    (z : ℂ) (hz : 5/7 ≤ z.im) :
    let g := 5*small34Angle l₁ r₁ z - 4*small34Angle l₂ r₂ z + 2*small34Angle l₃ r₃ z;
    -π + arctan (1/14) < g ∧ g < arctan (1/44) := by
  have hy : 0 < z.im := by linarith
  have up := rounded_bounds (-1.311446) (-0.096251) (-1.553002) 1.794300 (-0.308319) 2.074718
    z.im 44 hy (by norm_num) (fun x => small34_sign_upper x _ hz) z.re
  have lo := rounded_bounds (-1.311445) (-0.096252) (-1.553003) 1.794301 (-0.308318) 2.074717
    z.im 14 hy (by norm_num) (fun x => small34_sign_lower x _ hz) z.re
  change -π + arctan (1/14) < weighted l₁ r₁ l₂ r₂ l₃ r₃ z ∧ _
  rw [neg_add_eq_sub]
  exact ⟨lo.1.trans_le (weighted_mono z hy hl₁.2 hr₁.1 hl₂.1 hr₂.2 hl₃.2 hr₃.1),
    (weighted_mono z hy hl₁.1 hr₁.2 hl₂.2 hr₂.1 hl₃.1 hr₃.2).trans_lt up.2⟩

end Turan
