module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Small34CertificateChart
public import Turan.Small34CertificateChecks

@[expose] public section

noncomputable section
open Complex
open scoped ComplexConjugate
namespace Turan
namespace Small34Certificate

private theorem homogeneous (P : Boxes) (X V Y : ℝ) :
    product P (X*V) V Y = ((V^22 : ℝ) : ℂ) * product P X 1 Y := by
  have line_scale (e σ : ℤ) : line e σ (X*V) V Y = (V:ℂ)*line e σ X 1 Y := by
    unfold line
    push_cast
    ring
  have pair_scale (l r σ : ℤ) : pair l r σ (X*V) V Y = (V:ℂ)^2 * pair l r σ X 1 Y := by
    unfold pair
    rw [line_scale,line_scale]
    ring
  unfold product
  rw [pair_scale,pair_scale,pair_scale,Complex.ofReal_pow]
  ring

private theorem weight_scale (k : ℤ) (d : ℝ) (z : ℂ) :
    weight k ((d:ℂ)*z) = d*weight k z := by simp [weight]; ring

private theorem inside (P : Boxes) {a b : ℤ} (h : test P a b 1 = true) (X t : ℝ)
    (ht : 0 ≤ t) (ha : (a:ℝ) ≤ X) (hb : X < (b:ℝ)) :
    0 < weight P.slope (product P X 1 (5000000+t)) := by
  let x := (X-a)/(b-X)
  have hx : 0 ≤ x := div_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb.le)
  have he : (a:ℝ)+b*x = X*(1+x) := by dsimp [x]; field_simp; ring
  have hh := chart P h hx ht
  simp only [Int.cast_one,one_mul,he,homogeneous,weight_scale] at hh
  exact pos_of_mul_pos_right hh (by positivity)

private theorem exterior (P : Boxes) (hP : P=upper ∨ P=lower) (X Y : ℝ) (hy : 5000000 ≤ Y) :
    0 < weight P.slope (product P X 1 Y) := by
  have select {a b v : ℤ} (h : both a b v = true) : test P a b v = true := by
    rcases hP with rfl | rfl
    · exact (Bool.and_eq_true_iff.mp h).1
    · exact (Bool.and_eq_true_iff.mp h).2
  let t := Y-5000000
  have ht : 0 ≤ t := sub_nonneg.mpr hy
  rw [show Y=5000000+t by dsimp [t]; ring]
  by_cases h₀ : X < (-2000000)
  · have h := chart P (select checkLeft) (x := -2000000-X) (by linarith) ht
    convert h using 1 <;> norm_num
  by_cases h₁ : X < (-1000000)
  · exact inside P (select check₁) X t ht (by norm_num; linarith) (by exact_mod_cast h₁)
  by_cases h₂ : X < (-750000)
  · exact inside P (select check₂) X t ht (by norm_num; linarith) (by exact_mod_cast h₂)
  by_cases h₃ : X < (-500000)
  · exact inside P (select check₃) X t ht (by norm_num; linarith) (by exact_mod_cast h₃)
  by_cases h₄ : X < 0
  · exact inside P (select check₄) X t ht (by norm_num; linarith) (by exact_mod_cast h₄)
  by_cases h₅ : X < 500000
  · exact inside P (select check₅) X t ht (by norm_num; linarith) (by exact_mod_cast h₅)
  by_cases h₆ : X < 750000
  · exact inside P (select check₆) X t ht (by norm_num; linarith) (by exact_mod_cast h₆)
  by_cases h₇ : X < 1000000
  · exact inside P (select check₇) X t ht (by norm_num; linarith) (by exact_mod_cast h₇)
  by_cases h₈ : X < 2000000
  · exact inside P (select check₈) X t ht (by norm_num; linarith) (by exact_mod_cast h₈)
  have h := chart P (select checkRight) (x := X-2000000) (by linarith) ht
  convert h using 1 <;> norm_num

private theorem scaled_pair (l r : ℤ) (x y : ℝ) :
    pair l r 1 (1000000*x) 1 (7000000*y) =
      (7000000:ℂ)^2 * small34Z ((l:ℝ)/1000000) ((r:ℝ)/1000000) x y := by
  unfold pair line small34Z
  push_cast
  ring

private theorem scaled_conj_pair (l r : ℤ) (x y : ℝ) :
    pair l r (-1) (1000000*x) 1 (7000000*y) =
      (7000000:ℂ)^2 * conj (small34Z ((l:ℝ)/1000000) ((r:ℝ)/1000000) x y) := by
  unfold pair line small34Z
  push_cast
  simp only [map_mul,map_sub,map_add,conj_ofReal,conj_I,map_div₀,map_intCast,map_ofNat]
  ring

private theorem transfer (P : Boxes) (hP : P=upper ∨ P=lower) (x y : ℝ) (z : ℂ)
    (hy : 5/7 ≤ y) (h : product P (1000000*x) 1 (7000000*y) =
      (((7000000:ℝ)^22:ℝ):ℂ)*z) : 0 < weight P.slope z := by
  have hh := exterior P hP (1000000*x) (7000000*y) (by linarith)
  rw [h,weight_scale] at hh
  exact pos_of_mul_pos_right hh (by positivity)

end Small34Certificate

open Small34Certificate in
/-- Upper rounded angle product in Lemma 20, throughout the closed upper half-plane y ≥ 5/7. -/
theorem small34_upper_certificate (x y : ℝ) (hy : 5/7 ≤ y) :
    0 < (small34ZUpper x y).re - 44 * (small34ZUpper x y).im := by
  change 0 < weight upper.slope (small34ZUpper x y)
  apply transfer upper (.inl rfl) x y _ hy
  unfold product
  rw [scaled_pair,scaled_conj_pair,scaled_pair]
  norm_num [upper,small34ZUpper]
  ring

open Small34Certificate in
/-- Lower rounded angle product in Lemma 20, throughout the closed upper half-plane y ≥ 5/7. -/
theorem small34_lower_certificate (x y : ℝ) (hy : 5/7 ≤ y) :
    0 < (small34ZLower x y).re - 14 * (small34ZLower x y).im := by
  change 0 < weight lower.slope (small34ZLower x y)
  apply transfer lower (.inr rfl) x y _ hy
  unfold product
  rw [scaled_pair,scaled_conj_pair,scaled_pair]
  norm_num [lower,small34ZLower]
  ring

#print axioms small34_upper_certificate
#print axioms small34_lower_certificate
end Turan
