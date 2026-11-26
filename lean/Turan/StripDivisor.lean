module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.StripDetailDefs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.RemovableSingularity

@[expose] public section
noncomputable section
open Filter Set
namespace Turan.StripDetails

private theorem sinh_lattice (q : ℂ) :
    Complex.sinh q = 0 ↔ ∃ k : ℤ, q=(k:ℂ)*(Real.pi:ℂ)*Complex.I := by
  constructor
  · intro h
    obtain ⟨k,hk⟩ := Complex.sin_eq_zero_iff.mp (show Complex.sin (q*Complex.I)=0 by
      rw [Complex.sin_mul_I,h,zero_mul])
    refine ⟨-k, ?_⟩
    push_cast
    linear_combination -Complex.I*hk + q*Complex.I_sq
  · rintro ⟨k,rfl⟩
    rw [Complex.sinh_mul_I,Complex.sin_int_mul_pi,zero_mul]

theorem strip_factor_divisor (s : ℝ) :
    (∀ z : ℂ, Complex.sinh (coordinate s z)=0 ↔
      ∃ k : ℤ, z=(s:ℂ)+4*(height:ℂ)*Complex.I*(k:ℂ)) ∧
    (∀ z : ℂ, Complex.cosh (coordinate s z)=0 → 2*height ≤ |z.im|) ∧
    (∀ z : ℂ, |z.im| < 87/100 → AnalyticAt ℂ (factor s) z ∧ (factor s z=0 ↔ z=(s:ℂ))) ∧
    HasDerivAt (factor s) ((Real.pi/(4*height):ℝ):ℂ) (s:ℂ)  := by
  have hπ : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hcoord (z : ℂ) : (coordinate s z).im = Real.pi*z.im/(4*height) := by
    simp [coordinate, height,Complex.div_ofReal_im,Complex.mul_im,Complex.div_im,
      Complex.normSq_ofReal, Complex.sub_im]
    <;> ring
  have hz (z : ℂ) : Complex.sinh (coordinate s z)=0 ↔
      ∃ k : ℤ, z=(s:ℂ)+4*(height:ℂ)*Complex.I*(k:ℂ) := by
    rw [sinh_lattice]
    constructor
    · rintro ⟨k,hk⟩
      refine ⟨k, ?_⟩
      unfold coordinate at hk
      apply mul_left_cancel₀ hπ
      have hh : (4*(height:ℂ)) ≠ 0 := by norm_num [height]
      linear_combination (div_eq_iff hh).mp hk
    · rintro ⟨k,rfl⟩
      refine ⟨k, ?_⟩
      unfold coordinate
      norm_num [height]
      <;> ring
  have hp (z : ℂ) (hz' : Complex.cosh (coordinate s z)=0) : 2*height ≤ |z.im| := by
    have he : Complex.cos (coordinate s z*Complex.I)=0 := by rwa [Complex.cos_mul_I]
    obtain ⟨k,hk⟩ := Complex.cos_eq_zero_iff.mp he
    have h := congrArg Complex.re hk
    norm_num [Complex.mul_I_re,Complex.mul_re,Complex.add_re,Complex.div_ofNat_re,hcoord,height] at h
    by_contra! hlt
    obtain ⟨hl,hr⟩ := abs_lt.mp hlt
    norm_num [height] at hl hr
    by_cases hk₀ : 0 ≤ k
    · have hk' : 0 ≤ (k:ℝ) := by exact_mod_cast hk₀
      nlinarith only [h,mul_nonneg hk' Real.pi_pos.le,mul_pos (sub_pos.mpr hl) Real.pi_pos]
    · have hk' : (k:ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      nlinarith only [h,mul_nonneg (sub_nonneg.mpr hk') Real.pi_pos.le,mul_pos (sub_pos.mpr hr) Real.pi_pos]
  have hnear (z : ℂ) (hy : |z.im| < 87/100) : Complex.cosh (coordinate s z) ≠ 0 := by
    intro hh
    have hh' := hp z hh
    norm_num [height] at hh'
    linarith
  have hderiv (z : ℂ) : HasDerivAt (coordinate s) ((Real.pi/(4*height):ℝ):ℂ) z := by
    unfold coordinate
    simpa [mul_one] using ((((hasDerivAt_id z).sub_const (s:ℂ)).const_mul
      (Real.pi:ℂ)).div_const (4*(height:ℂ)))
  refine ⟨hz, hp, ?_, ?_⟩
  · intro z hy
    have ha : AnalyticAt ℂ (coordinate s) z := by unfold coordinate; fun_prop
    refine ⟨(Complex.analyticAt_sinh.comp ha).div (Complex.analyticAt_cosh.comp ha) (hnear z hy), ?_⟩
    rw [factor,Complex.tanh_eq_sinh_div_cosh,div_eq_zero_iff,or_iff_left (hnear z hy),hz]
    constructor
    · rintro ⟨k,hk⟩
      have hh := congrArg Complex.im hk
      simp [Complex.mul_im,Complex.mul_re,Complex.add_im,height] at hh
      have hk' : k=0 := by
        by_contra hk₀
        rcases lt_or_gt_of_ne hk₀ with hn | hn
        · have hn' : (k:ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
          linarith [(abs_lt.mp hy).1]
        · have hn' : 1 ≤ (k:ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
          linarith [(abs_lt.mp hy).2]
      simpa [hk'] using hk
    · rintro rfl
      exact ⟨0,by simp⟩
  · have h0 : coordinate s (s:ℂ)=0 := by simp [coordinate]
    have hd := ((Complex.hasDerivAt_sinh _).comp (s:ℂ) (hderiv s)).div
      ((Complex.hasDerivAt_cosh _).comp (s:ℂ) (hderiv s)) (by simp [h0])
    change HasDerivAt ((fun v => Complex.sinh (coordinate s v)) / (fun v => Complex.cosh (coordinate s v))) _ _
    simpa [Function.comp_def,h0] using hd

end Turan.StripDetails
