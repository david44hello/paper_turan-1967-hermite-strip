-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.QuarticStability
import Turan.QuarticEscape

noncomputable section
open Polynomial Set Metric Filter
open scoped Topology
namespace Turan

private abbrev Coeffs := ℂ × ℂ × ℂ

private def projective (v : Coeffs) : Polynomial ℂ :=
  C v.1 * (1+2*X) + C v.2.1 * hermite 2 + C v.2.2 * hermite 4

private theorem projective_eval (v : Coeffs) (z : ℂ) :
    (projective v).eval z = v.1*(1+2*z)+v.2.1*(hermite 2).eval z+v.2.2*(hermite 4).eval z := by
  simp [projective,eval_add,eval_mul]

private theorem projective_nc (v : Coeffs) (hv : v ≠ 0) : 0 < (projective v).natDegree := by
  by_contra! h
  have hzero (i : ℕ) (hi : 0 < i) := coeff_eq_zero_of_natDegree_lt (p:=projective v) (h.trans_lt hi)
  have h₁ := hzero 1 (by decide)
  have h₂ := hzero 2 (by decide)
  have h₄ := hzero 4 (by decide)
  have hh₂ : hermite 2 = 4*X^2-2 := by norm_num [hermite,nsmul_eq_mul]; ring
  have hh₄ : hermite 4 = 16*X^4-48*X^2+12 := by norm_num [hermite,nsmul_eq_mul]; ring
  norm_num [projective,hh₂,hh₄,coeff_add,coeff_sub,coeff_X_pow,coeff_X,coeff_one,coeff_C_mul,
    coeff_ofNat_mul] at h₁ h₂ h₄
  apply hv
  ext <;> simp_all

private def height24 (v : Coeffs) : ℝ :=
  if h : 0 < (projective v).natDegree then
    |(Classical.choose (polynomial_has_lowest_zero (projective v) h)).im| else 0

private theorem ht_spec (v : Coeffs) (hv : v ≠ 0) :
    (∃ z : ℂ, (projective v).eval z=0 ∧ |z.im|=height24 v) ∧
    ∀ z : ℂ, (projective v).eval z=0 → height24 v≤|z.im| := by
  have h := polynomial_has_lowest_zero (projective v) (projective_nc v hv)
  unfold height24
  rw [dif_pos (projective_nc v hv)]
  exact ⟨⟨h.choose,h.choose_spec.1,rfl⟩,h.choose_spec.2⟩

private theorem ht_upper : UpperSemicontinuousOn height24 (sphere (0:Coeffs) 1) := by
  have hc : Continuous (fun v : Coeffs × ℂ => (projective v.1).eval v.2) := by
    simp only [projective_eval]
    fun_prop
  have hne (a : Coeffs) (ha : a ∈ sphere (0:Coeffs) 1) : a ≠ 0 := by rintro rfl; simp at ha
  intro a ha r hr
  obtain ⟨z,hz,he⟩ := (ht_spec a (hne a ha)).1
  have hstable := nearby_polynomial_root projective hc a
    (ne_zero_of_natDegree_gt (projective_nc a (hne a ha))) z hz (r-height24 a) (sub_pos.mpr hr)
  filter_upwards [self_mem_nhdsWithin,hstable.filter_mono nhdsWithin_le_nhds] with v hv he'
  obtain ⟨w,hw,hd⟩ := he'
  have hh := (ht_spec v (hne v hv)).2 w hw
  have hdiff := Complex.abs_im_le_norm (w-z)
  rw [Complex.sub_im] at hdiff
  rw [dist_eq_norm] at hd
  have ht := abs_add_le (w.im-z.im) z.im
  rw [sub_add_cancel] at ht
  linarith

/-- Maximize the least root height on a unit coefficient sphere. Points where
the linear polynomial's coefficient vanishes cannot attain the maximum. -/
theorem quartic_height_attained (H : ℝ) (hH : 1/2 < H) (a₀ b₀ : ℂ)
    (h₀ : ∀ z : ℂ, (family 2 4 a₀ b₀).eval z=0 → H≤|z.im|) :
    ∃ y : ℝ, ∃ a b : ℂ, H≤y ∧
      (∀ z : ℂ, (family 2 4 a b).eval z=0 → y≤|z.im|) ∧
      (∀ c d : ℂ, ∃ z : ℂ, (family 2 4 c d).eval z=0 ∧ |z.im|≤y) := by
  have unit : ((1:ℂ),(0:ℂ),(0:ℂ)) ∈ sphere (0:Coeffs) 1 := by simp [mem_sphere,Prod.norm_def]
  obtain ⟨v,hv,hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn ⟨_,unit⟩ (isCompact_sphere _ _) ht_upper
  have hv₀ : v ≠ 0 := by rintro rfl; simp at hv
  have cert := ht_spec v hv₀
  have hAll (a b : ℂ) : ∃ z : ℂ, (family 2 4 a b).eval z=0 ∧ |z.im|≤height24 v := by
    let t : Coeffs := (1,a,b)
    have ht : t≠0 := by intro he; have := congrArg Prod.fst he; simpa [t] using this
    let u := (‖t‖⁻¹ : ℝ) • t
    have hu : u ∈ sphere (0:Coeffs) 1 := by
      rw [mem_sphere,dist_zero_right]
      dsimp [u]
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr ht)]
    have hu₀ : u ≠ 0 := by intro hz; rw [hz] at hu; simp at hu
    obtain ⟨w,hw,hheight⟩ := (ht_spec u hu₀).1
    refine ⟨w,?_,hheight.trans_le (hmax hu)⟩
    have hfactor : (projective u).eval w = ((‖t‖⁻¹ : ℝ):ℂ)*(family 2 4 a b).eval w := by
      simp [u,t,projective_eval,family,eval_mul,eval_add,Complex.real_smul]; ring
    rw [hfactor] at hw
    exact (mul_eq_zero.mp hw).resolve_left (by exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr ht))
  obtain ⟨w,hw,hwin⟩ := hAll a₀ b₀
  have hheight := (h₀ w hw).trans hwin
  have hv₁ : v.1≠0 := by
    intro h
    obtain ⟨z,hz,hh⟩ := quartic_homogeneous_small v.2.1 v.2.2 (by
      by_contra! h'
      exact hv₀ (Prod.ext h (Prod.ext h'.1 h'.2)))
    have he : (projective v).eval z=0 := by simpa [projective_eval,h] using hz
    linarith [cert.2 z he]
  refine ⟨height24 v,v.2.1/v.1,v.2.2/v.1,hheight,?_,hAll⟩
  intro z hz
  apply cert.2 z
  rw [projective_eval]
  simp only [family,eval_add,eval_mul,eval_one,eval_C,eval_X,eval_ofNat] at hz
  field_simp [hv₁] at hz
  linear_combination hz

end Turan
