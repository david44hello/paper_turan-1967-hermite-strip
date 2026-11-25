-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Constants
import Mathlib.Analysis.Convex.Deriv

open scoped ComplexConjugate Topology
namespace Turan

theorem cubic_auxiliary_increasing : StrictMono (fun t : ℝ => 4*t^3+3*t+1) := by
  intro s t hst
  dsimp
  linarith only [hst, (Odd.strictMono_pow (by decide : Odd 3)) hst]

theorem cubic_auxiliary_vieta :
    let r : ℂ := -2*(u:ℂ)
    r+W+conj W = 0 ∧ r*W+r*conj W+W*conj W = 3/4 ∧ r*W*conj W = -1/4 := by
  obtain ⟨hu, _, _, _, hh, _⟩ := constants_spec
  have hc : 32*(u:ℂ)^3 + 6*u = 1 := by exact_mod_cast hu
  have hh' : (h:ℂ)^2 = 3/4 + 3*(u:ℂ)^2 := by simpa using congrArg Complex.ofReal hh
  have hsum : W + conj W = 2*(u:ℂ) := by
    apply Complex.ext <;> simp [W, two_mul]
  have hprod : W * conj W = (u:ℂ)^2 + (h:ℂ)^2 := by
    apply Complex.ext <;> simp [W, sq, Complex.mul_re, Complex.mul_im]
    ring
  dsimp only
  refine ⟨by linear_combination hsum, ?_, ?_⟩
  · linear_combination (-2*(u:ℂ))*hsum + hprod + hh'
  · rw [mul_assoc, hprod, hh']
    linear_combination -hc / 4

theorem cubic_scale_root_real_part (z : ℂ) (hz : 12*z^2-12*z+9=0) : z.re = 1/2 := by
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  norm_num [sq, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im] at hr hi
  have hfac : (2*z.re-1)*z.im = 0 := by linarith only [hi]
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · rw [h] at hr
    nlinarith [sq_nonneg (z.re-1/2)]

theorem translated_root_relation (x y v : ℂ) (hv : v ≠ 0) :
    let τ := -1/(4*v)
    rootRelation x y v ↔ (x-τ)*(y-τ)=τ^2-(v+1)/(4*v) := by
  dsimp only
  unfold rootRelation
  constructor
  · intro hr
    field_simp [hv]
    linear_combination (4*v)*hr
  · intro hr
    field_simp [hv] at hr
    apply mul_left_cancel₀ (show (4:ℂ)*v ≠ 0 by exact mul_ne_zero (by norm_num) hv)
    linear_combination hr

theorem square_root_imaginary_identity (a b σ : ℂ) (hs : σ^2 = a*b) :
    2*σ.im^2 = ‖a‖*‖b‖-(a*b).re ∧ a.im*b.im ≤ σ.im^2 := by
  have hn := congrArg norm hs
  rw [norm_pow, norm_mul] at hn
  have hr := congrArg Complex.re hs
  simp only [sq, Complex.mul_re] at hr
  have he : 2*σ.im^2 = ‖a‖*‖b‖-(a*b).re := by
    rw [Complex.mul_re]
    nlinarith only [hr, hn, Complex.sq_norm_sub_sq_re σ]
  refine ⟨he, ?_⟩
  have dot := Complex.re_le_norm (a*conj b)
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, norm_mul, Complex.norm_conj] at dot
  rw [Complex.mul_re] at he
  linarith only [he, dot]

theorem third_poles (z : ℂ) : 4*z^2+1=0 ↔ z=Complex.I/2 ∨ z= -Complex.I/2 := by
  have hfac : 4*z^2+1 = 4*(z-Complex.I/2)*(z- -Complex.I/2) := by
    linear_combination Complex.I_sq
  rw [hfac]
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or, sub_eq_zero]

/-- Neither denominator zero is cancelled by the numerator of the third-root map. -/
theorem third_numerator_ne_at_pole (z : ℂ) (hz : 4*z^2+1=0) : -(2*z+1) ≠ 0 := by
  rcases (third_poles z).mp hz with rfl | rfl <;> intro he <;>
    have hr := congrArg Complex.re he <;>
    norm_num [Complex.div_re, Complex.mul_re, Complex.add_re] at hr

theorem boundary_quartic_convex :
    let q := fun s : ℝ => 16*(s^2+h^2)^2 - 16*h^2-8*s+3
    StrictConvexOn ℝ Set.univ q ∧ (∀ s, deriv q s = 64*s*(s^2+h^2)-8) ∧
      deriv q u = 0 ∧ q u = 0 := by
  let q := fun s : ℝ => 16*(s^2+h^2)^2 - 16*h^2-8*s+3
  change StrictConvexOn ℝ Set.univ q ∧ _
  have hd (s : ℝ) : deriv q s = 64*s*(s^2+h^2)-8 := by
    apply HasDerivAt.deriv
    convert ((((((hasDerivAt_id s).pow 2).add_const (h^2)).pow 2).const_mul 16).sub_const
      (16*h^2) |>.sub ((hasDerivAt_id s).const_mul 8) |>.add_const 3) using 1 <;>
      simp [q, Pi.pow_apply]
    ring
  obtain ⟨hu, _, _, _, hh, _⟩ := constants_spec
  refine ⟨StrictMono.strictConvexOn_univ_of_deriv (by dsimp [q]; fun_prop) ?_, hd, ?_, ?_⟩
  · intro s t hst
    rw [hd, hd]
    nlinarith only [(Odd.strictMono_pow (by decide : Odd 3)) hst,
      mul_le_mul_of_nonneg_right hst.le (sq_nonneg h)]
  · rw [hd, hh]
    linear_combination 8*hu
  · change 16*(u^2+h^2)^2 - 16*h^2-8*u+3 = 0
    rw [hh]
    linear_combination 8*u*hu

/-- In the coordinate w = 1/z the rational function is regular and zero at w = 0. -/
theorem third_decay : Filter.Tendsto third (Filter.cocompact ℂ) (𝓝 0) := by
  let g (w : ℂ) := -(2*w+w^2)/(4+w^2)
  have hcont : ContinuousAt g 0 := by unfold g; fun_prop (disch := norm_num)
  have hi : Filter.Tendsto (fun z : ℂ => z⁻¹) (Filter.cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact Filter.tendsto_inv₀_cobounded
  have hlim : Filter.Tendsto (fun z : ℂ => g z⁻¹) (Filter.cocompact ℂ) (𝓝 0) := by
    simpa only [Function.comp_def, show g 0 = 0 by simp [g]] using hcont.tendsto.comp hi
  apply hlim.congr'
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  have hn : z ≠ 0 := hz
  change -(2*z⁻¹+z⁻¹^2)/(4+z⁻¹^2) = -(2*z+1)/(4*z^2+1)
  rw [← mul_div_mul_right (-(2*z⁻¹+z⁻¹^2)) (4+z⁻¹^2) (pow_ne_zero 2 hn)]
  congr 1 <;> field_simp [hn]

theorem contact_pole_height : (-1/(4*W)).im = 2*u*h := by
  have hnorm := lemma_four.2.2.2.1
  rw [show -1/(4*W) = -(W⁻¹/4) by simp [div_eq_mul_inv, mul_inv_rev],
    Complex.neg_im, ← Complex.ofReal_ofNat (n := 4), Complex.div_ofReal_im,
    Complex.inv_im, Complex.normSq_eq_norm_sq, hnorm]
  change -(-h / (1/(8*u)) / 4) = 2*u*h
  simp only [div_eq_mul_inv, one_mul, inv_inv]
  ring

end Turan
