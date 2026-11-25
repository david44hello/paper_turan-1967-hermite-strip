-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.SectionTwoGradients
import Mathlib.Analysis.Analytic.IsolatedZeros

noncomputable section
open Polynomial Filter Metric InnerProductSpace
open scoped Topology BigOperators ComplexConjugate
namespace Turan.SectionTwo
variable {s : ℕ}

theorem symmetric_gradient_vanishes (u : ℂ → ℝ) (hu : HarmonicOnNhd u Set.univ)
    (hsymm : ∀ z : ℂ, u (conj z) = u z) (γ : Fin s → ℝ) (hγ : ∀ v, 0 ≤ γ v)
    (hchar : ∀ z : ℂ, (∏ v, ((complexGradient u z)^2 + (γ v : ℂ))) = 0) :
    (∀ x : ℝ, (complexGradient u (x : ℂ)).im = 0) ∧
    (∀ z, complexGradient u z = 0) ∧ ∀ z, u z = u 0 := by
  have hdiff : Differentiable ℝ u := fun z => (hu z trivial).1.differentiableAt two_ne_zero
  have hreal (x : ℝ) : (complexGradient u (x : ℂ)).im = 0 := by
    have hcomp : u ∘ (Complex.conjCLE : ℂ → ℂ) = u := funext hsymm
    have hd := congrArg (fun f : ℂ → ℝ => fderiv ℝ f (x : ℂ) Complex.I) hcomp
    rw [fderiv_comp _ (hdiff _) Complex.conjCLE.differentiableAt] at hd
    simp only [Complex.conjCLE_apply, Complex.conj_ofReal, Complex.conjCLE.fderiv,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conj_I, map_neg] at hd
    simp [complexGradient, Complex.mul_im]
    linarith
  have hzero (x : ℝ) : complexGradient u (x : ℂ) = 0 := by
    obtain ⟨v, _, hv⟩ := Finset.prod_eq_zero_iff.mp (hchar (x : ℂ))
    have h := congrArg Complex.re hv
    simp only [pow_two, Complex.add_re, Complex.mul_re, hreal, zero_mul, sub_zero,
      Complex.ofReal_re, Complex.zero_re] at h
    exact Complex.ext (by rw [Complex.zero_re]; nlinarith [hγ v, sq_nonneg (complexGradient u (x : ℂ)).re]) (hreal x)
  have ht : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_iff.mpr (Eventually.of_forall fun t ht => Complex.ofReal_ne_zero.mpr ht)⟩
  have hol := complexGradient_differentiable u hu
  have hall : complexGradient u = 0 := (hol.differentiableOn.analyticOnNhd isOpen_univ).eq_of_frequently_eq
    analyticOnNhd_const (ht.frequently (Frequently.of_forall hzero))
  refine ⟨hreal, fun z => congrFun hall z, fun z => is_const_of_fderiv_eq_zero hdiff ?_ z 0⟩
  intro z
  have hg : complexGradient u z = 0 := congrFun hall z
  have hre := congrArg Complex.re hg
  have him := congrArg Complex.im hg
  simp [complexGradient, Complex.mul_re, Complex.mul_im] at hre him
  ext w
  calc
    _ = fderiv ℝ u z (w.re • (1 : ℂ) + w.im • Complex.I) := by simp
    _ = _ := by simp only [map_add, map_smul, hre, him, smul_zero, add_zero, ContinuousLinearMap.zero_apply]

end Turan.SectionTwo
