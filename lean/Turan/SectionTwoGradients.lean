-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.SectionTwoLimitsDefs
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

noncomputable section
open Polynomial Filter Metric InnerProductSpace
open scoped Topology ComplexConjugate
namespace Turan.SectionTwo

theorem positive_ratio_reciprocal_bound (μ L : ℕ → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (h : Tendsto (fun j => μ j / L j) atTop (𝓝 γ)) :
    Tendsto (fun j => L j / μ j) atTop (𝓝 γ⁻¹) ∧
    ∀ᶠ j in atTop, |L j / μ j| ≤ 2/γ := by
  have hlim : Tendsto (fun j => L j / μ j) atTop (𝓝 γ⁻¹) := by
    simpa only [inv_div] using h.inv₀ hγ.ne'
  refine ⟨hlim, ?_⟩
  have hg : |γ⁻¹| < 2/γ := by rw [abs_of_pos (inv_pos.mpr hγ), ← one_div]; gcongr; norm_num
  exact (hlim.abs.eventually_lt_const hg).mono fun _ h => h.le

theorem gradient_of_re {g : ℂ → ℂ} {z v : ℂ} (h : HasDerivAt g v z) :
    complexGradient (fun w => (g w).re) z = v := by
  have hd := Complex.reCLM.hasFDerivAt.comp z (h.hasFDerivAt.restrictScalars ℝ)
  change (↑(fderiv ℝ (Complex.reCLM ∘ g) z 1) : ℂ) -
    Complex.I * ↑(fderiv ℝ (Complex.reCLM ∘ g) z Complex.I) = v
  rw [hd.fderiv]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

theorem complexGradient_differentiable (u : ℂ → ℝ) (hu : HarmonicOnNhd u Set.univ) :
    Differentiable ℂ (complexGradient u) :=
  fun z => HarmonicAt.differentiableAt_complex_partial (hu z (Set.mem_univ _))

theorem scaledJet_hasDerivAt (ω : ℝ) (p : Polynomial ℂ) (l : ℕ) (z : ℂ) :
    HasDerivAt (scaledJet ω p l) ((derivative ((derivative^[l]) p)).eval z / (ω : ℂ)^l) z :=
  ((derivative^[l] p).hasDerivAt z).div_const _

theorem scaled_quotient_identities (p : Polynomial ℂ) (ω : ℝ) (hω : 0 < ω)
    (z : ℂ) (hz : p.eval z ≠ 0) (l : ℕ) :
    complexGradient (scaledLog ω p) z = jetRatio ω p 1 z ∧
    deriv (jetRatio ω p l) z / (ω : ℂ) =
      jetRatio ω p (l+1) z - jetRatio ω p l z * jetRatio ω p 1 z := by
  have hω' := Complex.ofReal_ne_zero.mpr hω.ne'
  constructor
  · have aux {g : ℂ → ℂ} {v : ℂ} (hg : HasDerivAt g v z) (hg' : g z ∈ Complex.slitPlane) :
        complexGradient (fun w => Real.log ‖g w‖ / ω) z = (v / g z) / (ω : ℂ) := by
      simpa only [Complex.div_ofReal_re, Complex.log_re] using
        gradient_of_re ((hg.clog hg').div_const (ω : ℂ))
    have he : complexGradient (scaledLog ω p) z = (p.derivative.eval z / p.eval z) / (ω : ℂ) := by
      rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hz with hs | hs
      · exact aux (p.hasDerivAt z) hs
      · unfold scaledLog
        simpa using aux (p.hasDerivAt z).neg hs
    rw [he]
    simp only [jetRatio, scaledJet, Function.iterate_one, pow_one]
    ring
  · have hd := ((scaledJet_hasDerivAt ω p l z).div (p.hasDerivAt z) hz).deriv
    change deriv (scaledJet ω p l / (fun w => p.eval w)) z / (ω : ℂ) = _
    rw [hd]
    simp only [scaledJet, jetRatio, Function.iterate_succ_apply', Function.iterate_zero_apply, pow_succ, pow_zero, mul_one]
    field_simp [hω', hz]
    <;> ring

end Turan.SectionTwo
