module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.SectionTwoHarmonicEstimates
public import Turan.SectionTwoLogBounds
public import Turan.SlotDerivatives

@[expose] public section

noncomputable section
open Polynomial Filter Metric InnerProductSpace
open scoped Topology
namespace Turan.SectionTwo

private theorem joint_iff (G : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (hg : Continuous g) :
    TendstoLocallyUniformly G g atTop ↔ ∀ z : ℂ,
      Tendsto (fun p : ℕ × ℂ => G p.1 p.2) (atTop ×ˢ 𝓝 z) (𝓝 (g z)) := by
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  apply forall_congr'
  intro z
  have hleft : Tendsto (fun p : ℕ × ℂ => g p.2) (atTop ×ˢ 𝓝 z) (𝓝 (g z)) :=
    hg.continuousAt.tendsto.comp tendsto_snd
  exact ⟨hleft.congr_uniformity, fun h => (hleft.prodMk_nhds h).mono_right (nhds_le_uniformity _)⟩

private theorem deriv_limit (G : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (hlim : TendstoLocallyUniformly G g atTop)
    (hd : ∀ R : ℝ, 0 < R → ∀ᶠ j in atTop, DifferentiableOn ℂ (G j) (ball 0 R)) :
    TendstoLocallyUniformly (fun j => deriv (G j)) (deriv g) atTop := by
  apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
  intro S hS
  obtain ⟨R,hR,hSR⟩ := hS.isBounded.subset_ball_lt 0 (0 : ℂ)
  have hl := hlim.tendstoLocallyUniformlyOn.deriv (hd R hR) isOpen_ball
  exact (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp hl S hSR hS

theorem harmonic_jet_limits (F : ℕ → Polynomial ℂ) (ω : ℕ → ℝ)
    (hω : Tendsto ω atTop atTop) (he : escapesDisks F) (u : ℂ → ℝ)
    (hu : HarmonicOnNhd u Set.univ)
    (hlim : TendstoLocallyUniformly (fun j => scaledLog (ω j) (F j)) u atTop) :
    Differentiable ℂ (complexGradient u) ∧ ∀ l : ℕ, 1 ≤ l →
      TendstoLocallyUniformly (fun j => jetRatio (ω j) (F j) l)
        (fun z => (complexGradient u z)^l) atTop ∧
      TendstoLocallyUniformly (fun j z => deriv (jetRatio (ω j) (F j) l) z / (ω j : ℂ))
        (fun _ => 0) atTop := by
  let Q (l j : ℕ) := jetRatio (ω j) (F j) l
  let Φ := complexGradient u
  have hhol : Differentiable ℂ Φ := complexGradient_differentiable u hu
  have hpos := hω.eventually_gt_atTop 0
  have hnon (z : ℂ) : ∀ᶠ p : ℕ × ℂ in atTop ×ˢ 𝓝 z, (F p.1).eval p.2 ≠ 0 := by
    filter_upwards [tendsto_fst.eventually (he (‖z‖+1) (by positivity)),
      tendsto_snd.eventually (ball_mem_nhds z zero_lt_one)] with p hp hx
    apply hp
    linarith [norm_sub_norm_le p.2 z, mem_ball_iff_norm.mp hx]
  have hfirst : TendstoLocallyUniformly (Q 1) Φ atTop := by
    apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
    intro S hS
    obtain ⟨R,hR,hS'⟩ := hS.isBounded.subset_closedBall_lt 0 (0 : ℂ)
    have hcl := tendstoLocallyUniformly_iff_forall_isCompact.mp hlim _ (isCompact_closedBall 0 (R+1))
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hcl (ε/9) (by positivity),
      he (R+1) (by positivity), hpos] with j hj hfree hωj z hz
    have hzR : ‖z‖ ≤ R := by simpa using mem_closedBall.mp (hS' hz)
    have hsubset (w : ℂ) (hw : w ∈ ball z 1) : ‖w‖ ≤ R+1 := by
      linarith [norm_sub_norm_le w z, mem_ball_iff_norm.mp hw]
    let v := scaledLog (ω j) (F j)
    have hv : HarmonicOnNhd v (ball z 1) := fun w hw => scaledLog_harmonic _ _ _ (hfree _ (hsubset w hw))
    have hbd := harmonic_gradient_bound z (ε/9) (by positivity) (hv.sub (hu.mono (Set.subset_univ _)))
      (fun w hw => by
        have h := hj w (show w ∈ closedBall (0 : ℂ) (R+1) by simpa [mem_closedBall] using hsubset w hw)
        simpa [Real.dist_eq, abs_sub_comm, v] using h.le)
    have hdz := (hv z (mem_ball_self zero_lt_one)).1.differentiableAt two_ne_zero
    rw [gradient_sub hdz ((hu z trivial).1.differentiableAt two_ne_zero),
      (scaled_quotient_identities _ _ hωj z (hfree _ (by linarith)) 1).1] at hbd
    rw [dist_comm, dist_eq_norm]
    exact hbd.trans_lt (by linarith)
  have hdlim (l : ℕ) (hl : TendstoLocallyUniformly (Q l) (fun z => Φ z^l) atTop) :
      TendstoLocallyUniformly (fun j z => deriv (Q l j) z/(ω j : ℂ)) (fun _ => 0) atTop := by
    have hg := deriv_limit (Q l) _ hl (fun R hR => (he R hR).mono fun j hj z hz =>
      ((scaledJet_hasDerivAt (ω j) (F j) l z).div ((F j).hasDerivAt z)
        (hj z (by simpa using (mem_ball.mp hz).le))).differentiableAt.differentiableWithinAt)
    apply (locally_to_const _ _).mpr
    intro z
    have ha := (joint_iff _ _ (hhol.pow l).deriv.continuous).mp hg z
    have hb : Tendsto (fun p : ℕ × ℂ => (ω p.1 : ℂ)⁻¹) (atTop ×ˢ 𝓝 z) (𝓝 0) := by
      simpa only [Function.comp_def, Complex.ofReal_zero, Complex.ofReal_inv] using
        ((Complex.continuous_ofReal.tendsto 0).comp (tendsto_inv_atTop_zero.comp hω)).comp tendsto_fst
    simpa only [div_eq_mul_inv, mul_zero] using ha.mul hb
  refine ⟨hhol, fun l hl => ?_⟩
  suffices h : TendstoLocallyUniformly (Q l) (fun z => Φ z^l) atTop from ⟨h, hdlim l h⟩
  induction l, hl using Nat.le_induction with
  | base => simpa using hfirst
  | succ l hl ih =>
    apply (joint_iff _ _ (hhol.pow _).continuous).mpr
    intro z
    have hD := (locally_to_const _ _).mp (hdlim l ih) z
    have hprod := ((joint_iff _ _ (hhol.pow l).continuous).mp ih z).mul
      ((joint_iff _ _ hhol.continuous).mp hfirst z)
    have hadd := hD.add hprod
    simp only [zero_add, Pi.pow_apply, ← pow_succ] at hadd
    refine hadd.congr' ?_
    filter_upwards [hnon z, tendsto_fst.eventually hpos] with p hp hωp
    exact (eq_sub_iff_add_eq.mp (scaled_quotient_identities _ _ hωp _ hp l).2)

end Turan.SectionTwo
