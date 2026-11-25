-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.SectionTwoProjection
import Turan.SectionTwoNormalForm
import Turan.SectionTwoLimitsDefs

noncomputable section
open Polynomial Filter Metric InnerProductSpace
open scoped Topology BigOperators ComplexConjugate Classical
namespace Turan.SectionTwo
variable {s : ℕ}

private theorem conjugate_bound (hs : s ∈ Set.Icc 2 4) (z : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (k : Fin s → ℕ) (hk : Function.Injective k) (a : Fin s → ℂ),
      1 ≤ frequency k → ∀ M : ℝ, 0 ≤ M →
      (∀ w ∈ closedBall z ε, ‖(slotSum k a).eval w‖ ≤ M) →
      ‖(slotSum k a).eval (conj z)‖ ≤ D * frequency k ^ (2*(s-1)) * M := by
  obtain ⟨C₀, hC, hproject⟩ := project_slot_estimate s hs z ε hε
  have hs' : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by have := hs.1; omega)
  refine ⟨(s : ℝ)*C₀*2^(s-1), by positivity, ?_⟩
  intro k hk a hω M hM hm
  have bound (v : Fin s) : ‖a v * (hermite (k v)).eval (conj z)‖ ≤ C₀*(1+topLambda k)^(s-1)*M := by
    obtain ⟨he, _, h⟩ := hproject k hk a v
    specialize h M hM hm
    rw [he, eval_mul, eval_C, norm_mul] at h
    simpa only [(hermite_symmetry (k v) z).1, norm_mul, Complex.norm_conj] using h
  have hL : 1+topLambda k ≤ 2*frequency k^2 := by
    nlinarith [frequency_sq k, sq_nonneg (frequency k - 1)]
  simp only [slotSum, eval_finsetSum, eval_mul, eval_C]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _v : Fin s, C₀*(1+topLambda k)^(s-1)*M := Finset.sum_le_sum (fun v _ => bound v)
    _ = (s:ℝ)*(C₀*(1+topLambda k)^(s-1)*M) := by simp
    _ ≤ (s:ℝ)*(C₀*(2*frequency k^2)^(s-1)*M) := by
      gcongr
      rw [← frequency_sq]
      positivity
    _ = _ := by rw [mul_pow, pow_mul]; ring

theorem harmonic_slot_limit_symmetry (hs : s ∈ Set.Icc 2 4)
    (k : ℕ → Fin s → ℕ) (hk : ∀ j, Function.Injective (k j)) (a : ℕ → Fin s → ℂ)
    (hω : Tendsto (fun j => frequency (k j)) atTop atTop)
    (he : escapesDisks (fun j => slotSum (k j) (a j))) (u : ℂ → ℝ)
    (hu : HarmonicOnNhd u Set.univ)
    (hlim : TendstoLocallyUniformly (fun j => scaledLog (frequency (k j))
      (slotSum (k j) (a j))) u atTop) :
    (∀ z : ℂ, ∀ ε : ℝ, 0 < ε → ∃ w ∈ closedBall z ε, u (conj z) ≤ u w) ∧
    ∀ z : ℂ, u (conj z) = u z := by
  let F (j : ℕ) := slotSum (k j) (a j)
  let ω (j : ℕ) := frequency (k j)
  have hcont : Continuous u := continuousOn_univ.mp hu.contDiffOn.continuousOn
  have compare (z : ℂ) (ε : ℝ) (hε : 0 < ε) : ∃ w ∈ closedBall z ε, u (conj z) ≤ u w := by
    obtain ⟨w, hw, hmax⟩ := (isCompact_closedBall z ε).exists_isMaxOn
      (nonempty_closedBall.mpr hε.le) hcont.continuousOn
    obtain ⟨D,hD,hbound⟩ := conjugate_bound hs z ε hε
    let q := 2*(s-1)
    have hlog : Tendsto (fun j => Real.log (ω j)/ω j) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hω
    have hDlim : Tendsto (fun j => Real.log D/ω j) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hω
    have hconv := hlim.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ (conj z))
    have hunif := tendstoLocallyUniformly_iff_forall_isCompact.mp hlim _ (isCompact_closedBall z ε)
    refine ⟨w, hw, le_of_forall_pos_le_add fun δ hδ => ?_⟩
    have hmajor : ∀ᶠ j in atTop, scaledLog (ω j) (F j) (conj z) ≤
        Real.log D/ω j + q*(Real.log (ω j)/ω j) + (u w + δ) := by
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif δ hδ,
        he (‖z‖+ε+1) (by positivity), hω.eventually_ge_atTop 1] with j hclose hfree hj
      have hp : 0 < ω j := zero_lt_one.trans_le hj
      have hin (y : ℂ) (hy : y ∈ closedBall z ε) : ‖y‖ ≤ ‖z‖+ε+1 := by
        have ht := norm_sub_norm_le y z
        have hd := mem_closedBall_iff_norm.mp hy
        linarith
      have hM (y : ℂ) (hy : y ∈ closedBall z ε) :
          ‖(F j).eval y‖ ≤ Real.exp ((u w+δ)*ω j) := by
        apply (Real.log_le_iff_le_exp (norm_pos_iff.mpr (hfree y (hin y hy)))).mp
        apply (div_le_iff₀ hp).mp
        have h := hclose y hy
        rw [Real.dist_eq, abs_lt] at h
        change _ < u y - scaledLog (ω j) (F j) y ∧ _ at h
        change scaledLog (ω j) (F j) y ≤ u w + δ
        linarith only [show u y ≤ u w from hmax hy, h.1]
      have h := hbound (k j) (hk j) (a j) hj _ (Real.exp_pos _).le hM
      have hc : (F j).eval (conj z) ≠ 0 := hfree _ (by rw [Complex.norm_conj]; linarith)
      have hle := Real.log_le_log (norm_pos_iff.mpr hc) h
      change _ ≤ Real.log (D*ω j^q*Real.exp ((u w+δ)*ω j)) at hle
      rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp,
        Real.log_mul hD.ne' (pow_pos hp _).ne', Real.log_pow] at hle
      unfold scaledLog
      apply (div_le_iff₀ hp).mpr
      apply hle.trans_eq
      field_simp [hp.ne']
      <;> ring
    have hright := (hDlim.add (hlog.const_mul (q : ℝ))).add_const (u w+δ)
    simpa only [mul_zero, zero_add] using le_of_tendsto_of_tendsto hconv hright hmajor
  have oneSide (z : ℂ) : u (conj z) ≤ u z := by
    by_contra! hlt
    have hnb := (hcont.continuousAt (x := z)).eventually_lt_const hlt
    obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff_ball.mp hnb
    obtain ⟨w,hw,hle⟩ := compare z (ε/2) (half_pos hε)
    exact (he w (closedBall_subset_ball (half_lt_self hε) hw)).not_ge hle
  exact ⟨compare, fun z => le_antisymm (oneSide z) (by simpa using oneSide (conj z))⟩

end Turan.SectionTwo
