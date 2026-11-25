-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.SectionTwoSystem
import Turan.SectionTwoProjection
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section
open Polynomial Metric
open scoped Topology BigOperators Classical
namespace Turan.SectionTwo
variable {s : ℕ}

private def state (k : Fin s → ℕ) (a : Fin s → ℂ) (z : ℂ) (l : Fin (2*s)) : ℂ :=
  scaledJet (frequency k) (slotSum k a) l z

/-- Integrate the scaled first-order system along t ↦ t z, 0 ≤ t ≤ 1. -/
private theorem radial_growth (hs : s ∈ Set.Icc 2 4) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (k : Fin s → ℕ) (a : Fin s → ℂ), 1 ≤ topLambda k →
      ∀ z : ℂ, ‖z‖ ≤ R → ‖state k a z‖ ≤ ‖state k a 0‖ * Real.exp (C₀*frequency k) := by
  obtain ⟨A, hsys, hmat⟩ := scaled_jet_system s hs
  obtain ⟨b, hb, hbound⟩ := hmat R hR
  let C₀ := 1 + R * (2*s : ℕ) * b
  refine ⟨C₀, by dsimp [C₀]; positivity, ?_⟩
  intro k a hk z hz
  have hω := (zero_lt_one.trans_le (one_le_frequency hk))
  let rate (w : ℂ) (l : Fin (2*s)) := deriv (scaledJet (frequency k) (slotSum k a) l) w
  have hrate (w : ℂ) (hw : ‖w‖ ≤ R) :
      ‖rate w‖ ≤ (2*s : ℕ) * (b*frequency k) * ‖state k a w‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro l
    rw [show rate w l = _ from hsys k hk a l w]
    calc
      _ ≤ ∑ t : Fin (2*s), ‖(A k l t).eval w * state k a w t‖ := norm_sum_le _ _
      _ ≤ ∑ _t : Fin (2*s), (b*frequency k)*‖state k a w‖ := by
        apply Finset.sum_le_sum
        intro t _
        rw [norm_mul]
        exact mul_le_mul (hbound k hk w hw l t) (norm_le_pi_norm _ t) (norm_nonneg _) (by positivity)
      _ = _ := by simp [mul_assoc]
  let f (x : ℝ) := state k a ((x : ℂ)*z)
  let f' (x : ℝ) := z • rate ((x : ℂ)*z)
  have hd (x : ℝ) : HasDerivAt f (f' x) x := by
    apply hasDerivAt_pi.mpr
    intro l
    have hline : HasDerivAt (fun t : ℂ => t*z) z (x : ℂ) := by
      simpa using (hasDerivAt_id (x : ℂ)).mul_const z
    have hp : Differentiable ℂ (scaledJet (frequency k) (slotSum k a) l) :=
      (derivative^[l.val] (slotSum k a)).differentiable.div_const _
    simpa [f, f', state, rate, Function.comp_def, smul_eq_mul, mul_comm] using
      (((hp _).hasDerivAt.comp (x : ℂ) hline).comp_ofReal)
  have hbnd (x : ℝ) (hx : x ∈ Set.Ico (0:ℝ) 1) :
      ‖f' x‖ ≤ (C₀*frequency k)*‖f x‖ + 0 := by
    have hxz : ‖(x : ℂ)*z‖ ≤ R := by
      rw [norm_mul, Complex.norm_of_nonneg hx.1]
      exact (mul_le_of_le_one_left (norm_nonneg z) hx.2.le).trans hz
    rw [show ‖f' x‖ = _ from norm_smul z (rate ((x : ℂ)*z)), add_zero]
    apply (mul_le_mul hz (hrate _ hxz) (norm_nonneg _) hR).trans
    change R * (_ * _ * ‖f x‖) ≤ _
    dsimp only [C₀]
    nlinarith only [mul_nonneg hω.le (norm_nonneg (f x))]
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (f := f) (f' := f') (a := 0) (b := 1)
    (fun t _ => (hd t).continuousAt.continuousWithinAt) (fun t _ => (hd t).hasDerivWithinAt)
    (le_refl ‖f 0‖) hbnd 1 (by simp)
  simpa [f, gronwallBound_ε0] using hg

theorem normalize_initial_jet (hs : s ∈ Set.Icc 2 4) (k : Fin s → ℕ)
    (hL : 1 ≤ topLambda k) (a : Fin s → ℂ) (hp : slotSum k a ≠ 0) :
    ∃ t : ℂ, t ≠ 0 ∧ unitInitialJet k (C t * slotSum k a) := by
  have hs0 : 0 < 2*s := by have := hs.1; omega
  letI : Nonempty (Fin (2*s)) := ⟨⟨0, hs0⟩⟩
  have hn : state k a 0 ≠ 0 := by
    intro hzero
    apply hp
    apply Polynomial.funext
    intro z
    obtain ⟨_, _, hg⟩ := radial_growth hs ‖z‖ (norm_nonneg _)
    have h := hg k a hL z le_rfl
    rw [hzero, norm_zero, zero_mul, norm_le_zero_iff] at h
    simpa [state, scaledJet] using congrFun h (⟨0,hs0⟩ : Fin (2*s))
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun l => ‖state k a 0 l‖) Finset.univ_nonempty
  let M := ‖state k a 0 i‖
  have hM : 0 < M := lt_of_not_ge fun hm => hn (funext fun l =>
    norm_le_zero_iff.mp ((hi l (Finset.mem_univ _)).trans hm))
  let t := (M : ℂ)⁻¹
  have ht : t ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr hM.ne')
  have he (l : Fin (2*s)) :
      ‖scaledJet (frequency k) (C t * slotSum k a) l 0‖ = ‖state k a 0 l‖ / M := by
    simp only [scaledJet, state, iterate_derivative_C_mul, eval_mul, eval_C, norm_div, norm_mul, t, norm_inv, Complex.norm_of_nonneg hM.le]
    ring
  exact ⟨t, ht, fun l => (he l).trans_le ((div_le_one hM).mpr (hi l (Finset.mem_univ _))),
    i, (he i).trans (div_self hM.ne')⟩

theorem normalized_growth (s : ℕ) (hs : s ∈ Set.Icc 2 4) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (k : Fin s → ℕ) (a : Fin s → ℂ), 1 ≤ topLambda k →
      unitInitialJet k (slotSum k a) →
      (∀ z : ℂ, ‖z‖ ≤ R → ‖(slotSum k a).eval z‖ ≤ Real.exp (C₀ * frequency k)) ∧
      ∃ z : ℂ, ‖z‖ ≤ 1 ∧ 1 / (((2*s-1).factorial : ℕ) : ℝ) ≤ ‖(slotSum k a).eval z‖ := by
  obtain ⟨C₀, hC, hg⟩ := radial_growth hs R hR
  refine ⟨C₀, hC, ?_⟩
  intro k a hk ⟨hunit, l, hl⟩
  have hinit : ‖state k a 0‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr hunit
  constructor
  · intro z hz
    have hs0 : 0 < 2*s := by have := hs.1; omega
    have hval := norm_le_pi_norm (state k a z) (⟨0,hs0⟩ : Fin (2*s))
    apply (show ‖(slotSum k a).eval z‖ ≤ ‖state k a z‖ by simpa [state, scaledJet] using hval).trans
    exact (hg k a hk z hz).trans (mul_le_of_le_one_left (Real.exp_pos _).le hinit)
  · let p := slotSum k a
    obtain ⟨z, hz, hmax⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_isMaxOn
      (nonempty_closedBall.mpr zero_le_one) p.continuous.norm.continuousOn
    refine ⟨z, by simpa using mem_closedBall.mp hz, ?_⟩
    have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le l.val zero_lt_one
      p.differentiable.diffContOnCl (fun w hw => hmax (sphere_subset_closedBall hw))
    rw [polynomial_iteratedDeriv, one_pow, div_one] at hd
    have hω := one_le_frequency hk
    have hl' : ‖(derivative^[l.val] p).eval 0‖ = frequency k ^ l.val := by
      change ‖_ / (frequency k : ℂ)^l.val‖ = 1 at hl
      rwa [norm_div, norm_pow, Complex.norm_of_nonneg (zero_le_one.trans hω),
        div_eq_one_iff_eq (pow_pos (zero_lt_one.trans_le hω) _).ne'] at hl
    have hfac : (l.val.factorial : ℝ) ≤ (2*s-1).factorial := by
      exact_mod_cast Nat.factorial_le (show l.val ≤ 2*s-1 by have := l.isLt; omega)
    apply (div_le_iff₀ (by positivity)).mpr
    rw [mul_comm]
    exact (one_le_pow₀ hω).trans ((hl' ▸ hd).trans (mul_le_mul_of_nonneg_right hfac (norm_nonneg _)))

end Turan.SectionTwo
