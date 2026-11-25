-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.LowerTailRadial

noncomputable section
open Filter Metric Set Polynomial
open scoped ComplexConjugate Topology
namespace Turan.LowerTailSteps

theorem radial_shrink {s : ℝ} (hs : s ∈ Icc 0 1) {v : ℂ} (hv : ‖v‖ ≤ 1) :
    ‖(s:ℂ)*v‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
  exact mul_le_one₀ hs.2 (norm_nonneg _) hv

theorem op_continuous (j : ℕ) (ξ ρ : ℝ) {f : ℂ → ℂ} (hf : Continuous f) :
    Continuous (volterraOp j ξ ρ f) := by
  unfold volterraOp
  apply Continuous.mul (by fun_prop)
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold Function.uncurry radialPotential
  fun_prop

theorem iter_continuous (j : ℕ) (ξ ρ : ℝ) {f : ℂ → ℂ} (hf : Continuous f) (k : ℕ) :
    Continuous ((volterraOp j ξ ρ)^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [Function.iterate_succ_apply']; exact op_continuous j ξ ρ ih

theorem op_add (j : ℕ) (ξ ρ : ℝ) {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    volterraOp j ξ ρ (f+g) = volterraOp j ξ ρ f + volterraOp j ξ ρ g := by
  funext v
  dsimp [volterraOp,Pi.add_apply]
  simp_rw [mul_add]
  rw [intervalIntegral.integral_add, mul_add] <;>
    apply Continuous.intervalIntegrable <;> unfold radialPotential <;> fun_prop

theorem iter_add (j : ℕ) (ξ ρ : ℝ) {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g) (k : ℕ) :
    (volterraOp j ξ ρ)^[k] (f+g) = (volterraOp j ξ ρ)^[k] f + (volterraOp j ξ ρ)^[k] g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply',ih,op_add j ξ ρ (iter_continuous j ξ ρ hf k) (iter_continuous j ξ ρ hg k)]

theorem op_congr_disk (j : ℕ) (ξ ρ : ℝ) {f g : ℂ → ℂ}
    (h : ∀ w : ℂ, ‖w‖ ≤ 1 → f w = g w) (v : ℂ) (hv : ‖v‖ ≤ 1) :
    volterraOp j ξ ρ f v = volterraOp j ξ ρ g v := by
  unfold volterraOp
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only
  rw [h _ (radial_shrink (s := s) (by simpa only [uIcc_of_le zero_le_one] using hs) hv)]

private theorem op_bound (j : ℕ) (ξ ρ : ℝ) (hρ : 0 < ρ) (f : ℂ → ℂ) (B : ℝ)
    (l : ℕ) (hb : ∀ w : ℂ, ‖w‖ ≤ 1 → ‖f w‖ ≤ B*‖w‖^l/(l.factorial:ℝ))
    (v : ℂ) (hv : ‖v‖ ≤ 1) :
    ‖volterraOp j ξ ρ f v‖ ≤ circleQ j ξ ρ * B * ‖v‖^(l+2)/((l+2).factorial:ℝ) := by
  let Q := circleQ j ξ ρ
  let C := Q*B*‖v‖^l
  have hpoint (s : ℝ) (hs : s ∈ Ioc 0 1) :
      ‖((1-s:ℝ):ℂ)*radialPotential j ξ ρ ((s:ℂ)*v)*f ((s:ℂ)*v)‖ ≤
        C*((1-s)*s^l/(l.factorial:ℝ)) := by
    have hs' : s ∈ Icc 0 1 := ⟨hs.1.le,hs.2⟩
    have hw := radial_shrink hs' hv
    calc
      _ = (1-s)*‖radialPotential j ξ ρ ((s:ℂ)*v)‖*‖f ((s:ℂ)*v)‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.2)]
      _ ≤ (1-s)*Q*(B*‖(s:ℂ)*v‖^l/(l.factorial:ℝ)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left (radial_q_bound j ξ ρ hρ _ hw) (sub_nonneg.mpr hs.2))
          (hb _ hw) (norm_nonneg _) (mul_nonneg (sub_nonneg.mpr hs.2) (by dsimp [Q,circleQ]; positivity))
      _ = _ := by simp [C, norm_mul, abs_of_pos hs.1, mul_pow]; ring
  have hI := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) zero_le_one
    (Filter.Eventually.of_forall hpoint) (Continuous.intervalIntegrable (by fun_prop) ..)
  rw [intervalIntegral.integral_const_mul, factorial_integral] at hI
  rw [volterraOp, norm_mul, norm_neg, norm_pow]
  apply (mul_le_mul_of_nonneg_left hI (sq_nonneg _)).trans_eq
  dsimp only [C,Q]
  ring

theorem iter_bound (j : ℕ) (ξ ρ : ℝ) (hρ : 0 < ρ) (f : ℂ → ℂ) (B : ℝ)
    (l : ℕ) (hb : ∀ w : ℂ, ‖w‖ ≤ 1 → ‖f w‖ ≤ B*‖w‖^l/(l.factorial:ℝ))
    (k : ℕ) (v : ℂ) (hv : ‖v‖ ≤ 1) :
    ‖((volterraOp j ξ ρ)^[k] f) v‖ ≤
      (circleQ j ξ ρ)^k * B * ‖v‖^(2*k+l)/((2*k+l).factorial:ℝ) := by
  induction k generalizing v with
  | zero => simpa using hb v hv
  | succ k ih =>
    rw [Function.iterate_succ_apply', show 2*(k+1)+l = (2*k+l)+2 by omega]
    apply (op_bound j ξ ρ hρ _ _ (2*k+l) ih v hv).trans_eq
    ring

theorem volterra_factorial_bounds (j : ℕ) (ξ ρ : ℝ) (hρ : 0 < ρ)
    (k : ℕ) (v : ℂ) (hv : ‖v‖ ≤ 1) :
    let T := volterraOp j ξ ρ
    let A := radialMode j ξ ρ 0
    let δ := radialSlope j ξ ρ
    let Q := circleQ j ξ ρ
    let evenBound := Q^k * ‖A‖ * ‖v‖^(2*k) / ((2*k).factorial : ℝ)
    let oddBound := Q^k * ‖δ‖ * ‖v‖^(2*k+1) / ((2*k+1).factorial : ℝ)
    ‖(T^[k] (fun _ => A)) v‖ ≤ evenBound ∧
    ‖(T^[k] (fun w => δ*w)) v‖ ≤ oddBound ∧
    ‖volterraTerm j ξ ρ k v‖ ≤ evenBound + oddBound := by
  let A := radialMode j ξ ρ 0
  let d := radialSlope j ξ ρ
  let T := volterraOp j ξ ρ
  have he := iter_bound j ξ ρ hρ (fun _ => A) ‖A‖ 0 (fun w _ => by simp) k v hv
  have ho := iter_bound j ξ ρ hρ (fun w => d*w) ‖d‖ 1 (fun w _ => by simp [norm_mul]) k v hv
  simp only [add_zero] at he
  refine ⟨he,ho,?_⟩
  have hsum : radialAffine j ξ ρ = (fun _ => A) + (fun w => d*w) := rfl
  rw [volterraTerm, hsum, iter_add j ξ ρ continuous_const (by fun_prop) k, Pi.add_apply]
  exact (norm_add_le ..).trans (add_le_add he ho)

end Turan.LowerTailSteps
