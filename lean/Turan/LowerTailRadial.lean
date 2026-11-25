-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Volterra
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open Filter Metric Set Polynomial
open scoped ComplexConjugate Topology
namespace Turan.LowerTailSteps

def radialMode (j : ℕ) (ξ ρ : ℝ) (v : ℂ) : ℂ := phi j ((ξ : ℂ) + ρ*v)

def radialSlope (j : ℕ) (ξ ρ : ℝ) : ℂ := (ρ : ℂ) * deriv (phi j) (ξ : ℂ)

def radialPotential (j : ℕ) (ξ ρ : ℝ) (v : ℂ) : ℂ :=
  (ρ : ℂ)^2 * (2*(j:ℂ)+1-((ξ:ℂ)+ρ*v)^2)

def volterraOp (j : ℕ) (ξ ρ : ℝ) (f : ℂ → ℂ) (v : ℂ) : ℂ :=
  -v^2 * ∫ t : ℝ in 0..1,
    ((1-t : ℝ) : ℂ) * radialPotential j ξ ρ ((t : ℂ)*v) * f ((t : ℂ)*v)

def radialAffine (j : ℕ) (ξ ρ : ℝ) (v : ℂ) : ℂ :=
  radialMode j ξ ρ 0 + radialSlope j ξ ρ * v

def volterraTerm (j : ℕ) (ξ ρ : ℝ) (k : ℕ) : ℂ → ℂ :=
  (volterraOp j ξ ρ)^[k] (radialAffine j ξ ρ)

theorem factorial_integral (ℓ : ℕ) :
    (∫ t : ℝ in 0..1, (1-t)*t^ℓ / (ℓ.factorial : ℝ)) = 1/((ℓ+2).factorial : ℝ) := by
  simp_rw [sub_mul, one_mul, ← pow_succ']
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) ..)
    (Continuous.intervalIntegrable (by fun_prop) ..), integral_pow, integral_pow]
  simp [Nat.factorial_succ]
  field_simp
  ring

theorem radial_q_bound (j : ℕ) (ξ ρ : ℝ) (hρ : 0 < ρ) (v : ℂ) (hv : ‖v‖ ≤ 1) :
    ‖radialPotential j ξ ρ v‖ ≤ circleQ j ξ ρ := by
  have hw : ‖(ρ:ℂ)*v‖ ≤ ρ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hρ]
    exact mul_le_of_le_one_right hρ.le hv
  unfold radialPotential circleQ
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hρ,norm_sub_rev]
  exact mul_le_mul_of_nonneg_left (oscillator_coeff j ξ ρ _ hw) (sq_nonneg _)

theorem mode_continuous (j : ℕ) (ξ ρ : ℝ) : Continuous (radialMode j ξ ρ) :=
  (continuous_iff_continuousAt.mpr (fun w => ((phi_equation j).1 w).continuousAt)).comp
    (continuous_const.add (continuous_const.mul continuous_id))

theorem radial_integral_equation (j : ℕ) (ξ ρ : ℝ) (hρ : 0 < ρ) (v : ℂ) (hv : ‖v‖ ≤ 1) :
    ‖radialPotential j ξ ρ v‖ ≤ circleQ j ξ ρ ∧
    radialMode j ξ ρ v = radialAffine j ξ ρ v + volterraOp j ξ ρ (radialMode j ξ ρ) v := by
  refine ⟨radial_q_bound j ξ ρ hρ v hv, ?_⟩
  let a := (ρ:ℂ)*v
  let z (s : ℂ) := (ξ:ℂ)+s*a
  let U (s : ℝ) := phi j (z s)
  let V (s : ℝ) := deriv (phi j) (z s)*a
  let F (s : ℝ) := U s + ((1:ℂ)-s)*V s
  let f (s : ℝ) := ((1-s:ℝ):ℂ)*radialPotential j ξ ρ ((s:ℂ)*v)*radialMode j ξ ρ ((s:ℂ)*v)
  have hz (s : ℂ) : HasDerivAt z a s := by simpa [z] using ((hasDerivAt_id s).mul_const a).const_add (ξ:ℂ)
  have hu (s : ℝ) : HasDerivAt U (V s) s := (((phi_equation j).1 _).comp (s:ℂ) (hz s)).comp_ofReal
  have hV (s : ℝ) : HasDerivAt V (((z s)^2-(2*(j:ℂ)+1))*U s*a*a) s :=
    ((((phi_equation j).2 _).comp (s:ℂ) (hz s)).mul_const a).comp_ofReal
  have hF (s : ℝ) : HasDerivAt F (-v^2*f s) s := by
    convert (hu s).add ((((hasDerivAt_id (s:ℂ)).const_sub 1).comp_ofReal).mul (hV s)) using 1
    · rfl
    have hid : (ξ:ℂ)+ρ*((s:ℂ)*v) = z s := by dsimp [z,a]; ring
    dsimp only [f,radialPotential,radialMode,U]
    rw [hid]
    push_cast
    dsimp only [a]
    simp only [id]
    ring
  have hc : Continuous f := by
    dsimp [f]
    apply Continuous.mul _ ((mode_continuous j ξ ρ).comp (by fun_prop))
    unfold radialPotential
    fun_prop
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
    (fun s _ => hF s) ((continuous_const.mul hc).intervalIntegrable ..)
  rw [intervalIntegral.integral_const_mul] at H
  simp [F,U,V,z,a] at H
  change _ = _ + (-v^2)*(∫ s in (0:ℝ)..1, f s)
  unfold radialMode radialAffine radialSlope
  simp only [radialMode, mul_zero, add_zero]
  linear_combination -H

end Turan.LowerTailSteps
