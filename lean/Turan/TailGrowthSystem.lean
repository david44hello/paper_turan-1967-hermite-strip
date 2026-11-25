-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.ODE.Gronwall

noncomputable section
open Polynomial Metric
namespace Turan

/-- The four filtered polynomials in the coordinate t = Ω (w - z). -/
structure TailGrowthSystem where
  P : ℕ → Polynomial ℂ
  A : ℂ → ℂ
  c : ℕ → ℂ
  step : ∀ i < 4, ∀ t, (P (i+1)).eval t = (P i).derivative.derivative.eval t -
    A t * (P i).derivative.eval t + c i * (P i).eval t
  terminal : P 4 = 0
  drift : ∀ t, ‖t‖ ≤ 7 → ‖A t‖ ≤ 0.56
  diagonal : ∀ i < 4, ‖c i‖ ≤ 1

namespace TailGrowthSystem

private abbrev scale : ℂ := ((4/7 : ℝ) : ℂ)

private theorem scale_norm : ‖scale‖ = 4/7 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]

variable (S : TailGrowthSystem)

def state (t : ℂ) (i : Fin 4) : ℂ × ℂ :=
  ((S.P i).eval t, (S.P i).derivative.eval t * scale)

private def rate (t : ℂ) (i : Fin 4) : ℂ × ℂ :=
  ((S.P i).derivative.eval t, (S.P i).derivative.derivative.eval t * scale)

theorem value_le_state (t : ℂ) (i : Fin 4) : ‖(S.P i).eval t‖ ≤ ‖S.state t‖ :=
  (norm_fst_le (S.state t i)).trans (norm_le_pi_norm _ i)

private theorem rate_bound (t : ℂ) (ht : ‖t‖ ≤ 7) :
    ‖S.rate t‖ ≤ 1.75 * ‖S.state t‖ := by
  apply pi_norm_le_iff_of_nonneg (by positivity) |>.2
  intro i
  have hd := (norm_snd_le (S.state t i)).trans (norm_le_pi_norm _ i)
  change ‖(S.P i).derivative.eval t * scale‖ ≤ _ at hd
  rw [norm_mul, scale_norm] at hd
  have hd' : ‖(S.P i).derivative.eval t‖ ≤ 1.75 * ‖S.state t‖ := by linarith
  have hn : ‖(S.P (i.val+1)).eval t‖ ≤ ‖S.state t‖ := by
    by_cases h : i.val+1 < 4
    · exact S.value_le_state t ⟨i.val+1,h⟩
    · have he : i.val+1 = 4 := by omega
      simp [he, S.terminal]
  have he : (S.P i).derivative.derivative.eval t =
      (S.P (i.val+1)).eval t + S.A t * (S.P i).derivative.eval t - S.c i * (S.P i).eval t := by
    rw [S.step i i.isLt]
    ring
  apply norm_prod_le_iff.mpr ⟨hd', ?_⟩
  change ‖(S.P i).derivative.derivative.eval t * scale‖ ≤ _
  rw [norm_mul, scale_norm, he]
  have htri := (norm_sub_le ((S.P (i.val+1)).eval t + S.A t * (S.P i).derivative.eval t)
    (S.c i * (S.P i).eval t)).trans (add_le_add_left (norm_add_le ..) _)
  simp only [norm_mul] at htri
  have hA := mul_le_mul (S.drift t ht) hd' (norm_nonneg _) (by norm_num)
  have hc := mul_le_mul (S.diagonal i i.isLt) (S.value_le_state t i) (norm_nonneg _) zero_le_one
  linarith only [htri, hn, hA, hc, norm_nonneg (S.state t)]

/-- Integrate the eight-component differential inequality along the radius from 0 to v. -/
theorem radial_state_le (v : ℂ) (hv : ‖v‖ ≤ 7) :
    ‖S.state v‖ ≤ Real.exp (1.75 * ‖v‖) * ‖S.state 0‖ := by
  let f (x : ℝ) := S.state ((x:ℂ)*v)
  let f' (x : ℝ) := v • S.rate ((x:ℂ)*v)
  have hf (x : ℝ) : HasDerivAt f (f' x) x := by
    apply hasDerivAt_pi.mpr
    intro i
    have hline : HasDerivAt (fun t : ℂ => t*v) v (x:ℂ) := by
      simpa using (hasDerivAt_id (x:ℂ)).mul_const v
    have h (p : Polynomial ℂ) := ((p.hasDerivAt _).comp (x:ℂ) hline).comp_ofReal
    simpa [f, f', state, rate, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Function.comp_def]
      using (h (S.P i)).prodMk ((h (S.P i).derivative).mul_const scale)
  have hb (x : ℝ) (hx : x ∈ Set.Ico (0:ℝ) 1) : ‖f' x‖ ≤ (1.75 * ‖v‖) * ‖f x‖ + 0 := by
    have hrad : ‖(x:ℂ)*v‖ ≤ 7 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact (mul_le_mul_of_nonneg_right hx.2.le (norm_nonneg _)).trans (by simpa using hv)
    rw [show ‖f' x‖ = ‖v‖ * ‖S.rate ((x:ℂ)*v)‖ by exact norm_smul _ _]
    have h := mul_le_mul_of_nonneg_left (S.rate_bound _ hrad) (norm_nonneg v)
    dsimp [f]
    linarith
  have h := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := f) (f' := f') (a := 0) (b := 1)
    (fun x _ => (hf x).continuousAt.continuousWithinAt)
    (fun x _ => (hf x).hasDerivWithinAt) (le_refl ‖f 0‖) hb 1 (by simp)
  simpa [f, gronwallBound_ε0, mul_comm] using h

/-- The outer-disk bound for the initial polynomial. -/
theorem radial (v : ℂ) (hv : ‖v‖ ≤ 7) :
    ‖(S.P 0).eval v‖ ≤ Real.exp 12.25 * ‖S.state 0‖ := by
  refine (S.value_le_state v 0).trans ((S.radial_state_le v hv).trans ?_)
  gcongr
  linarith

/-- First and second polynomial derivatives on a disk of radius one half. -/
theorem cauchy_half (p : Polynomial ℂ) (t : ℂ) (B : ℝ)
    (h : ∀ w ∈ sphere t (1/2), ‖p.eval w‖ ≤ B) :
    ‖p.derivative.eval t‖ ≤ 2*B ∧ ‖p.derivative.derivative.eval t‖ ≤ 8*B := by
  have h₁ := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : 0 < (1:ℝ)/2)
    p.differentiable.diffContOnCl h
  have h₂ := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2
    (by norm_num : 0 < (1:ℝ)/2) p.differentiable.diffContOnCl h
  have hd : deriv (fun w => p.eval w) = fun w => p.derivative.eval w := funext fun _ => p.deriv
  rw [show (2:ℕ) = 1+1 by decide, iteratedDeriv_succ, iteratedDeriv_one, hd, Polynomial.deriv] at h₂
  rw [Polynomial.deriv] at h₁
  norm_num at h₁ h₂
  constructor <;> linarith

/-- Successive Cauchy estimates, losing half a unit of radius at each filter. -/
theorem state_at_zero (B : ℝ) (hB : 0 ≤ B) (h : ∀ t : ℂ, ‖t‖ ≤ 2 → ‖(S.P 0).eval t‖ ≤ B) :
    ‖S.state 0‖ ≤ 1600 * B := by
  have stages (i : ℕ) (hi : i ≤ 3) (t : ℂ) (ht : ‖t‖ ≤ 2 - (i:ℝ)/2) :
      ‖(S.P i).eval t‖ ≤ 11^i*B := by
    induction i generalizing t with
    | zero => simpa using h t (by simpa using ht)
    | succ i ih =>
      have hprev := ih (by omega) t (by push_cast at ht; linarith)
      have hcircle (w : ℂ) (hw : w ∈ sphere t (1/2)) : ‖(S.P i).eval w‖ ≤ 11^i*B := by
        apply ih (by omega)
        have hdist := mem_sphere_iff_norm.mp hw
        have htri := norm_add_le (w-t) t
        rw [sub_add_cancel, hdist] at htri
        push_cast at ht
        linarith
      obtain ⟨hd,hdd⟩ := cauchy_half (S.P i) t _ hcircle
      have hA := mul_le_mul (S.drift t (by push_cast at ht; linarith [Nat.cast_nonneg (α := ℝ) i]))
        hd (norm_nonneg _) (by norm_num)
      have hc := mul_le_mul (S.diagonal i (by omega)) hprev (norm_nonneg _) zero_le_one
      rw [S.step i (by omega)]
      have htri := (norm_add_le ((S.P i).derivative.derivative.eval t - S.A t * (S.P i).derivative.eval t)
        (S.c i * (S.P i).eval t)).trans (add_le_add_left (norm_sub_le ..) _)
      simp only [norm_mul] at htri
      rw [pow_succ]
      nlinarith only [htri, hdd, hA, hc, show 0 ≤ (11:ℝ)^i * B by positivity]
  apply pi_norm_le_iff_of_nonneg (by positivity) |>.2
  intro i
  have hi : i.val ≤ 3 := by omega
  have hR : (1:ℝ)/2 ≤ 2 - (i:ℝ)/2 := by linarith [show (i.val:ℝ) ≤ 3 by exact_mod_cast hi]
  have hval := stages i hi 0 (by simpa using (le_trans (by norm_num : (0:ℝ) ≤ 1/2) hR))
  have hder := (cauchy_half (S.P i) 0 _ (fun w hw =>
    stages i hi w (by simpa using (mem_sphere_iff_norm.mp hw).le.trans hR))).1
  have hp : (11:ℝ)^i.val ≤ 1331 := by
    calc _ ≤ (11:ℝ)^3 := pow_le_pow_right₀ (by norm_num) hi
         _ = _ := by norm_num
  have hpow := mul_le_mul_of_nonneg_right hp hB
  apply norm_prod_le_iff.mpr
  change ‖(S.P i).eval 0‖ ≤ _ ∧ ‖(S.P i).derivative.eval 0 * scale‖ ≤ _
  rw [norm_mul, scale_norm]
  constructor <;> linarith

end TailGrowthSystem
end Turan
