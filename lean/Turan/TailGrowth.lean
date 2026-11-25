-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.TailDefs
import Turan.Hermite
import Turan.TailGrowthSystem

noncomputable section
open Polynomial Metric
namespace Turan

namespace TailGrowth

private def coord (z s : ℂ) : Polynomial ℂ := C z + C s * X

private theorem coord_deriv (z s : ℂ) : (coord z s).derivative = C s := by
  simp [coord]

private def mode (z s : ℂ) (j : ℕ) := (hermite j).comp (coord z s)
private def eigen (s : ℂ) (j : ℕ) := 2 * s^2 * (j:ℂ)
private def filterOp (z s c : ℂ) (p : Polynomial ℂ) :=
  p.derivative.derivative - C (2*s) * coord z s * p.derivative + C c * p

private theorem filter_add (z s c : ℂ) (p q : Polynomial ℂ) :
    filterOp z s c (p+q) = filterOp z s c p + filterOp z s c q := by
  simp only [filterOp, derivative_add]
  ring

private theorem filter_const_mul (z s c d : ℂ) (p : Polynomial ℂ) :
    filterOp z s c (C d * p) = C d * filterOp z s c p := by
  simp only [filterOp, derivative_C_mul]
  ring

/-- After the affine change of variable the Hermite equation diagonalizes every filter. -/
private theorem filter_mode (z s c : ℂ) (j : ℕ) :
    filterOp z s c (mode z s j) = C (c - eigen s j) * mode z s j := by
  have h := congrArg (fun p : Polynomial ℂ => p.comp (coord z s)) (hermite_equation j)
  simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, sub_comp, mul_comp, ofNat_comp,
    X_comp, neg_comp, natCast_comp] at h
  simp only [filterOp, mode, derivative_comp, coord_deriv, derivative_C_mul, eigen,
    map_sub, map_mul, map_pow, map_ofNat, map_natCast]
  linear_combination (C s)^2 * h

private def index (n m : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => n
  | _ => m

private def coef (j : ℕ) (a : ℂ) := a / (Real.sqrt (2^j * (j.factorial:ℝ)) : ℂ)

private def stage (n m : ℕ) (a b z s : ℂ) : ℕ → Polynomial ℂ
  | 0 => mode z s 0 + mode z s 1 +
      C (coef n a) * mode z s n + C (coef m b) * mode z s m
  | i+1 => filterOp z s (eigen s (index n m i)) (stage n m a b z s i)

private theorem stage_terminal (n m : ℕ) (a b z s : ℂ) :
    stage n m a b z s 4 = 0 := by
  simp only [stage, index, filter_add, filter_const_mul, filter_mode, sub_self,
    map_zero, zero_mul, mul_zero, zero_add]

private theorem stage_start (n m : ℕ) (a b z s t : ℂ) :
    (stage n m a b z s 0).eval t = normalizedFamily n m a b (z+s*t) := by
  simp only [stage, mode, eval_add, eval_comp, eval_mul, eval_C, coord, eval_X,
    normalizedFamily, psi, coef, hermite, eval_one, eval_ofNat]
  ring

private theorem omega_bounds (m : ℕ) (hm : 450 ≤ m) (z : ℂ) :
    30 ≤ omega m z ∧ |z.re| ≤ omega m z / 4 ∧ 2*(m:ℝ) ≤ (omega m z)^2 := by
  have hsq : (omega m z)^2 = 2*(m:ℝ) + 16*z.re^2 := Real.sq_sqrt (by positivity)
  have hnon : 0 ≤ omega m z := Real.sqrt_nonneg _
  have hm' : (450:ℝ) ≤ m := by exact_mod_cast hm
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [sq_nonneg z.re]
  · nlinarith [sq_abs z.re, abs_nonneg z.re, Nat.cast_nonneg (α := ℝ) m]
  · nlinarith [sq_nonneg z.re]

/-- Instantiate the polynomial system on the normalized disk. -/
private theorem system_exists (n m : ℕ) (hm : 450 ≤ m) (hnm : n < m) (a b z : ℂ)
    (hz : |z.im| ≤ 7/11) :
    ∃ S : TailGrowthSystem, ∀ t : ℂ,
      (S.P 0).eval t = normalizedFamily n m a b (z + ((omega m z : ℂ)⁻¹)*t) := by
  let O := omega m z
  let s : ℂ := (O:ℂ)⁻¹
  obtain ⟨hO, hx, hmO⟩ := omega_bounds m hm z
  change 30 ≤ O at hO
  change |z.re| ≤ O/4 at hx
  change 2*(m:ℝ) ≤ O^2 at hmO
  have hp : 0 < O := by linarith
  have hs : ‖s‖ = O⁻¹ := by
    simp only [s, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  refine ⟨{ P := stage n m a b z s
            A := fun t => 2*s*(z+s*t)
            c := fun i => eigen s (index n m i)
            step := ?_
            terminal := stage_terminal ..
            drift := ?_
            diagonal := ?_ }, fun t => stage_start n m a b z s t⟩
  · intro i _ t
    simp only [stage, filterOp, coord, eval_add, eval_sub, eval_mul, eval_C, eval_X]
  · intro t ht
    have hst : ‖s*t‖ ≤ 7/O := by
      rw [norm_mul, hs, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left ht (by positivity)
    have hball : 7/O ≤ 7/30 := by gcongr
    have hz' := Complex.norm_le_abs_re_add_abs_im z
    have hr := norm_add_le z (s*t)
    have hsmall : ‖z+s*t‖ ≤ 0.28 * O := by linarith
    rw [norm_mul, norm_mul, hs]
    norm_num
    calc 2 * O⁻¹ * ‖z+s*t‖ ≤ 2 * O⁻¹ * (0.28 * O) := by gcongr
         _ = _ := by field_simp; ring
  · intro i hi
    have hk : index n m i ≤ m := by
      interval_cases i <;> simp [index] <;> omega
    have hk' : (index n m i : ℝ) ≤ m := by exact_mod_cast hk
    simp only [eigen, norm_mul, norm_pow, hs, Complex.norm_natCast]
    norm_num
    rw [← div_eq_mul_inv]
    calc 2 / O^2 * (index n m i : ℝ) = (2*(index n m i : ℝ)) / O^2 := by ring
         _ ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)

/-- A rational lower Taylor bound for the numerical conversion in Appendix A.2. -/
private theorem exp_budget : Real.exp 12.25 * 1600 ≤ Real.exp 19.628 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : 0 ≤ (0.7378:ℝ)) 8
  have hl : (2.0913:ℝ) ≤ Real.exp 0.7378 := by
    refine le_trans ?_ h
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hpow := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.0913) hl 10
  have hb : (1600:ℝ) ≤ Real.exp 7.378 := by
    rw [show (7.378:ℝ) = (10:ℕ)*0.7378 by norm_num, Real.exp_nat_mul]
    exact le_trans (by norm_num) hpow
  calc _ ≤ Real.exp 12.25 * Real.exp 7.378 := by gcongr
       _ = _ := by rw [← Real.exp_add]; norm_num

end TailGrowth

open TailGrowth in
theorem tailGrowth_doubling (n m : ℕ) (hm : 450 ≤ m)
    (hhalf : m ≤ 2*n) (hnm : n < m) (a b : ℂ)
    (hs : emptyStrip (normalizedFamily n m a b) (87/100))
    (z : ℂ) (hz : |z.im| ≤ 7/11) :
    ∃ M : ℝ, 0 < M ∧
      (∀ w ∈ Metric.closedBall z (7 / omega m z),
        ‖normalizedFamily n m a b w‖ ≤ M) ∧
      ∃ z₁ ∈ Metric.closedBall z (2 / omega m z),
        M ≤ Real.exp 19.628 * ‖normalizedFamily n m a b z₁‖ := by
  obtain ⟨S, hS⟩ := system_exists n m hm hnm a b z hz
  let O := omega m z
  have hO : 0 < O := lt_of_lt_of_le (by norm_num : (0:ℝ) < 30) (omega_bounds m hm z).1
  have hOc : (O:ℂ) ≠ 0 := by exact_mod_cast hO.ne'
  let q (t : ℂ) := z + (O:ℂ)⁻¹*t
  change ∀ t, (S.P 0).eval t = normalizedFamily n m a b (q t) at hS
  have hnorm : ‖(O:ℂ)‖ = O := by simp [abs_of_pos hO]
  obtain ⟨t₁, ht₁, hmax⟩ := (isCompact_closedBall (0:ℂ) 2).exists_isMaxOn
    (nonempty_closedBall.mpr (by norm_num)) (S.P 0).continuous.norm.continuousOn
  let B := ‖(S.P 0).eval t₁‖
  have hB (t : ℂ) (ht : ‖t‖ ≤ 2) : ‖(S.P 0).eval t‖ ≤ B :=
    hmax (by simpa [mem_closedBall, dist_eq_norm] using ht)
  have hBpos : 0 < B := by
    apply lt_of_lt_of_le _ (hB 0 (by simp))
    rw [hS, norm_pos_iff]
    simpa [q] using hs z (lt_of_le_of_lt hz (by norm_num))
  have hstate := S.state_at_zero B hBpos.le hB
  refine ⟨Real.exp 12.25 * 1600 * B, by positivity, ?_, q t₁, ?_, ?_⟩
  · intro w hw
    let t := (O:ℂ)*(w-z)
    have ht : ‖t‖ ≤ 7 := by
      rw [show ‖t‖ = O*‖w-z‖ by simp only [t, norm_mul, hnorm]]
      have hd := (le_div_iff₀ hO).mp (mem_closedBall_iff_norm.mp hw)
      linarith
    have he : q t = w := by
      dsimp [q,t]
      field_simp
      ring
    rw [← he, ← hS]
    calc _ ≤ Real.exp 12.25 * ‖S.state 0‖ := S.radial t ht
         _ ≤ Real.exp 12.25 * (1600 * B) := by gcongr
         _ = _ := by ring
  · rw [mem_closedBall_iff_norm]
    simp only [q, add_sub_cancel_left, norm_mul, norm_inv, hnorm]
    rw [div_eq_inv_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa [mem_closedBall, dist_eq_norm] using ht₁
  · rw [← hS]
    exact mul_le_mul_of_nonneg_right exp_budget hBpos.le

end Turan
