module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Hermite
public import Turan.Normalized
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Polynomial Metric
namespace Turan

private def gen (z t : ℂ) := Complex.exp (2*z*t-t^2)

private theorem raise_eval (n : ℕ) (v : ℂ) :
    (hermite (n+1)).eval v = 2*v*(hermite n).eval v - (hermite n).derivative.eval v := by
  cases n with
  | zero => simp [hermite, eval_mul]
  | succ n => rw [hermite, hermite_derivative, eval_sub, eval_mul, eval_mul, eval_X, eval_ofNat]

/-- Differentiation raises the Hermite index at the translated argument z-t. -/
private theorem gen_deriv (z : ℂ) (n : ℕ) :
    iteratedDeriv n (gen z) = fun t => (hermite n).eval (z-t)*gen z t := by
  induction n with
  | zero => funext t; simp [hermite]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hg : HasDerivAt (gen z) ((2*z-2*t)*gen z t) t := by
      convert ((((hasDerivAt_id t).const_mul (2*z)).sub ((hasDerivAt_id t).pow 2)).cexp) using 1
      · rfl
      · change (2*z-2*t)*gen z t = gen z t*(2*z*1 - (2:ℂ)*t^(2-1)*1)
        ring
    have hh := ((hermite n).hasDerivAt (z-t)).comp t ((hasDerivAt_id t).const_sub z)
    rw [raise_eval]
    convert (hh.mul hg).deriv using 1
    all_goals first | rfl | (simp [Function.comp_apply]; ring)

theorem hermite_generating (z t : ℂ) :
    HasSum (fun k : ℕ => (hermite k).eval z * t^k / (k.factorial:ℂ))
      (Complex.exp (2*z*t-t^2)) := by
  apply (Complex.hasSum_taylorSeries_of_entire (f := gen z) (by unfold gen; fun_prop) 0 t).congr_fun
  intro n
  simp [gen_deriv, gen, smul_eq_mul, div_eq_mul_inv]
  ring

/-- Apply Cauchy's estimate at radius √k and use k! ≤ k^k. -/
theorem normalized_cauchy_bound (k : ℕ) (hk : 1 ≤ k) (z : ℂ) :
    ‖psi k z‖ ≤ (Real.exp 1 / Real.sqrt 2)^k * Real.exp (2*‖z‖*Real.sqrt k) := by
  let R := Real.sqrt k
  have hk₀ : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hR : 0 < R := Real.sqrt_pos.mpr hk₀
  have hR2 : R^2 = (k:ℝ) := Real.sq_sqrt hk₀.le
  have hd : Differentiable ℂ (gen z) := by unfold gen; fun_prop
  have hb := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (f := gen z) k hR
    (hd.diffContOnCl (s := ball (0:ℂ) R)) (C := Real.exp (2*‖z‖*R+k)) (by
      intro w hw
      have h := mem_sphere_zero_iff_norm.mp hw
      rw [gen, Complex.norm_exp, Real.exp_le_exp]
      exact (Complex.re_le_norm _).trans ((norm_sub_le _ _).trans (by
        simp [norm_pow, h, hR2])))
  simp only [gen_deriv, sub_zero, gen, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, sub_self, Complex.exp_zero, mul_one] at hb
  have hfac : Real.sqrt (k.factorial : ℝ) ≤ R^k := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), ← pow_mul, Nat.mul_comm k, pow_mul, hR2]
    exact_mod_cast Nat.factorial_le_pow k
  have hd₂ : Real.sqrt (2^k * (k.factorial:ℝ)) = Real.sqrt 2 ^ k * Real.sqrt (k.factorial:ℝ) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), mul_pow, ← pow_mul, Nat.mul_comm k, pow_mul,
      Real.sq_sqrt (by norm_num), Real.sq_sqrt (by positivity)]
  have hfact := Real.sq_sqrt (by positivity : 0 ≤ (k.factorial:ℝ))
  have hexp : Real.exp (2*‖z‖*R+k) = Real.exp (2*‖z‖*R) * Real.exp 1 ^ k := by
    rw [Real.exp_add, ← Real.exp_nat_mul]; simp
  rw [hexp, le_div_iff₀ (pow_pos hR k)] at hb
  have hn : ‖(hermite k).eval z‖ ≤ Real.exp 1 ^ k * Real.exp (2*‖z‖*R) * Real.sqrt (k.factorial:ℝ) := by
    apply le_of_mul_le_mul_right (a := Real.sqrt (k.factorial:ℝ)) _ (by positivity)
    calc
      _ ≤ ‖(hermite k).eval z‖ * R^k := mul_le_mul_of_nonneg_left hfac (norm_nonneg _)
      _ ≤ _ := hb
      _ = _ := by linear_combination -(Real.exp 1 ^ k * Real.exp (2*‖z‖*R)) * hfact
  rw [psi, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), hd₂,
    div_le_iff₀ (by positivity), div_pow]
  convert hn using 1
  dsimp [R]
  field_simp

theorem mehler_term_majorant (k : ℕ) (z w : ℂ) :
    ‖((1:ℂ)/5)^k * psi k z * psi k w‖ ≤
      (Real.exp 1 ^ 2/10)^k * Real.exp (2*Real.sqrt k*(‖z‖+‖w‖)) := by
  cases k with
  | zero => simp [psi, hermite]
  | succ n =>
    let k := n+1
    have h := mul_le_mul (normalized_cauchy_bound k (by omega) z)
      (normalized_cauchy_bound k (by omega) w) (norm_nonneg _) (by positivity)
    calc
      _ = (1/5:ℝ)^k * (‖psi k z‖*‖psi k w‖) := by simp [k, norm_pow, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by
        rw [show (1/5:ℝ)^k * (((Real.exp 1 / Real.sqrt 2)^k * Real.exp (2*‖z‖*Real.sqrt k)) *
            ((Real.exp 1 / Real.sqrt 2)^k * Real.exp (2*‖w‖*Real.sqrt k))) =
            (1/5*(Real.exp 1 / Real.sqrt 2)^2)^k *
            (Real.exp (2*‖z‖*Real.sqrt k)*Real.exp (2*‖w‖*Real.sqrt k)) by
              rw [mul_pow, sq, mul_pow]; ring]
        rw [div_pow, Real.sq_sqrt (by norm_num), ← Real.exp_add]
        congr 2 <;> ring

theorem mehler_growth_ratio : Real.exp 1 ^ 2 / 10 < (74:ℝ)/100 := by
  nlinarith [sq_lt_sq₀ (Real.exp_pos 1).le (by norm_num) |>.2 Real.exp_one_lt_d9]

end Turan
