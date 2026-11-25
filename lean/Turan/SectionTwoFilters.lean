-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.SectionTwoAlgebraDefs
import Turan.Degree
import Turan.Hermite

noncomputable section
open Polynomial Filter Metric
open scoped Topology BigOperators Classical
namespace Turan.SectionTwo

theorem twice_EStar_hermite (k : ℕ) :
    2 * EStar (hermite k) = -C (lambda k : ℂ) * hermite k := by
  apply Polynomial.funext
  intro z
  have h := congrArg (eval z) (hermite_equation k)
  simp only [EStar, lambda, eval_sub, eval_mul, eval_neg, eval_X, eval_C, eval_ofNat,
    nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, eval_natCast, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_natCast] at h ⊢
  linear_combination h

theorem single_filter_action (μ : ℝ) (hμ : 0 < μ) (k : ℕ) :
    realFilter μ (hermite k) = C ((1 - lambda k / μ : ℝ) : ℂ) * hermite k ∧
    (realFilter μ (hermite k) = 0 ↔ lambda k = μ) := by
  have he : realFilter μ (hermite k) = C ((1 - lambda k / μ : ℝ) : ℂ) * hermite k := by
    unfold realFilter
    have h := twice_EStar_hermite k
    simp only [div_eq_mul_inv, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_one, map_sub, map_one, map_mul, map_ofNat]
    linear_combination C (μ : ℂ)⁻¹ * h
  have hH : hermite k ≠ 0 := fun h => by
    have htop := (hermite_degree k).2
    simp [h] at htop
    exact (pow_ne_zero k (by norm_num : (2 : ℂ) ≠ 0)) htop.symm
  refine ⟨he, ?_⟩
  rw [he, mul_eq_zero, or_iff_left hH, C_eq_zero, Complex.ofReal_eq_zero,
    sub_eq_zero, eq_comm (a := (1 : ℝ)), div_eq_one_iff_eq hμ.ne']

end Turan.SectionTwo
