module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

noncomputable section
open Polynomial Metric
namespace Turan

/-- The contribution of one linear factor whose root is off the circle. -/
private theorem integral_root_kernel {c w : ℂ} {r : ℝ} (hr : 0 < r) (hw : w ∉ sphere c r) :
    (∮ z in C(c, r), (z - w)⁻¹) = if dist w c < r then 2 * Real.pi * Complex.I else 0 := by
  by_cases hin : dist w c < r
  · rw [ite_eq_left hin]
    exact circleIntegral.integral_sub_inv_of_mem_ball hin
  · rw [ite_eq_right hin]
    have hout : w ∉ closedBall c r := fun h => hw (mem_sphere.mpr
      (le_antisymm (mem_closedBall.mp h) (le_of_not_gt hin)))
    have hd : DifferentiableOn ℂ (fun z : ℂ => (z - w)⁻¹) (closedBall c r) :=
      (differentiableOn_id.sub_const w).inv fun z hz =>
        sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hout)
    exact (hd.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero hr.le

/-- Integrate the logarithmic derivative one factor at a time, including repeated factors. -/
private theorem integral_of_root_factors (c : ℂ) (r : ℝ) (hr : 0 < r) (a : ℂ)
    (s : Multiset ℂ) (p : Polynomial ℂ) (hfac : p = C a * (s.map (X - C ·)).prod)
    (hb : ∀ z ∈ sphere c r, p.eval z ≠ 0) :
    (∮ z in C(c, r), p.derivative.eval z / p.eval z) =
      2 * Real.pi * Complex.I * ((s.filter (fun z => dist z c < r)).card : ℂ) := by
  induction s using Multiset.induction_on generalizing p with
  | empty =>
    subst p
    simp [circleIntegral]
  | cons w s ih =>
    let q := C a * (s.map (X - C ·)).prod
    have hp : p = (X - C w) * q := by rw [hfac]; simp [q, mul_left_comm]
    have hprod (z : ℂ) (hz : z ∈ sphere c r) : (z - w) * q.eval z ≠ 0 := by
      simpa [hp, eval_mul, eval_sub] using hb z hz
    have hw : w ∉ sphere c r := fun h => hprod w h (by simp)
    have hq (z : ℂ) (hz : z ∈ sphere c r) : q.eval z ≠ 0 := right_ne_zero_of_mul (hprod z hz)
    calc
      (∮ z in C(c, r), p.derivative.eval z / p.eval z) =
          ∮ z in C(c, r), (z - w)⁻¹ + q.derivative.eval z / q.eval z := by
        apply circleIntegral.integral_congr hr.le
        intro z hz
        have hzw : z - w ≠ 0 := left_ne_zero_of_mul (hprod z hz)
        simp only [hp, derivative_mul, derivative_X_sub_C, one_mul, eval_add, eval_mul,
          eval_sub, eval_X, eval_C]
        field_simp [hzw, hq z hz]
      _ = (∮ z in C(c, r), (z - w)⁻¹) + ∮ z in C(c, r), q.derivative.eval z / q.eval z := by
        apply circleIntegral.integral_add
        · rw [circleIntegrable_sub_inv_iff, abs_of_pos hr]
          exact Or.inr hw
        · exact (q.derivative.continuousOn.div q.continuousOn hq).circleIntegrable hr.le
      _ = _ := by
        rw [integral_root_kernel hr hw, ih q rfl hq]
        by_cases hin : dist w c < r
        · simp [Multiset.filter_cons_of_pos, hin, mul_add, add_comm]
        · simp [Multiset.filter_cons_of_neg, hin]

/-- The argument principle for a complex polynomial, counting each interior root with multiplicity. -/
theorem polynomial_argument_principle (p : Polynomial ℂ) (c : ℂ) (r : ℝ)
    (hr : 0 < r) (hb : ∀ z ∈ sphere c r, p.eval z ≠ 0) :
    (∮ z in C(c, r), p.derivative.eval z / p.eval z) =
      2 * Real.pi * Complex.I * ((p.roots.filter (fun z => dist z c < r)).card : ℂ) :=
  integral_of_root_factors c r hr p.leadingCoeff p.roots p (IsAlgClosed.splits p).eq_prod_roots hb

end Turan
