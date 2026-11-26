module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.GeneratingBounds
public import Turan.GeneratingKernel
public import Mathlib.Analysis.Normed.Group.FunctionSeries

@[expose] public section

noncomputable section
open Filter Metric
namespace Turan

/-- Absorb the square-root exponential into a geometric majorant, uniformly
in both arguments on a fixed ball. -/
theorem mehler_uniform_on_balls (R : ℝ) :
    TendstoUniformlyOn
      (fun N (p : ℂ × ℂ) => ∑ k ∈ Finset.range N, ((1:ℂ)/5)^k*psi k p.1*psi k p.2)
      (fun p => (Real.sqrt (1-(1/5:ℝ)^2):ℂ)⁻¹ * Complex.exp
        ((2*p.1*p.2/5-(p.1^2+p.2^2)/25)/(1-(1/5:ℂ)^2)))
      atTop (closedBall 0 R) := by
  let q := Real.exp 1 ^ 2/10
  let δ := Real.log (5/4)
  have hδ : 0 < δ := Real.log_pos (by norm_num)
  let M := Real.exp (4*R^2/δ)
  let f (k : ℕ) (p : ℂ × ℂ) := ((1:ℂ)/5)^k * psi k p.1 * psi k p.2
  have hsum (p : ℂ × ℂ) := mehler_kernel (1/5) (by norm_num) (by norm_num) p.1 p.2
  have hid (p : ℂ × ℂ) : ∑' k, f k p = (Real.sqrt (1-(1/5:ℝ)^2):ℂ)⁻¹ * Complex.exp
        ((2*p.1*p.2/5-(p.1^2+p.2^2)/25)/(1-(1/5:ℂ)^2)) := by
    convert (hsum p).tsum_eq using 1 <;> push_cast
    · rfl
    · congr 2
      ring
  change TendstoUniformlyOn (fun N p => ∑ k ∈ Finset.range N, f k p) _ _ _
  simp_rw [← hid]
  apply tendstoUniformlyOn_tsum_nat (u := fun n => M*(q*(5/4))^n)
    ((summable_geometric_of_lt_one (by dsimp [q]; positivity)
      (by dsimp [q]; linarith only [mehler_growth_ratio])).mul_left M)
  intro n p hp
  have hp' : ‖p‖ ≤ R := mem_closedBall_zero_iff.mp hp
  have h₁ := (norm_fst_le p).trans hp'
  have h₂ := (norm_snd_le p).trans hp'
  have hlin : 2*Real.sqrt n*(‖p.1‖+‖p.2‖) ≤ δ*(n:ℝ) + 4*R^2/δ := by
    have hb := mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by positivity : 0 ≤ 2*Real.sqrt n)
    apply hb.trans
    rw [add_comm (δ*(n:ℝ)), ← sub_le_iff_le_add, le_div_iff₀ hδ]
    have hs := Real.sq_sqrt (by positivity : 0 ≤ (n:ℝ))
    nlinarith only [sq_nonneg (δ*Real.sqrt n-2*R),
      congrArg (fun y : ℝ => δ^2*y) hs]
  apply (mehler_term_majorant n p.1 p.2).trans
  calc
    _ ≤ q^n * Real.exp (δ*(n:ℝ)+4*R^2/δ) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlin) (by dsimp [q]; positivity)
    _ = _ := by
      rw [Real.exp_add, mul_comm δ, Real.exp_nat_mul, show Real.exp δ = 5/4 from Real.exp_log (by norm_num),
        mul_pow]
      dsimp only [M]
      ring

end Turan
