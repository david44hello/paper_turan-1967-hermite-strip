module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.LowerTailScalarDetails

@[expose] public section

namespace Turan.MehlerJets

/-- Take the nonnegative square root of the diagonal bound, then apply the real Gaussian weight. -/
theorem weight_of_squared_diagonal (n : ℕ) (X Y A : ℝ) (hA : 0 ≤ A)
    (hs : (1/5:ℝ)^n*A^2 ≤ (Real.sqrt (1-1/25:ℝ))⁻¹*Real.exp (X^2/3+Y^2/2)) :
    A*Real.exp (-X^2/2) ≤ (1-(1:ℝ)/25)^(-(1:ℝ)/4)*
      Real.exp (-X^2/3+Y^2/4+((n:ℝ)/2)*Real.log 5) := by
  let D : ℝ := 1 - 1/25
  let E := X^2/6 + Y^2/4 + ((n:ℝ)/2)*Real.log 5
  let B := D^(-(1:ℝ)/4) * Real.exp E
  have hD : 0 ≤ D := by norm_num [D]
  have hB : 0 ≤ B := mul_nonneg (Real.rpow_nonneg hD _) (Real.exp_nonneg _)
  have hquarter : (D^(-(1:ℝ)/4))^2 = (Real.sqrt D)⁻¹ := by
    rw [← Real.rpow_mul_natCast hD, Real.sqrt_eq_rpow, ← Real.rpow_neg hD]
    norm_num
  have hBsq : B^2 = ((Real.sqrt D)⁻¹ * Real.exp (X^2/3+Y^2/2)) * (5:ℝ)^n := by
    have hE : E + E = (X^2/3+Y^2/2) + (n:ℝ)*Real.log 5 := by dsimp [E]; ring
    rw [show B^2 = (D^(-(1:ℝ)/4))^2 * (Real.exp E)^2 by exact mul_pow ..,
      hquarter, sq (Real.exp E), ← Real.exp_add, hE, Real.exp_add, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0:ℝ) < 5), mul_assoc]
  have hAsq : A^2 ≤ B^2 := by
    rw [hBsq]
    apply (div_le_iff₀ (by positivity : 0 < (5:ℝ)^n)).mp
    simpa only [D, div_eq_inv_mul, mul_one, inv_pow] using hs
  have hab := Real.sqrt_le_sqrt hAsq
  rw [Real.sqrt_sq hA, Real.sqrt_sq hB] at hab
  calc
    _ ≤ B * Real.exp (-X^2/2) := mul_le_mul_of_nonneg_right hab (Real.exp_nonneg _)
    _ = _ := by
      dsimp only [B, D]
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [E]
      ring

theorem weighted_diagonal_estimate (n : ℕ) (z : ℂ) :
    ‖psi n z‖*Real.exp (-z.re^2/2) ≤ (1-(1:ℝ)/25)^(-(1:ℝ)/4)*
      Real.exp (-z.re^2/3+z.im^2/4+((n:ℝ)/2)*Real.log 5) :=
  weight_of_squared_diagonal n z.re z.im ‖psi n z‖ (norm_nonneg _)
    (LowerTailSteps.mehler_diagonal_term n z).2.2.2

end Turan.MehlerJets
