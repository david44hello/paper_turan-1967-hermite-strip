module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TransferDefs
public import Turan.Circles
public import Turan.Hermite

@[expose] public section

noncomputable section
open Polynomial Metric
open scoped ComplexConjugate
namespace Turan

def chartPoly (P Q : Polynomial ℂ) (χ κ : ℂ) : Polynomial ℂ :=
  P + C χ*Q + C κ*(1+2*X)

theorem eval_le_mass (p : Polynomial ℂ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖p.eval z‖ ≤ coefficientMass p := by
  rw [eval_eq_sum]
  exact (norm_sum_le ..).trans (Finset.sum_le_sum fun k _ => by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg z) hz))

theorem affine_chart_cap (P Q : Polynomial ℂ) (χ κ : ℂ) (r : ℝ) (hr : 0 < r)
    (hrh : r < 87/100)
    (free : ∀ z : ℂ, |z.im| < 87/100 → (chartPoly P Q χ κ).eval z ≠ 0) :
    ‖κ‖ ≤ (coefficientMass (diskExpansion P (-1/2) r) +
      ‖χ‖*coefficientMass (diskExpansion Q (-1/2) r))/(2*r) := by
  by_contra! hlarge
  rw [div_lt_iff₀ (by positivity)] at hlarge
  let c : ℂ := -1/2
  let f := chartPoly P Q χ κ
  let g := C κ*(1+2*X : Polynomial ℂ)
  have dom (z : ℂ) (hz : z ∈ sphere c r) : ‖f.eval z - g.eval z‖ < ‖g.eval z‖ := by
    have hn : ‖z-c‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hz
    have bound (p : Polynomial ℂ) : ‖p.eval z‖ ≤ coefficientMass (diskExpansion p c r) := by
      let v := (z-c)/(r:ℂ)
      have hv : ‖v‖ ≤ 1 := by simp [v, norm_div, abs_of_pos hr, hn, hr.ne']
      have he : c+(r:ℂ)*v = z := by dsimp [v]; field_simp [Complex.ofReal_ne_zero.mpr hr.ne']; ring
      simpa [diskExpansion, eval_comp, eval_mul, he] using eval_le_mass (diskExpansion p c r) v hv
    have hp : ‖1+2*z‖ = 2*r := circle_at_neg_half r z (by rwa [show z+1/2=z-c by dsimp [c]; ring])
    simp only [f, g, chartPoly, eval_add, eval_mul, eval_C, eval_one, eval_ofNat, eval_X, add_sub_cancel_right,
      norm_mul, hp]
    exact (norm_add_le ..).trans_lt (lt_of_le_of_lt (by rw [norm_mul]; gcongr <;> exact bound _) hlarge)
  obtain ⟨z,hz,hfz⟩ := circle_comparison hr f.differentiable.differentiableOn g.differentiable.differentiableOn
    ⟨c, mem_ball_self hr, by norm_num [g, c, eval_add, eval_mul]⟩ dom
  exact free z (disk_in_strip c z r _ (by simpa [c] using hrh) (ball_subset_closedBall hz)) hfz

/-- Reduction to the two choices of the larger high-mode coefficient and the
upper half of the unit disk. Both real rescalings may depend on the degrees. -/
theorem high_chart_reduction (n m : ℕ) (P Q : Polynomial ℂ) (s t : ℝ)
    (hs : s ≠ 0) (ht : t ≠ 0) (hP : P = C (s:ℂ)*hermite n) (hQ : Q = C (t:ℂ)*hermite m)
    (solve : ∀ (U V : Polynomial ℂ), ((U=P ∧ V=Q) ∨ (U=Q ∧ V=P)) →
      ∀ χ κ : ℂ, ‖χ‖ ≤ 1 → 0 ≤ χ.im →
        ∃ z : ℂ, (chartPoly U V χ κ).eval z = 0 ∧ |z.im| < 87/100)
    (a b : ℂ) : ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| < 87/100 := by
  have realOn (p : Polynomial ℂ) (hp : p=P ∨ p=Q) (z : ℂ) :
      p.eval (conj z) = conj (p.eval z) := by
    rcases hp with rfl | rfl
    · simp [hP, eval_mul, (hermite_symmetry n z).1]
    · simp [hQ, eval_mul, (hermite_symmetry m z).1]
  have allCharts (U V : Polynomial ℂ) (hUV : (U=P ∧ V=Q) ∨ (U=Q ∧ V=P))
      (χ κ : ℂ) (hχ : ‖χ‖ ≤ 1) :
      ∃ z : ℂ, (chartPoly U V χ κ).eval z = 0 ∧ |z.im| < 87/100 := by
    by_cases hu : 0 ≤ χ.im
    · exact solve U V hUV χ κ hχ hu
    obtain ⟨z, hz, hzi⟩ := solve U V hUV (conj χ) (conj κ) (by simpa using hχ) (by simp; linarith)
    refine ⟨conj z, ?_, by simpa using hzi⟩
    have hU := realOn U (by tauto) z
    have hV := realOn V (by tauto) z
    simpa [chartPoly, eval_add, eval_mul, hU, hV, map_ofNat] using congrArg (starRingEnd ℂ) hz
  let A := a/(s:ℂ)
  let B := b/(t:ℂ)
  have repr (z : ℂ) : (family n m a b).eval z = 1+2*z+A*P.eval z+B*Q.eval z := by
    simp [family, hP, hQ, eval_add, eval_mul, A, B, hs, ht, div_eq_mul_inv, mul_assoc]
  have normalized (U V : Polynomial ℂ) (A B : ℂ) (hA : A ≠ 0) (hAB : ‖B‖ ≤ ‖A‖)
      (hUV : (U=P ∧ V=Q) ∨ (U=Q ∧ V=P)) :
      ∃ z : ℂ, 1+2*z+A*U.eval z+B*V.eval z=0 ∧ |z.im| < 87/100 := by
    obtain ⟨z,hz,hzi⟩ := allCharts U V hUV (B/A) A⁻¹ (by
      rw [norm_div, div_le_one (norm_pos_iff.mpr hA)]; exact hAB)
    refine ⟨z, ?_, hzi⟩
    simp only [chartPoly, eval_add, eval_mul, eval_C, eval_one, eval_ofNat, eval_X] at hz
    field_simp [hA] at hz
    linear_combination hz
  by_cases hAB : ‖B‖ ≤ ‖A‖
  · by_cases hA : A = 0
    · have hB : B = 0 := norm_le_zero_iff.mp (by simpa [hA] using hAB)
      exact ⟨-1/2, by rw [repr,hA,hB]; ring, by norm_num⟩
    obtain ⟨z,hz,hzi⟩ := normalized P Q A B hA hAB (.inl ⟨rfl,rfl⟩)
    exact ⟨z, by rwa [repr], hzi⟩
  · have hB := norm_pos_iff.mp ((norm_nonneg A).trans_lt (lt_of_not_ge hAB))
    obtain ⟨z,hz,hzi⟩ := normalized Q P B A hB (le_of_not_ge hAB) (.inr ⟨rfl,rfl⟩)
    exact ⟨z, by rw [repr]; linear_combination hz, hzi⟩

end Turan
