module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TailLogCoeffs

@[expose] public section

noncomputable section
namespace Turan
open Complex Metric Filter
open scoped Topology

/-- The analytic part of Lemma 14. A local doubling estimate on the two
concentric disks gives the first four relative derivative estimates. -/
theorem tailLog_deriv_bound {F : ℂ → ℂ} {z w : ℂ} {Ω M : ℝ}
    (hF : Differentiable ℂ F) (hΩ : 0 < Ω) (hM : 0 < M)
    (hfree : ∀ t ∈ closedBall z (7/Ω), F t ≠ 0)
    (hbound : ∀ t ∈ closedBall z (7/Ω), ‖F t‖ ≤ M)
    (hw : ‖w-z‖ ≤ 2/Ω) (hdouble : M ≤ Real.exp (19628/1000) * ‖F w‖)
    (l : ℕ) (hl : 1 ≤ l) (hl' : l ≤ 4) :
    ‖iteratedDeriv l F z / F z‖ ≤ (11 * Ω)^l := by
  let R := 7/Ω
  have hR : 0 < R := div_pos (by norm_num) hΩ
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hfz := hfree z (mem_closedBall_self hR.le)
  let G := fun t : ℂ ↦ F (z + (R : ℂ)*t) / F z
  have hg : Differentiable ℂ G := by dsimp [G]; fun_prop
  have hg0 : G 0 = 1 := by simp [G, hfz]
  have hmap (t) (ht : t ∈ ball (0 : ℂ) 1) : z + (R : ℂ)*t ∈ closedBall z R := by
    rw [mem_closedBall_iff_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR]
    simpa using mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp ht).le hR.le
  have hgf (t) (ht : t ∈ ball (0 : ℂ) 1) : G t ≠ 0 := div_ne_zero (hfree _ (hmap t ht)) hfz
  obtain ⟨H, h0, hD, hE⟩ := tailLog_disk_branch hg hg0 hgf
  have hd : DifferentiableOn ℂ H (ball 0 1) := fun t ht ↦
    (hD t ht).differentiableAt.differentiableWithinAt
  let B := M / ‖F z‖
  have hB : 0 < B := div_pos hM (norm_pos_iff.mpr hfz)
  have hb (t) (ht : t ∈ ball (0 : ℂ) 1) : (H t).re ≤ Real.log B := by
    rw [← Real.exp_le_exp, Real.exp_log hB, ← Complex.norm_exp, hE t ht]
    simpa only [G, norm_div, B] using
      div_le_div_of_nonneg_right (hbound _ (hmap t ht)) (norm_nonneg (F z))
  let u := (w-z) / (R : ℂ)
  have hu : ‖u‖ ≤ 2/7 := by
    rw [show ‖u‖ = ‖w-z‖ / R by simp [u, Complex.norm_real, abs_of_pos hR]]
    rw [div_le_iff₀ hR]
    calc
      ‖w-z‖ ≤ 2/Ω := hw
      _ = 2/7 * R := by dsimp [R]; ring
  have hu' := mem_ball_zero_iff.mpr (show ‖u‖ < 1 by linarith)
  have heval : z + (R : ℂ)*u = w := by
    dsimp [u]
    field_simp [hRc]
    ring
  have hnear : Real.log B ≤ 19628/1000 + (H u).re := by
    rw [← Real.exp_le_exp, Real.exp_log hB, Real.exp_add, ← Complex.norm_exp, hE u hu']
    simp only [G, heval, norm_div, B, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hdouble (norm_nonneg _)
  have hL := tailLog_harnack h0 hd hb hu hnear
  have he : deriv G =ᶠ[𝓝 0] fun t ↦ G t * deriv H t := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with t ht
    rw [(hD t ht).deriv]
    field_simp [hgf t ht]
  have hunit := tailLog_unit_deriv hg hg0 hd h0
    (fun t ht ↦ (hb t ht).trans (by linarith)) he l hl hl'
  have hshift : ContDiff ℂ l (fun v : ℂ ↦ F (z+v)) := by
    have hF' : ContDiff ℂ l F := contDiff_iff_contDiffAt.mpr fun x ↦ (hF.analyticAt x).contDiffAt
    fun_prop
  have hscale : iteratedDeriv l G 0 = (R : ℂ)^l * (iteratedDeriv l F z / F z) := by
    simp only [G, iteratedDeriv_div_const, iteratedDeriv_comp_const_mul hshift,
      iteratedDeriv_comp_const_add, mul_zero, add_zero, mul_div_assoc]
  rw [hscale, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] at hunit
  apply le_of_mul_le_mul_left _ (pow_pos hR l)
  calc
    R^l * ‖iteratedDeriv l F z / F z‖ ≤ 77^l := hunit
    _ = R^l * (11 * Ω)^l := by
      rw [← mul_pow]
      congr 1
      dsimp [R]
      field_simp [hΩ.ne']
      ring

#print axioms tailLog_deriv_bound

end Turan
