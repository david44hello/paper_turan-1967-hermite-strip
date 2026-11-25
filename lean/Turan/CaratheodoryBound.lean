-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Tactic

noncomputable section
open Complex Real Metric Set
open scoped ComplexConjugate Topology
namespace Turan

/-- On a circle the conjugate of the positive-frequency mode has zero average.
This lets the real part of g replace one half of g in its coefficient integral. -/
private theorem conjugate_mode_zero (g : ℂ → ℂ) (z : ℂ) (r R : ℝ) (hr : 0<r)
    (hrR : r<R) (hg : DifferentiableOn ℂ g (ball z R)) (l : ℕ) (hl : 1 ≤ l) :
    circleAverage (fun w => conj (g w)/(w-z)^l) z r = 0 := by
  let F := fun w : ℂ => g w*(w-z)^l
  have hF : DifferentiableOn ℂ F (ball z R) := hg.mul ((differentiableOn_id.sub_const z).pow l)
  have hclosed := hF.diffContOnCl_ball (closedBall_subset_ball (x:=z) hrR)
  have hmean : circleAverage F z r = 0 := by
    rw [DiffContOnCl.circleAverage (by simpa [abs_of_pos hr] using hclosed)]
    simp [F,zero_pow (by omega : l≠0)]
  have hI : CircleIntegrable F z r :=
    (hF.continuousOn.mono ((sphere_subset_closedBall).trans (closedBall_subset_ball hrR))).circleIntegrable hr.le
  let k : ℂ := (((r:ℂ)^2)^l)⁻¹
  have heq : circleAverage (fun w => conj (g w)/(w-z)^l) z r =
      circleAverage (fun w => k • (conjCLE ∘ F) w) z r := by
    apply circleAverage_congr_sphere
    intro w hw
    have hn : ‖w-z‖=r := by simpa [abs_of_pos hr,mem_sphere,dist_eq_norm] using hw
    have hh : (w-z)*conj (w-z)=(r:ℂ)^2 := by rw [Complex.mul_conj',hn]
    have hwz : w-z≠0 := norm_pos_iff.mp (hn.symm ▸ hr)
    have hc : (r:ℂ)≠0 := by exact_mod_cast hr.ne'
    dsimp [F,k]
    change conj (g w)/(w-z)^l = (((r:ℂ)^2)^l)⁻¹ * conj (g w*(w-z)^l)
    rw [map_mul,map_pow,eq_comm,inv_mul_eq_div]
    apply (div_eq_div_iff (pow_ne_zero _ (pow_ne_zero _ hc)) (pow_ne_zero _ hwz)).2
    rw [← hh,mul_pow]
    ring
  rw [heq,circleAverage_fun_smul]
  change k • circleAverage (conjCLE.toContinuousLinearMap ∘ F) z r = 0
  rw [conjCLE.toContinuousLinearMap.circleAverage_comp_comm hI,hmean]; simp

theorem caratheodory_average_bound (g : ℂ → ℂ) (z : ℂ) (r R : ℝ) (hr : 0<r) (hrR : r<R)
    (hg : DifferentiableOn ℂ g (ball z R)) (hpos : ∀ w ∈ ball z R, 0 ≤ (g w).re)
    (l : ℕ) (hl : 1 ≤ l) :
    ‖circleAverage (fun w => g w/(w-z)^l) z r‖ ≤ 2*(g z).re/r^l := by
  let K := fun w : ℂ => (w-z)^l
  have hgc : ContinuousOn g (sphere z r) :=
    hg.continuousOn.mono (sphere_subset_closedBall.trans (closedBall_subset_ball hrR))
  have hK (w : ℂ) (hw : w ∈ sphere z r) : K w ≠ 0 := by
    apply pow_ne_zero
    apply sub_ne_zero.mpr
    rintro rfl
    exact hr.ne (by simpa [mem_sphere] using hw)
  have hKI : ContinuousOn K (sphere z r) := by dsimp [K]; fun_prop
  have hI : CircleIntegrable (fun w => g w / K w) z r := (hgc.div hKI hK).circleIntegrable hr.le
  have hcI : CircleIntegrable (fun w => conj (g w) / K w) z r := ((Complex.continuous_conj.comp_continuousOn hgc).div hKI hK).circleIntegrable hr.le
  have hsum : circleAverage (fun w => g w/K w) z r =
      circleAverage (fun w => ((2*(g w).re:ℝ):ℂ)/K w) z r := by
    calc
      _ = circleAverage (fun w => g w/K w) z r + circleAverage (fun w => conj (g w)/K w) z r := by
        rw [conjugate_mode_zero g z r R hr hrR hg l hl, add_zero]
      _ = _ := by
        rw [← circleAverage_fun_add hI hcI]
        apply circleAverage_congr_sphere
        intro w _
        change g w / K w + conj (g w) / K w = _
        rw [← add_div, Complex.add_conj]
  have hmean := (hg.diffContOnCl_ball (closedBall_subset_ball (x:=z) hrR))
  have hmean' : circleAverage g z r = g z :=
    DiffContOnCl.circleAverage (by simpa [abs_of_pos hr] using hmean)
  have hrmean : circleAverage (fun w => (g w).re) z r = (g z).re := by
    rw [← hmean']
    exact Complex.reCLM.circleAverage_comp_comm (hgc.circleIntegrable hr.le)
  change ‖circleAverage (fun w => g w/K w) z r‖ ≤ _
  rw [hsum]
  refine Real.norm_circleAverage_le_circleAverage_norm.trans (le_of_eq ?_)
  calc
    _ = circleAverage (fun w => (2/r^l) • (g w).re) z r := by
      apply circleAverage_congr_sphere
      intro w hw
      have hn : ‖w-z‖=r := by simpa [abs_of_pos hr,mem_sphere,dist_eq_norm] using hw
      have hwR : w ∈ ball z R := mem_ball.mpr (by rw [dist_eq_norm,hn]; exact hrR)
      change ‖((2*(g w).re:ℝ):ℂ)/K w‖ = (2/r^l) • (g w).re
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by norm_num) (hpos w hwR))]
      dsimp [K]
      rw [norm_pow, hn]
      ring
    _ = 2*(g z).re/r^l := by rw [circleAverage_fun_smul,hrmean,smul_eq_mul]; ring

end Turan
