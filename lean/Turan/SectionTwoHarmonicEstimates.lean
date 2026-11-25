-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.SectionTwoGradients
import Turan.CompactnessTools
import Mathlib.Analysis.Complex.BorelCaratheodory

noncomputable section
open Polynomial Filter Metric InnerProductSpace
open scoped Topology
namespace Turan.SectionTwo

theorem gradient_congr {u v : ℂ → ℝ} {z : ℂ} (h : u =ᶠ[𝓝 z] v) :
    complexGradient u z = complexGradient v z := by simp only [complexGradient, h.fderiv_eq]

theorem gradient_sub {u v : ℂ → ℝ} {z : ℂ} (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    complexGradient (u - v) z = complexGradient u z - complexGradient v z := by
  simp only [complexGradient, fderiv_sub hu hv, ContinuousLinearMap.sub_apply, Complex.ofReal_sub]
  ring

/-- A harmonic function bounded by M on the unit disk has gradient at most 8M at its center. -/
theorem harmonic_gradient_bound {u : ℂ → ℝ} (z : ℂ) (M : ℝ) (hM : 0 < M)
    (hu : HarmonicOnNhd u (ball z 1)) (hb : ∀ w ∈ ball z 1, |u w| ≤ M) :
    ‖complexGradient u z‖ ≤ 8*M := by
  obtain ⟨g,hg,hre⟩ := hu.exists_analyticOnNhd_ball_re_eq
  have hz := mem_ball_self (x := z) zero_lt_one
  have heq : (fun w => (g w).re) =ᶠ[𝓝 z] u := Filter.eventually_of_mem (ball_mem_nhds z zero_lt_one) hre
  let G (w : ℂ) := g (w+z) - g z
  have hG (w : ℂ) (hw : w ∈ ball 0 1) :
      HasDerivAt G (deriv g (w+z)) w := by
    have hmem : w+z ∈ ball z 1 := by simpa [mem_ball, dist_eq_norm] using hw
    simpa [G, Function.comp_def, Pi.sub_def, Pi.add_def, id_def] using
      (((hg _ hmem).differentiableAt.hasDerivAt.comp w ((hasDerivAt_id w).add_const z)).sub_const (g z))
  have hGd : DifferentiableOn ℂ G (ball 0 1) := fun w hw => (hG w hw).differentiableAt.differentiableWithinAt
  have hupper : Set.MapsTo G (ball 0 1) {w | w.re ≤ 2*M} := by
    intro w hw
    have hmem : w+z ∈ ball z 1 := by simpa [mem_ball, dist_eq_norm] using hw
    change (g (w+z) - g z).re ≤ _
    rw [Complex.sub_re, show (g (w+z)).re = u (w+z) from hre hmem, show (g z).re = u z from hre hz]
    linarith [(abs_le.mp (hb _ hmem)).2, (abs_le.mp (hb _ hz)).1]
  have hc : DiffContOnCl ℂ G (ball 0 (1/2)) := by
    apply DifferentiableOn.diffContOnCl
    apply hGd.mono
    rw [closure_ball _ (by norm_num : (1/2 : ℝ) ≠ 0)]
    exact closedBall_subset_ball (by norm_num)
  have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := (0 : ℂ))
    (by norm_num : 0 < (1/2 : ℝ)) hc (C := 4*M) (fun w hw => by
      have hw' := mem_sphere_zero_iff_norm.mp hw
      have hh := Complex.borelCaratheodory_zero (by positivity : 0 < 2*M) hGd hupper zero_lt_one
        (mem_ball_zero_iff.mpr (hw'.trans_lt (by norm_num))) (show G 0 = 0 by simp [G])
      rw [hw'] at hh
      exact hh.trans_eq (by ring))
  rw [← gradient_congr heq, gradient_of_re (hg z hz).differentiableAt.hasDerivAt]
  rw [(hG 0 (mem_ball_self zero_lt_one)).deriv, zero_add] at hC
  linarith only [hC]

/-- Quantitative Harnack bounds on the central half of a closed disk. -/
private theorem half_harnack (H : ℂ → ℝ) (S : ℝ) (hS : 0 < S)
    (hh : HarmonicContOnCl H (ball 0 S)) (hn : ∀ w ∈ sphere 0 S, 0 ≤ H w)
    (h0 : 0 ≤ H 0) (w : ℂ) (hw : ‖w‖ ≤ S/2) :
    H 0/3 ≤ H w ∧ H w ≤ 3*H 0 := by
  have hlt : ‖w‖ < S := by linarith
  have ⟨lo,hi⟩ := harnack_disk H 0 w S hh hn (mem_ball_zero_iff.mpr hlt)
  rw [sub_zero] at lo hi
  have hl : 1/3 ≤ (S-‖w‖)/(S+‖w‖) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hh' : (S+‖w‖)/(S-‖w‖) ≤ 3 := (div_le_iff₀ (sub_pos.mpr hlt)).mpr (by linarith)
  constructor
  · exact (show H 0/3 = (1/3)*(H 0) by ring).le.trans ((mul_le_mul_of_nonneg_right hl h0).trans lo)
  · exact hi.trans (mul_le_mul_of_nonneg_right hh' h0)

theorem harmonic_anchor_bounds (u : ℕ → ℂ → ℝ)
    (hup : ∀ R : ℝ, 0 < R → ∃ A : ℝ, ∀ᶠ j in atTop,
      HarmonicOnNhd (u j) (ball 0 R) ∧ ∀ z ∈ ball 0 R, u j z ≤ A)
    (hanchor : ∃ b : ℝ, ∀ᶠ j in atTop, ∃ z ∈ closedBall (0 : ℂ) 1, b ≤ u j z)
    (R : ℝ) (hR : 0 ≤ R) : ∃ B : ℝ, 0 < B ∧ ∀ᶠ j in atTop,
      HarmonicOnNhd (u j) (closedBall 0 R) ∧ ∀ z ∈ closedBall 0 R, |u j z| ≤ B := by
  obtain ⟨b,hb⟩ := hanchor
  let S := 2*(R+1)
  have hS : 0 < S := by dsimp [S]; positivity
  obtain ⟨A,hA⟩ := hup (S+1) (by positivity)
  refine ⟨10*(|A|+|b|+1), by positivity, ?_⟩
  filter_upwards [hA,hb] with j hj hanc
  obtain ⟨w, hw, hval⟩ := hanc
  let H := (fun _ : ℂ => A+1) - u j
  have hsub : closedBall (0 : ℂ) S ⊆ ball 0 (S+1) := closedBall_subset_ball (by linarith)
  have hh : HarmonicContOnCl H (ball 0 S) := by
    apply HarmonicOnNhd.harmonicContOnCl
    rw [closure_ball _ hS.ne']
    exact (harmonicOnNhd_const _).sub (hj.1.mono hsub)
  have hn (y : ℂ) (hy : y ∈ closedBall 0 S) : 0 ≤ H y := by
    change 0 ≤ A+1-u j y
    linarith [hj.2 y (hsub hy)]
  have hhalf := half_harnack H S hS hh (fun y hy => hn y (sphere_subset_closedBall hy))
    (hn 0 (mem_closedBall_self hS.le))
  have hw' : ‖w‖ ≤ 1 := by simpa using mem_closedBall.mp hw
  have hlo := (hhalf w (by dsimp [S]; linarith)).1
  have hinc : closedBall (0 : ℂ) R ⊆ ball 0 (S+1) := closedBall_subset_ball (by dsimp [S]; linarith)
  refine ⟨hj.1.mono hinc, ?_⟩
  intro x hx
  have hx' : ‖x‖ ≤ R := by simpa using mem_closedBall.mp hx
  have hhi := (hhalf x (by dsimp [S]; linarith)).2
  change (A+1-u j 0)/3 ≤ A+1-u j w at hlo
  change A+1-u j x ≤ 3*(A+1-u j 0) at hhi
  rw [abs_le]
  constructor <;> linarith [hj.2 x (hinc hx), le_abs_self A, neg_le_abs A, neg_le_abs b, abs_nonneg A, abs_nonneg b]

end Turan.SectionTwo
