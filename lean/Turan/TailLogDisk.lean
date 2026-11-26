module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic

@[expose] public section

noncomputable section
namespace Turan
open Complex Metric Set
open scoped Topology

/-- The primitive of the logarithmic derivative, normalized at the center. -/
theorem tailLog_disk_branch {G : ℂ → ℂ} (hG : Differentiable ℂ G) (h0 : G 0 = 1)
    (hn : ∀ t ∈ ball (0 : ℂ) 1, G t ≠ 0) :
    ∃ H : ℂ → ℂ, H 0 = 0 ∧
      (∀ t ∈ ball (0 : ℂ) 1, HasDerivAt H (deriv G t / G t) t) ∧
      (∀ t ∈ ball (0 : ℂ) 1, exp (H t) = G t) := by
  have hq := hG.deriv.differentiableOn.div hG.differentiableOn hn
  obtain ⟨H, hH0, hH⟩ := hq.isExactOn_ball.with_val_at 0 0
  refine ⟨H, hH0, hH, ?_⟩
  let K := fun t ↦ exp (H t) / G t
  have hK (t) (ht : t ∈ ball (0 : ℂ) 1) : HasDerivAt K 0 t := by
    convert ((hH t ht).cexp.div (hG t).hasDerivAt (hn t ht)) using 1
    dsimp
    field_simp [hn t ht]
    ring
  intro t ht
  have he := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
    (fun t ht ↦ (hK t ht).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ (hK t ht).deriv) ht (mem_ball_self (by norm_num : (0 : ℝ) < 1))
  simpa [K, hH0, h0, div_eq_iff (hn t ht)] using he

/-- The Möbius transform of a centered holomorphic function with bounded real part. -/
theorem tailLog_schwarz {H : ℂ → ℂ} {L : ℝ} (hL : 0 < L) (h0 : H 0 = 0)
    (hd : DifferentiableOn ℂ H (ball 0 1))
    (hb : ∀ t ∈ ball (0 : ℂ) 1, (H t).re ≤ L) :
    ∃ S : ℂ → ℂ, S 0 = 0 ∧ DifferentiableOn ℂ S (ball 0 1) ∧
      (∀ t ∈ ball (0 : ℂ) 1, ‖S t‖ ≤ ‖t‖) ∧
      (∀ t ∈ ball (0 : ℂ) 1, H t = (2 * (L : ℂ)) * S t - H t * S t) ∧
      (∀ t ∈ ball (0 : ℂ) 1, S t = H t / (2 * (L : ℂ) - H t)) := by
  let S := fun t ↦ H t / (2 * (L : ℂ) - H t)
  have hden (t) (ht : t ∈ ball (0 : ℂ) 1) : 2 * (L : ℂ) - H t ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    simp at h
    linarith [hb t ht]
  have hS : DifferentiableOn ℂ S (ball 0 1) := hd.div (hd.const_sub _) hden
  have hS0 : S 0 = 0 := by simp [S, h0]
  have hmap : MapsTo S (ball 0 1) (closedBall (S 0) 1) := by
    intro t ht
    rw [hS0, mem_closedBall_zero_iff]
    dsimp [S]
    rw [norm_div, div_le_one₀ (norm_pos_iff.mpr (hden t ht)),
      ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    simp [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [mul_nonneg hL.le (sub_nonneg.mpr (hb t ht))]
  refine ⟨S, hS0, hS, fun t ht ↦ ?_, fun t ht ↦ ?_, fun _ _ ↦ rfl⟩
  · simpa [hS0] using Complex.dist_le_div_mul_dist_of_mapsTo_ball hS hmap ht
  · dsimp [S]
    field_simp [hden t ht]

/-- The Harnack factor at radius 2/7 on the unit disk. -/
theorem tailLog_harnack {H : ℂ → ℂ} {L : ℝ} {u : ℂ} (h0 : H 0 = 0)
    (hd : DifferentiableOn ℂ H (ball 0 1))
    (hb : ∀ t ∈ ball (0 : ℂ) 1, (H t).re ≤ L)
    (hu : ‖u‖ ≤ 2/7) (hnear : L ≤ 19628/1000 + (H u).re) :
    L ≤ (9/5) * (19628/1000) := by
  by_cases hL : 0 < L
  · have hu' : u ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (by linarith)
    obtain ⟨S, _, _, hS, _, hq⟩ := tailLog_schwarz hL h0 hd hb
    have h := (hS u hu').trans hu
    have hd0 : 2 * (L : ℂ) - H u ≠ 0 := by
      intro he
      have he' := congrArg Complex.re he
      simp at he'
      linarith [hb u hu']
    rw [hq u hu', norm_div, div_le_iff₀ (norm_pos_iff.mpr hd0)] at h
    have hsq := sq_le_sq₀ (norm_nonneg (H u)) (by positivity) |>.2 h
    rw [mul_pow, Complex.sq_norm, Complex.sq_norm] at hsq
    simp [Complex.normSq_apply] at hsq
    have hr : 9 * (H u).re ≤ 4*L := by
      by_contra! hlt
      nlinarith [mul_pos (sub_pos.mpr hlt) (show 0 < 5*(H u).re + 4*L by linarith),
        sq_nonneg (H u).im]
    linarith
  · linarith

end Turan
