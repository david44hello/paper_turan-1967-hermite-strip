-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Entire
import Turan.TransferDisks
import Turan.GeneralNodes
noncomputable section
open Polynomial Set Metric
namespace Turan

theorem uniform_dominant_coefficient {α : Type*} (K : Set α)
    (f : α → ℂ → ℂ) (a : α → ℕ → ℂ) (k : ℕ) (hk : 1 ≤ k) (L : ℝ) (U : ℕ → ℝ)
    (hU : Summable U) (hgap : ∑' j, U j < L)
    (hf : ∀ t ∈ K, Differentiable ℂ (f t))
    (ha : ∀ t ∈ K, ∀ z : ℂ, HasSum (fun j => a t j*z^j) (f t z))
    (hl : ∀ t ∈ K, L ≤ ‖a t k‖)
    (hu : ∀ t ∈ K, ∀ j, (if j=k then 0 else ‖a t j‖) ≤ U j) :
    ∀ t ∈ K, ∃ roots : Multiset ℂ, roots.card = k ∧ ∀ z : ℂ,
      (roots.count z : ℕ∞) = if ‖z‖ < 1 then analyticOrderAt (f t) z else 0  := by
  intro t ht
  let b := fun j => if j=k then 0 else ‖a t j‖
  have hnon (j : ℕ) : 0 ≤ b j := by dsimp [b]; split <;> positivity
  have hsum : Summable b := .of_nonneg_of_le hnon (hu t ht) hU
  exact dominant_entire_term _ _ _ hk (hf t ht) (ha t ht) _ hsum.hasSum
    ((hsum.tsum_le_tsum (hu t ht) hU).trans_lt (hgap.trans_le (hl t ht)))

theorem transfer_outer_cap (S : Polynomial ℂ) (m : ℕ) (b : ℂ) (x r : ℝ) (hr : 0 < r)
    (hsgn : ((hermite m).eval ((x-r:ℝ):ℂ)).re * ((hermite m).eval ((x+r:ℝ):ℂ)).re < 0)
    (hfree : ∀ z ∈ ball (x:ℂ) r, S.eval z + b*(hermite m).eval z ≠ 0) :
    let L := min ‖(hermite m).eval ((x-r:ℝ):ℂ)‖ ‖(hermite m).eval ((x+r:ℝ):ℂ)‖
    let M := sSup ((fun z => ‖S.eval z‖) '' sphere (x:ℂ) r)
    0 < L ∧ ‖b‖ ≤ M/L  := by
  dsimp only
  let H := hermite m
  let L := min ‖H.eval ((x-r:ℝ):ℂ)‖ ‖H.eval ((x+r:ℝ):ℂ)‖
  let M := sSup ((fun z => ‖S.eval z‖) '' sphere (x:ℂ) r)
  have hL : 0 < L := by
    apply lt_min <;> apply norm_pos_iff.mpr <;> intro he <;> change (hermite m).eval _ = 0 at he <;>
      rw [he] at hsgn <;> simp at hsgn
  refine ⟨hL, (le_div_iff₀ hL).mpr ?_⟩
  by_contra! h
  obtain ⟨y, hy, he⟩ := hermite_zero_of_sign_change m _ _ (by linarith) hsgn
  have hyball : (y:ℂ) ∈ ball (x:ℂ) r := by
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hy.1,hy.2]
  obtain ⟨z,hz,heval⟩ := circle_comparison (P := fun z => b*H.eval z)
    (F := fun z => S.eval z+b*H.eval z) hr
    (S.differentiable.add (H.differentiable.const_mul b)).differentiableOn
    (H.differentiable.const_mul b).differentiableOn
    ⟨(y:ℂ),hyball,by change b*(hermite m).eval _ = 0; rw [he,mul_zero]⟩ (by
      intro z hz
      have hM : ‖S.eval z‖ ≤ M := le_csSup
        ((isCompact_sphere ..).bddAbove_image S.continuous.norm.continuousOn) ⟨z,hz,rfl⟩
      have hmin := real_rooted_circle H (fun t ht => (hermite_real_simple m t ht).1) x r hr z
        (by simpa [dist_eq_norm] using mem_sphere.mp hz)
      simp only [add_sub_cancel_right,norm_mul]
      exact hM.trans_lt (h.trans_le (mul_le_mul_of_nonneg_left hmin (norm_nonneg b))))
  exact hfree z hz heval

theorem node_pair_continuous_increment (n m : ℕ) (a b : ℂ) (x y : ℝ) (hx : x≠0) (hy : y≠0)
    (hxy : x<y) (hn : divided (nodeMode n) x y=0) (hm : divided (nodeMode m) x y=0)
    (hfree : ∀ t : ℝ, (family n m a b).eval (t:ℂ) ≠ 0) :
    let F := family n m a b
    ∃ A : ℝ → ℝ, Continuous A ∧
      (∀ t : ℝ, Complex.exp ((A t:ℂ)*Complex.I) = F.eval (t:ℂ)/(‖F.eval (t:ℂ)‖:ℂ)) ∧
      ∃ k : ℤ, A (y-1/2)-A (x-1/2) = (F.roots.map (intervalAngle (x-1/2) (y-1/2))).sum ∧
        A (y-1/2)-A (x-1/2) = (2*(k:ℝ)+(if x*y<0 then 1 else 0))*Real.pi  := by
  dsimp only
  obtain ⟨A,hA,hphase,hinc⟩ := polynomial_argument_on_real_axis _ hfree
  obtain ⟨k,hk⟩ := equal_nodes_angle_parity n m a b x y hx hy hxy hn hm hfree
  have he := hinc (x-1/2) (y-1/2) (by linarith)
  exact ⟨A,hA,hphase,k,he,he.trans hk⟩

end Turan
