module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.RouteDefs
public import Turan.Circles
public import Turan.Rouche

@[expose] public section

noncomputable section
open Polynomial Metric
namespace Turan

theorem transfer_arbitrary_perturbation (check : UniformTransferCheck) (n : ℕ)
    (hn : 2 ≤ n) (hn' : n ≤ 7) (swap : Bool) (θ : ℂ) (hχ : |θ.re| ≤ 1)
    (him : 0 ≤ θ.im) (him' : θ.im ≤ 1) :
    ∃ (w : ℂ) (r : ℝ), 0 < r ∧ ‖w‖+r ≤ 5/4 ∧ |w.im|+r < 87/100 ∧
      ∀ g : Polynomial ℂ, (∀ z : ℂ, ‖z‖ ≤ 5/4 → ‖g.eval z‖ < 1/64) →
        ∃ z ∈ ball w r, (transferPencil n swap θ+g).eval z = 0 := by
  classical
  obtain ⟨w,r,k,hr,hk,hin,hstrip,hmargin⟩ := check n hn hn' swap θ hχ him him'
  refine ⟨w,r,hr,hin,hstrip,?_⟩
  intro g hg
  let S := transferPencil n swap θ
  let p := diskExpansion S w r
  let G := diskExpansion g w r
  let top := monomial k (p.coeff k)
  have hp : p.coeff k ≠ 0 := by
    intro h
    change 1/64 < ‖p.coeff k‖ - _ at hmargin
    rw [h,norm_zero] at hmargin
    linarith [Finset.sum_nonneg (s := p.support.erase k) (fun j _ => norm_nonneg (p.coeff j))]
  have dom (z : ℂ) (hz : z ∈ sphere (0 : ℂ) 1) : ‖(p+G).eval z-top.eval z‖ < ‖top.eval z‖ := by
    have hnz : ‖z‖=1 := by simpa using mem_sphere.mp hz
    have ht : p.eval z-top.eval z = ∑ j ∈ p.support.erase k, p.coeff j*z^j := by
      apply sub_eq_iff_eq_add.mpr
      rw [eval_eq_sum, Polynomial.sum, eval_monomial]
      exact (Finset.sum_erase_add _ _ (mem_support_iff.mpr hp)).symm
    have hs : ‖p.eval z-top.eval z‖ ≤ ∑ j ∈ p.support.erase k, ‖p.coeff j‖ := by
      rw [ht]
      simpa [norm_mul, norm_pow, hnz] using
        norm_sum_le (p.support.erase k) (fun j => p.coeff j*z^j)
    have hwz : ‖w+(r:ℂ)*z‖ ≤ 5/4 := (norm_add_le ..).trans (by
      simpa [norm_mul, abs_of_pos hr, hnz] using hin)
    have hG : ‖G.eval z‖ < 1/64 := by
      simpa [G,diskExpansion,eval_comp,eval_mul] using hg _ hwz
    rw [eval_add, add_sub_right_comm, eval_monomial, norm_mul, norm_pow, hnz, one_pow, mul_one]
    refine (norm_add_le ..).trans_lt ?_
    change 1/64 < ‖p.coeff k‖ - ∑ j ∈ p.support.erase k, ‖p.coeff j‖ at hmargin
    simp only [top, eval_monomial] at hs
    linarith only [hs,hG,hmargin]
  have zero : top.eval 0=0 := by simp [top,eval_monomial,Nat.ne_of_gt hk]
  obtain ⟨z,hz,h₀⟩ := circle_comparison zero_lt_one (p+G).differentiable.differentiableOn
    top.differentiable.differentiableOn ⟨0,mem_ball_self zero_lt_one,zero⟩ dom
  have hz' : ‖z‖<1 := by simpa using mem_ball.mp hz
  refine ⟨w+(r:ℂ)*z, ?_, ?_⟩
  · rw [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_mul,Complex.norm_of_nonneg hr.le]
    simpa using mul_lt_mul_of_pos_left hz' hr
  · simpa [S,p,G,diskExpansion,eval_add,eval_comp,eval_mul] using h₀

end Turan
