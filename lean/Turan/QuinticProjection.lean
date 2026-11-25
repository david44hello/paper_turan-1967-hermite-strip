-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

import Mathlib.Tactic

noncomputable section
open scoped RealInnerProductSpace
namespace Turan

/-- Project the fifth coordinate vector off the constant vector and
the imaginary-part vector. The sum Σ* runs over just the four upper entries. -/
theorem quintic_fifth_orthogonal_projection (z : Fin 5 → ℂ)
    (hz : ∑ i, z i = 0) (hz2 : ∑ i, (z i) ^ 2 = 10)
    (hupper : ∀ i : Fin 4, 0 < (z i.castSucc).im) :
    let x : EuclideanSpace ℝ (Fin 5) := WithLp.toLp 2 (fun i => (z i).re)
    let y : EuclideanSpace ℝ (Fin 5) := WithLp.toLp 2 (fun i => (z i).im)
    let ones : EuclideanSpace ℝ (Fin 5) := WithLp.toLp 2 (fun _ => (1 : ℝ))
    let e₅ := EuclideanSpace.single (4 : Fin 5) (1 : ℝ)
    let p := (Submodule.span ℝ {ones, y})ᗮ.starProjection e₅
    let σ := ∑ i : Fin 4, (z i.castSucc).im ^ 2
    let t := (z 4).im
    0 < ‖y‖ ^ 2 ∧ (z 4).re = ⟪x, p⟫ ∧ ‖p‖ ^ 2 = 4 / 5 - t ^ 2 / ‖y‖ ^ 2 ∧
      (z 4).re ^ 2 ≤ ‖x‖ ^ 2 * ‖p‖ ^ 2 ∧
      ‖x‖ ^ 2 * ‖p‖ ^ 2 = 10 * (4 / 5 - t ^ 2 / ‖y‖ ^ 2) + (4 * σ - t ^ 2) / 5 ∧
      10 * (4 / 5 - t ^ 2 / ‖y‖ ^ 2) + (4 * σ - t ^ 2) / 5 ≤ 3 + (3 / 5) * σ := by
  intro x y ones e p σ t
  let K := Submodule.span ℝ {ones,y}
  let N := ‖y‖^2
  have hy0 : y ≠ 0 := by
    intro h
    have he := congrArg (fun u : EuclideanSpace ℝ (Fin 5) => u (0:Fin 5)) h
    have hn := hupper (0:Fin 4)
    change (z 0).im = 0 at he
    exact hn.ne' he
  have hN : 0 < N := sq_pos_of_pos (norm_pos_iff.mpr hy0)
  have hNx : ‖x‖^2 = 10+N := by
    have h := congrArg Complex.re hz2
    simp only [Complex.re_sum,pow_two,Complex.mul_re,show (10:ℂ).re=10 from rfl,
      Finset.sum_sub_distrib] at h
    rw [EuclideanSpace.real_norm_sq_eq]
    dsimp [N]
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [x,y,pow_two,WithLp.ofLp_toLp] using sub_eq_iff_eq_add.mp h
  have hNσ : N = σ+t^2 := by
    change ‖y‖^2 = _
    rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_castSucc]
    rfl
  have hx1 : ⟪x,ones⟫=0 := by simpa [x,ones,PiLp.inner_apply] using congrArg Complex.re hz
  have hy1 : ⟪y,ones⟫=0 := by simpa [y,ones,PiLp.inner_apply] using congrArg Complex.im hz
  have h1y : ⟪ones,y⟫=0 := by rw [real_inner_comm,hy1]
  have hxy : ⟪x,y⟫=0 := by
    have hh := congrArg Complex.im hz2
    simp only [Complex.im_sum,pow_two,Complex.mul_im,show (10:ℂ).im=0 from rfl] at hh
    simp_rw [mul_comm (z _).im (z _).re, ← two_mul] at hh
    rw [← Finset.mul_sum] at hh
    simpa [x,y,PiLp.inner_apply,mul_comm] using (mul_eq_zero.mp hh).resolve_left (by norm_num)
  have h11 : ⟪ones,ones⟫=5 := by
    rw [real_inner_self_eq_norm_sq,EuclideanSpace.real_norm_sq_eq]
    simp [ones]
  have he₁ : ⟪ones,e⟫=1 := by simp [e,ones,EuclideanSpace.inner_single_right]
  have hey : ⟪y,e⟫=t := by simp [e,y,t,EuclideanSpace.inner_single_right]
  have hex : ⟪x,e⟫=(z 4).re := by simp [e,x,EuclideanSpace.inner_single_right]
  let q := e - (1/5:ℝ) • ones - (t/N) • y
  have h₁ : ⟪ones,q⟫=0 := by
    simp only [q,inner_sub_right,real_inner_smul_right,h11,he₁,h1y]
    ring
  have h₂ : ⟪y,q⟫=0 := by
    simp only [q,inner_sub_right,real_inner_smul_right,hy1,mul_zero,sub_zero,hey,real_inner_self_eq_norm_sq]
    change t - t/N*N = 0
    rw [div_mul_cancel₀ _ hN.ne',sub_self]
  have hq : q ∈ Kᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro u hu
    induction hu using Submodule.span_induction with
    | mem a ha =>
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact h₁
      · exact h₂
    | zero => simp
    | add a b ha hb ia ib => rw [inner_add_left,ia,ib,add_zero]
    | smul r a ha ih => rw [real_inner_smul_left,ih,mul_zero]
  have hres : e-q ∈ K := by
    rw [show e-q = (1/5:ℝ) • ones + (t/N) • y by dsimp [q]; abel]
    exact K.add_mem (K.smul_mem _ (Submodule.subset_span (by simp)))
      (K.smul_mem _ (Submodule.subset_span (by simp)))
  have hp : p=q := Submodule.eq_starProjection_of_mem_orthogonal hq
    (K.le_orthogonal_orthogonal hres)
  have hcoord : (z 4).re = ⟪x,p⟫ := by simp [hp,q,inner_sub_right,real_inner_smul_right,hex,hx1,hxy]
  have hpN : ‖p‖^2 = 4/5-t^2/N := by
    rw [hp, ← real_inner_self_eq_norm_sq]
    calc
      ⟪q,q⟫ = ⟪q,e⟫ := by
        have h := Submodule.inner_left_of_mem_orthogonal hres hq
        rw [inner_sub_right,sub_eq_zero] at h
        exact h.symm
      _ = _ := by
        simp [q,inner_sub_left,EuclideanSpace.inner_single_right,e,ones,y,t]
        ring
  have hσ : σ ≤ t^2 := by
    have hi := congrArg Complex.im hz
    simp [Fin.sum_univ_succ,Complex.add_im] at hi
    have H (i : Fin 4) := (hupper i).le
    have H₀ : 0 ≤ (z 0).im := H 0
    have H₁ : 0 ≤ (z 1).im := H 1
    have H₂ : 0 ≤ (z 2).im := H 2
    have H₃ : 0 ≤ (z 3).im := H 3
    have ht : (z 4).im = -((z 0).im+(z 1).im+(z 2).im+(z 3).im) := by linarith only [hi]
    simp [σ,t,Fin.sum_univ_succ,ht]
    nlinarith only [mul_nonneg H₀ H₁,mul_nonneg H₀ H₂,mul_nonneg H₀ H₃,
      mul_nonneg H₁ H₂,mul_nonneg H₁ H₃,mul_nonneg H₂ H₃]
  refine ⟨hN,hcoord,hpN,?_,?_,?_⟩
  · rw [hcoord,← mul_pow]
    nlinarith only [(sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg x) (norm_nonneg p))).2
      (abs_real_inner_le_norm x p),sq_abs ⟪x,p⟫]
  · rw [hNx,hpN]
    change (10+N)*(4/5-t^2/N) = 10*(4/5-t^2/N)+(4*σ-t^2)/5
    field_simp [hN.ne']
    rw [hNσ]
    ring
  · have hfrac : 1/2 ≤ t^2/N := (le_div_iff₀ hN).mpr (by linarith only [hNσ,hσ])
    change 10*(4/5-t^2/N)+(4*σ-t^2)/5 ≤ _
    linarith only [hfrac,hσ]


#print axioms quintic_fifth_orthogonal_projection

end Turan
