-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.QuarticPositionAlgebra

noncomputable section
open scoped ComplexConjugate
namespace Turan

private theorem candidate_roots {u b z : ℂ} (hb : b ≠ 0)
    (h : 16*b*(z-u)^3*(z+3*u) = 0) : z = u ∨ z = -(3*u) := by
  by_cases he : z = u
  · exact Or.inl he
  · have hn := mul_ne_zero (mul_ne_zero (by norm_num : (16 : ℂ) ≠ 0) hb)
      (pow_ne_zero 3 (sub_ne_zero.mpr he))
    exact Or.inr (eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp h).resolve_left hn))

open QuarticPosition in
theorem quartic_candidate (w : ℂ) (hw : 0 < w.im ∧ 12*w^4+16*w^3+12*w^2-3=0) :
    let b₀ := (64*w^3)⁻¹
    let a₀ := (12-24*w^2)*b₀
    family 2 4 a₀ b₀ ≠ family 2 4 (conj a₀) (conj b₀) ∧ b₀ ≠ 0 ∧
    (∀ z : ℂ, (family 2 4 a₀ b₀).eval z = 16*b₀*(z-w)^3*(z+3*w) ∧
      (family 2 4 (conj a₀) (conj b₀)).eval z =
        16*conj b₀*(z-conj w)^3*(z+3*conj w)) := by
  intro b₀ a₀
  have hw₀ : w ≠ 0 := by
    intro h
    simpa [h] using hw.1
  have hden : 64*w^3 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hw₀)
  have hb : b₀ ≠ 0 := inv_ne_zero hden
  have hinv : (64*w^3)*b₀ = 1 := mul_inv_cancel₀ hden
  have hf (z : ℂ) : model a₀ b₀ z = 16*b₀*(z-w)^3*(z+3*w) := by
    unfold model a₀
    linear_combination 4*b₀*hw.2 - (2*z+1)*hinv
  have hc (z : ℂ) : model (conj a₀) (conj b₀) z = 16*conj b₀*(z-conj w)^3*(z+3*conj w) := by
    simpa [model, map_ofNat] using congrArg conj (hf (conj z))
  refine ⟨?_, hb, fun z => ⟨(eval_model _ _ _).trans (hf z), (eval_model _ _ _).trans (hc z)⟩⟩
  intro heq
  have he := congrArg (fun p : Polynomial ℂ => p.eval w) heq
  change (family 2 4 a₀ b₀).eval w = (family 2 4 (conj a₀) (conj b₀)).eval w at he
  rw [eval_model, hf, eval_model, hc] at he
  have hn : conj b₀ ≠ 0 := by simpa using hb
  rcases candidate_roots hn (by simpa using he.symm) with h | h <;>
    have hi := congrArg Complex.im h <;> norm_num [Complex.mul_im] at hi <;> linarith [hw.1]

private theorem candidate_root_height {u z : ℂ} (h : z = u ∨ z = -(3*u)) : |u.im| ≤ |z.im| := by
  rcases h with h | h
  · rw [h]
  · rw [h]
    norm_num [Complex.mul_im, abs_mul]
    linarith [abs_nonneg u.im]

theorem quartic_candidate_heights (w : ℂ) (hw : 0 < w.im ∧ 12*w^4+16*w^3+12*w^2-3=0) :
    let b₀ := (64*w^3)⁻¹
    let a₀ := (12-24*w^2)*b₀
    (∀ z : ℂ, (family 2 4 a₀ b₀).eval z = 0 → w.im ≤ |z.im|) ∧
    (∀ z : ℂ, (family 2 4 (conj a₀) (conj b₀)).eval z = 0 → w.im ≤ |z.im|) ∧
    (family 2 4 a₀ b₀).eval w = 0 ∧
    (family 2 4 (conj a₀) (conj b₀)).eval (conj w) = 0 := by
  intro b₀ a₀
  obtain ⟨_, hb, hf⟩ := quartic_candidate w hw
  change b₀ ≠ 0 at hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [(hf z).1] at hz
    simpa [abs_of_pos hw.1] using candidate_root_height (candidate_roots hb hz)
  · intro z hz
    rw [(hf z).2] at hz
    have hn : conj b₀ ≠ 0 := by simpa using hb
    simpa [abs_of_pos hw.1] using candidate_root_height (candidate_roots hn hz)
  · rw [(hf w).1]
    simp
  · rw [(hf (conj w)).2]
    simp

#print axioms quartic_candidate
#print axioms quartic_candidate_heights

end Turan
