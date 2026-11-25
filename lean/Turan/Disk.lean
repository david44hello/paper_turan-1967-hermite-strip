-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.DiskNodes
import Turan.BoundedDisk

noncomputable section
open Polynomial
namespace Turan

private theorem trinomial_uniform_disk :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 2 ≤ n → ∀ a : ℂ,
      ∃ z : ℂ, 1+2*z+a*(hermite n).eval z = 0 ∧ ‖z‖ < K := by
  obtain ⟨R, hR, M, hM⟩ := high_mode_small_on_disk 1 zero_le_one
  obtain ⟨S, hS, hbound⟩ := bounded_degree_disk (max M 3)
  refine ⟨max S (R+1), lt_of_lt_of_le hS (le_max_left ..), ?_⟩
  intro n hn a
  by_cases h2 : n = 2
  · subst n
    obtain ⟨z, hz, hr⟩ := hbound 2 3 (by decide) (by decide) (le_max_right ..) a 0
    exact ⟨z, by simpa [family, eval_add, eval_mul] using hz, hr.trans_le (le_max_left ..)⟩
  have hnm : 2 < n := by omega
  by_cases small : n ≤ M
  · obtain ⟨z, hz, hr⟩ := hbound 2 n (by decide) hnm (small.trans (le_max_left ..)) 0 a
    exact ⟨z, by simpa [family, eval_add, eval_mul] using hz, hr.trans_le (le_max_left ..)⟩
  by_contra! noRoot
  have free (w : ℂ) (hw : ‖w‖ ≤ R) : (family 2 n 0 a).eval w ≠ 0 := by
    intro hz
    have hf := noRoot w (by simpa [family, eval_add, eval_mul] using hz)
    linarith [le_max_right S (R+1)]
  let w : ℂ := -1/2
  have hw : ‖w‖ ≤ 1 := by norm_num [w, norm_div]
  have he : (family 2 n 0 a).eval w = a*(hermite n).eval w := by
    norm_num [w, family, eval_add, eval_mul]
  have hf := free w (hw.trans hR.le)
  have h := hM 2 n (by decide) hnm (by omega) 0 a free w hw
  rw [← he, div_self hf, norm_one] at h
  exact h.false

theorem proposition_three :
    ∃ R : ℝ, 0 < R ∧ ∀ n m : ℕ, 2 ≤ n → n < m → ∀ a b : ℂ,
      (∃ z : ℂ, (family n m a b).eval z = 0 ∧ ‖z‖ < R) ∧
      (∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| < R) := by
  obtain ⟨K, hK, htri⟩ := trinomial_uniform_disk
  obtain ⟨R, hR, M, hmode⟩ := high_mode_small_on_disk K hK.le
  obtain ⟨S, hS, hbound⟩ := bounded_degree_disk M
  refine ⟨max S (R+1), lt_of_lt_of_le hS (le_max_left ..), ?_⟩
  intro n m hn hnm a b
  suffices hroot : ∃ z : ℂ, (family n m a b).eval z = 0 ∧ ‖z‖ < max S (R+1) by
    obtain ⟨z, hz, hr⟩ := hroot
    exact ⟨⟨z,hz,hr⟩, ⟨z,hz,(Complex.abs_im_le_norm z).trans_lt hr⟩⟩
  by_cases hm : m ≤ M
  · obtain ⟨z, hz, hr⟩ := hbound n m hn hnm hm a b
    exact ⟨z,hz,hr.trans_le (le_max_left ..)⟩
  by_contra! noRoot
  have free (w : ℂ) (hw : ‖w‖ ≤ R) : (family n m a b).eval w ≠ 0 := by
    intro hz
    have hf := noRoot w hz
    linarith [le_max_right S (R+1)]
  obtain ⟨w, hw, hr⟩ := htri n hn a
  have hf := free w (hr.trans hR).le
  have he : (family n m a b).eval w = b*(hermite m).eval w := by
    simp [family, eval_add, eval_mul, hw]
  have h := hmode n m hn hnm (by omega) a b free w hr.le
  rw [← he, div_self hf, norm_one] at h
  exact h.false

end Turan
