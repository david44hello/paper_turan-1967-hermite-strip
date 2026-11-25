-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.ProjectiveDefs
import Turan.Rouche

noncomputable section
open Polynomial
namespace Turan

private theorem projective_root (basis : Fin 3 → Polynomial ℂ) (u : Fin 3 → ℂ)
    (h : ℝ) (hh : 0 < h) (D : ℕ) (check : ProjectiveDiskCheck basis 65536 h D) :
    ∃ z : ℂ, (∑ j, C (u j)*basis j).eval z = 0 ∧ |z.im| < h := by
  classical
  obtain ⟨i, _, hm⟩ := Finset.exists_max_image Finset.univ (fun j => ‖u j‖) Finset.univ_nonempty
  by_cases hi : u i = 0
  · have hu (j) : u j = 0 := norm_le_zero_iff.mp <| by simpa [hi] using hm j (Finset.mem_univ _)
    exact ⟨0, by simp [hu], by simpa using hh⟩
  let v j := u j / u i
  have hv (j) : ‖v j‖ ≤ 1 := by
    dsimp only [v]
    rw [norm_div, div_le_one (norm_pos_iff.mpr hi)]
    exact hm _ (Finset.mem_univ _)
  obtain ⟨x,y,r,k,hr,hk,_,hgeo,hd⟩ := check i v (div_self hi) (fun j =>
    ⟨(Complex.abs_re_le_norm _).trans (hv j), (Complex.abs_im_le_norm _).trans (hv j)⟩)
  let w : ℂ := ⟨(x:ℝ)/65536, (y:ℝ)/65536⟩
  let ρ : ℝ := (r:ℝ)/65536
  let g := ∑ j, C (v j)*basis j
  let p := g.comp (C w+C (ρ:ℂ)*X)
  change |w.im| + ρ ≤ h at hgeo
  have count := dominant_polynomial_term p k hk hd
  obtain ⟨t, ht⟩ := Multiset.card_pos_iff_exists_mem.mp (count.symm ▸ hk)
  obtain ⟨htroot, hnorm⟩ := Multiset.mem_filter.mp ht
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let z := w + (ρ:ℂ)*t
  have hzero : g.eval z = 0 := by simpa [p, z, eval_comp, eval_mul] using isRoot_of_mem_roots htroot
  have eqp : (∑ j, C (u j)*basis j) = C (u i)*g := by
    simp only [g, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_assoc, ← map_mul]
    have he : u i * v j = u j := by dsimp [v]; field_simp
    rw [he]
  refine ⟨z, by rw [eqp, eval_mul, hzero, mul_zero], ?_⟩
  change |(w+(ρ:ℂ)*t).im| < h
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have := (Complex.abs_im_le_norm t).trans_lt hnorm
  calc
    _ ≤ |w.im|+|ρ*t.im| := abs_add_le .. 
    _ < |w.im|+ρ := by rw [abs_mul, abs_of_pos hρ]; nlinarith [mul_pos hρ (sub_pos.mpr this)]
    _ ≤ _ := hgeo

theorem quintic_chart_gap (check : QuinticChartCheck) (a b : ℂ) :
    ∃ z : ℂ, (family 3 5 a b).eval z = 0 ∧ |z.im| < 29491/32768 := by
  let u : Fin 3 → ℂ := ![(1-6*a+60*b)/4, a-20*b, 4*b]
  obtain ⟨z, hz, hy⟩ := projective_root (lowBasis 3 5) u _ (by norm_num) 5 check
  refine ⟨z, ?_, hy⟩
  apply Eq.trans _ hz
  norm_num [u, family, hermite, lowBasis, Fin.sum_univ_succ, eval_add, eval_sub, eval_mul,
    eval_pow, nsmul_eq_mul]
  ring

theorem sextic_chart_gap (check : SexticChartCheck) (n : ℕ) (hn : n = 2 ∨ n = 3 ∨ n = 4) (a b : ℂ) :
    ∃ z : ℂ, (family n 6 a b).eval z = 0 ∧ |z.im| < 57016/65536 := by
  let u : Fin 3 → ℂ := if n=2 then ![1/8, (a+180*b)/4, 16*b]
    else if n=3 then ![1/15-2*a/5, 2*a/5, -8*b] else ![1/15, 4*(a-15*b)/5, 4*b]
  obtain ⟨z, hz, hy⟩ := projective_root (lowBasis n 6) u _ (by norm_num) 6
    (check n (by rcases hn with rfl | rfl | rfl <;> decide))
  refine ⟨z, ?_, hy⟩
  apply Eq.trans _ hz
  rcases hn with rfl | rfl | rfl <;>
    norm_num [u, family, hermite, lowBasis, Fin.sum_univ_succ, eval_add, eval_sub, eval_mul,
      eval_pow, nsmul_eq_mul] <;> ring

end Turan
