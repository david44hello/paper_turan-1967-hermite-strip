module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Degree
public import Mathlib.Analysis.Complex.Polynomial.GaussLucas
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Polynomial Set
namespace Turan

private theorem secondDerivative_small (a b : ℂ) (hb : b ≠ 0) :
    ∃ z : ℂ, (family 3 4 a b).derivative.derivative.eval z = 0 ∧ |z.im| < 5/7 := by
  let q : Polynomial ℂ := C (192*b)*X^2 + C (48*a)*X + C (-96*b)
  have hq : (family 3 4 a b).derivative.derivative = q := by
    apply Polynomial.funext
    intro z
    norm_num [family, hermite, q, nsmul_eq_mul, derivative_add, derivative_mul,
      derivative_sub, eval_add, eval_mul, eval_sub]
    ring
  have hB : 192*b ≠ 0 := mul_ne_zero (by norm_num) hb
  have hc := (IsAlgClosed.splits q).natDegree_eq_card_roots.symm.trans (natDegree_quadratic hB)
  obtain ⟨x,y,hxy⟩ := Multiset.card_eq_two.mp hc
  have hfac := (IsAlgClosed.splits q).eq_prod_roots
  rw [show q.leadingCoeff = 192*b from leadingCoeff_quadratic hB, hxy] at hfac
  have hfac' : q = C (192*b)*(X-C x)*(X-C y) := by simpa [mul_assoc] using hfac
  have hc₀ := congrArg (eval 0) hfac'
  simp [q, eval_add, eval_mul, eval_sub] at hc₀
  have hprod : x*y = -1/2 := by
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp (show b*(x*y - -1/2) = 0 by linear_combination -hc₀/192)).resolve_left hb
  have hnorm : ‖x‖*‖y‖ = 1/2 := by simpa [norm_mul,norm_div] using congrArg norm hprod
  rw [hq]
  by_contra! h
  have hx := (h x (by rw [hfac']; simp [eval_mul,eval_sub])).trans (Complex.abs_im_le_norm x)
  have hy := (h y (by rw [hfac']; simp [eval_mul,eval_sub])).trans (Complex.abs_im_le_norm y)
  linarith [mul_le_mul hx hy (by norm_num : (0:ℝ) ≤ 5/7) (norm_nonneg x)]

/-- Sorted roots with multiplicities. Under strip avoidance the first is lower
and the last upper, by two applications of Gauss–Lucas. -/
theorem small34_roots (a b : ℂ) (hb : b ≠ 0)
    (hh : ∀ z : ℂ, (family 3 4 a b).eval z = 0 → 5/7 ≤ |z.im|) :
    ∃ z : Fin 4 → ℂ, Monotone (fun i => (z i).im) ∧
      (z 0).im ≤ -(5/7) ∧ 5/7 ≤ (z 3).im ∧ (∀ i, 5/7 ≤ |(z i).im|) ∧
      family 3 4 a b = C (family 3 4 a b).leadingCoeff * ∏ i, (X-C (z i)) := by
  classical
  let p := family 3 4 a b
  have hd : p.natDegree = 4 := by simp [p, family_degree 3 4 (by decide) (by decide), hb]
  have hdp : 0 < p.degree := natDegree_pos_iff_degree_pos.mp (by omega)
  have hdd : 0 < p.derivative.degree := natDegree_pos_iff_degree_pos.mp
    (by rw [natDegree_derivative, hd]; decide)
  have hdd' : p.derivative.derivative ≠ 0 := ne_zero_of_natDegree_gt
    (show 0 < p.derivative.derivative.natDegree by rw [natDegree_derivative, natDegree_derivative, hd]; decide)
  obtain ⟨q,hq,hsmall⟩ := secondDerivative_small a b hb
  have convex_mem {S : Set ℂ} (hS : Convex ℝ S) (h : p.rootSet ℂ ⊆ S) : q ∈ S := by
    have h1 := (rootSet_derivative_subset_convexHull_rootSet hdp).trans (convexHull_min h hS)
    have h2 := (rootSet_derivative_subset_convexHull_rootSet hdd).trans (convexHull_min h1 hS)
    apply h2
    exact mem_rootSet.mpr ⟨hdd', by simpa using hq⟩
  have split := IsAlgClosed.splits p
  obtain ⟨n, u, hu⟩ := List.exists_iff_exists_tuple.mp
    (show ∃ l : List ℂ, (l : Multiset ℂ) = p.roots from ⟨_, p.roots.coe_toList⟩)
  have hn : n = 4 := by simpa [← hu] using split.natDegree_eq_card_roots.symm.trans hd
  subst n
  let σ := Tuple.sort (fun i => (u i).im)
  let z := u ∘ σ
  have hm : Monotone (fun i => (z i).im) := Tuple.monotone_sort (fun i => (u i).im)
  have hfac : p = C p.leadingCoeff * ∏ i, (X-C (z i)) := by
    calc
      p = _ := split.eq_prod_roots
      _ = _ := by
        rw [← hu, Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, List.prod_ofFn]
        congr 1
        exact (Equiv.prod_comp σ (fun i => X - C (u i))).symm
  have hz (i : Fin 4) : 5/7 ≤ |(z i).im| := by
    apply hh
    change p.eval _ = 0
    rw [hfac, eval_mul, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (sub_self (z i)), mul_zero]
  have hr {c : ℂ} (hc : c ∈ p.rootSet ℂ) : ∃ i, z i = c := by
    have h := (mem_rootSet.mp hc).2
    rw [coe_aeval_eq_eval, hfac, eval_mul, eval_C, eval_prod] at h
    have hne := leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt (show 0 < p.natDegree by omega))
    obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp ((mul_eq_zero.mp h).resolve_left hne)
    exact ⟨i, (sub_eq_zero.mp (by simpa [eval_sub] using hi)).symm⟩
  refine ⟨z,hm,?_,?_,hz,hfac⟩
  · rcases le_abs.mp (hz 0) with h | h
    · have he := convex_mem (S := {c : ℂ | 5/7 ≤ c.im}) (convex_halfSpace_im_ge (5/7)) (by
        intro c hc; obtain ⟨i,rfl⟩ := hr hc; exact h.trans (hm (Fin.zero_le i)))
      exact False.elim ((abs_lt.mp hsmall).2.not_ge he)
    · linarith
  · rcases le_abs.mp (hz 3) with h | h
    · exact h
    · have he := convex_mem (S := {c : ℂ | c.im ≤ -(5/7)}) (convex_halfSpace_im_le (-(5/7))) (by
        intro c hc; obtain ⟨i,rfl⟩ := hr hc
        exact (hm (Fin.le_last i)).trans (show (z 3).im ≤ -(5/7) by linarith))
      exact False.elim ((abs_lt.mp hsmall).1.not_ge he)

end Turan
