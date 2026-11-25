-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.GirouxJacobi
import Turan.GirouxSchur
import Turan.GirouxRounding

noncomputable section
open Polynomial Module Matrix
open scoped ComplexConjugate InnerProductSpace
namespace Turan
open Giroux

private theorem combination_degree (k : ℕ) (d : Fin (k+1) → ℂ) :
    (combination k d).natDegree = k+1 := by
  have hdeg (j : ℕ) : (mode j).natDegree = j := by
    rw [mode, natDegree_C_mul (inv_ne_zero (by exact_mod_cast (scale_pos j).ne')), (hermite_degree j).1]
  have hlow : (∑ j, C (d j)*mode j.val).natDegree ≤ k :=
    natDegree_sum_le_of_forall_le _ _ fun j _ =>
      (natDegree_C_mul_le _ _).trans ((hdeg j.val).le.trans (Nat.le_of_lt_succ j.isLt))
  rw [combination, natDegree_add_eq_left_of_natDegree_lt (by rw [hdeg]; omega), hdeg]

/-- Giroux's sum of root heights in the normalized Hermite basis. The top
coefficient is one and d consists of the lower coefficients divided by it.
Polynomial.roots counts every zero with its algebraic multiplicity. -/
theorem giroux_sum_im_roots (k : ℕ) (d : Fin (k+1) → ℂ) :
    (((combination k d).roots.map (fun z : ℂ => |z.im|)).sum) ≤
      Real.sqrt (((k+1:ℕ):ℝ)/2) * Real.sqrt (∑ i, ‖d i‖^2) := by
  let u : EuclideanSpace ℂ (Fin (k+1)) := WithLp.toLp 2 (Pi.single (Fin.last k) (gamma (k+1) : ℂ))
  let v : EuclideanSpace ℂ (Fin (k+1)) := WithLp.toLp 2 (star d)
  let J := (jacobi (k+1)).toEuclideanLin
  let A := perturbed k d
  have hA : A.toEuclideanLin = J - (InnerProductSpace.rankOne ℂ u v).toLinearMap := by
    change Matrix.toEuclideanLin (_ - _) = _
    rw [map_sub]
    congr 1
    apply Matrix.toEuclideanLin.symm.injective
    rw [LinearEquiv.symm_apply_apply, InnerProductSpace.symm_toEuclideanLin_rankOne]
    simp [u, v]
  have hch : A.toEuclideanLin.charpoly = A.charpoly := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.charpoly_toLin]
  have hr : (combination k d).roots = A.charpoly.roots := by
    apply Multiset.eq_of_le_of_card_le (Polynomial.roots.le_of_dvd A.charpoly_monic.ne_zero
      (combination_dvd_charpoly k d))
    rw [splits_iff_card_roots.mp (IsAlgClosed.splits (combination k d)), combination_degree]
    exact (card_roots' _).trans (by simp [A])
  have hu : ‖u‖ = gamma (k+1) := by
    have hnon : 0 ≤ gamma (k+1) := by unfold gamma; positivity
    simp [u, PiLp.toLp_single, PiLp.norm_single, Real.norm_of_nonneg hnon]
  have hv : ‖v‖ = Real.sqrt (∑ i, ‖d i‖^2) := by
    simp [EuclideanSpace.norm_eq, v, Pi.star_apply]
  have hg : gamma (k+1) = Real.sqrt (((k+1:ℕ):ℝ)/2) := by
    apply (sq_eq_sq₀ (by unfold gamma; positivity) (Real.sqrt_nonneg _)).mp
    rw [gamma, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    ring
  have h := rank_one_root_sum _ J (Matrix.isSymmetric_toEuclideanLin_iff.mpr (jacobi_hermitian _)) u v
  rwa [hr, ← hch, hA, ← hg, ← hu, ← hv]

/-- Coefficient form of the multiplicity sum for an arbitrary nonzero top coefficient. -/
theorem giroux_coefficient_sum (k : ℕ) (b : ℂ) (hb : b ≠ 0) (c : Fin (k+1) → ℂ) :
    let Q := C b * mode (k+1) + ∑ i, C (c i) * mode i.val
    ‖b‖ * (Q.roots.map (fun z : ℂ => |z.im|)).sum ≤
      Real.sqrt (((k+1:ℕ):ℝ)/2) * Real.sqrt (∑ i, ‖c i‖^2) := by
  dsimp only
  let d (i : Fin (k+1)) := c i / b
  have hQ : C b * combination k d = C b * mode (k+1) + ∑ i, C (c i) * mode i.val := by
    rw [combination, mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc, ← C_mul, show b*d i = c i by dsimp [d]; field_simp]
  have hnorm : ‖b‖ * Real.sqrt (∑ i, ‖d i‖^2) = Real.sqrt (∑ i, ‖c i‖^2) := by
    conv_lhs => lhs; rw [← Real.sqrt_sq (norm_nonneg b)]
    rw [← Real.sqrt_mul (sq_nonneg _), Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [d]
    rw [norm_div, div_pow]
    field_simp [norm_ne_zero_iff.mpr hb]
  rw [← hQ, roots_C_mul _ hb, ← hnorm, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (giroux_sum_im_roots k d) (norm_nonneg b)

private theorem sparse_sum {ι R : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid R]
    (x y z : ι) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (A B D : ℂ)
    (f : ι → ℂ → R) (hf : ∀ i, f i 0 = 0) :
    ∑ i, f i (if i=x then A else if i=y then B else if i=z then D else 0) =
      f x A + f y B + f z D := by
  calc
    _ = ∑ i, ((if i=x then f i A else 0) + (if i=y then f i B else 0) +
          (if i=z then f i D else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp_all
    _ = _ := by simp [Finset.sum_add_distrib]

theorem giroux_family (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m) (a b : ℂ)
    (hs : emptyStrip (normalizedFamily n m a b) (87/100)) :
    (87/100)*Real.sqrt (2*(m:ℝ))*‖b‖ ≤ Real.sqrt 3 + ‖a‖ := by
  classical
  by_cases hb : b = 0
  · subst b; simp; positivity
  cases m with
  | zero => omega
  | succ k =>
    let i : Fin (k+1) := 0
    let j : Fin (k+1) := ⟨1, by omega⟩
    let l : Fin (k+1) := ⟨n, hnm⟩
    have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
    have hil : i ≠ l := by simp [i, l, Fin.ext_iff]; omega
    have hjl : j ≠ l := by simp [j, l, Fin.ext_iff]; omega
    let s := (Real.sqrt 2 : ℂ)
    let d (t : Fin (k+1)) : ℂ := if t=i then 1/b else if t=j then s/b else if t=l then a/b else 0
    let p := combination k d
    have hev (z : ℂ) : b*p.eval z = normalizedFamily n (k+1) a b z := by
      simp only [p, combination, eval_add, eval_finsetSum, eval_mul, eval_C, mode_eval, d]
      rw [sparse_sum i j l hij hil hjl (1/b) (s/b) (a/b) (fun t c => c * psi t.val z)
        (fun t => zero_mul _)]
      have hsne : s ≠ 0 := by dsimp [s]; exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)).ne'
      change b*(psi (k+1) z + (1/b*psi 0 z + s/b*psi 1 z + a/b*psi n z)) = _
      have h0 : psi 0 z = 1 := by simp [psi, hermite]
      have h1 : psi 1 z = 2*z/s := by simp [psi, hermite, s, eval_mul]
      rw [h0, h1]; unfold normalizedFamily
      field_simp [hb, hsne]
      ring
    have hlower (t : Multiset ℂ) (ht : ∀ z ∈ t, (87/100:ℝ) ≤ |z.im|) :
        (t.card:ℝ)*(87/100) ≤ (t.map (fun z : ℂ => |z.im|)).sum := by
      induction t using Multiset.induction_on with
      | empty => simp
      | cons x t ih =>
        have hx := ht x (Multiset.mem_cons_self ..)
        have h := ih fun z hz => ht z (Multiset.mem_cons_of_mem hz)
        simp only [Multiset.card_cons, Nat.cast_add, Nat.cast_one, Multiset.map_cons, Multiset.sum_cons]
        linarith
    have hlo := hlower p.roots (fun z hz => le_of_not_gt fun hin =>
      hs z hin (by rw [← hev, isRoot_of_mem_roots hz, mul_zero]))
    have hcard : p.roots.card = k+1 := (splits_iff_card_roots.mp (IsAlgClosed.splits p)).trans
      (combination_degree k d)
    rw [hcard] at hlo
    have h := hlo.trans (giroux_sum_im_roots k d)
    have hnorm : ‖b‖ * Real.sqrt (∑ t, ‖d t‖^2) = Real.sqrt (3 + ‖a‖^2) := by
      rw [show (∑ t, ‖d t‖^2) = _ from sparse_sum i j l hij hil hjl (1/b) (s/b) (a/b)
        (fun _ c => ‖c‖^2) (by simp)]
      simp only [norm_div, norm_one, s, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      conv_lhs => lhs; rw [← Real.sqrt_sq (norm_nonneg b)]
      rw [← Real.sqrt_mul (sq_nonneg _)]
      congr 1
      field_simp [norm_ne_zero_iff.mpr hb]
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    let M : ℝ := k+1
    have hM : 0 < M := by dsimp [M]; positivity
    have hroot : Real.sqrt (2*M) * Real.sqrt (M/2) = M := by
      rw [← Real.sqrt_mul (by positivity), show 2*M*(M/2) = M^2 by ring, Real.sqrt_sq hM.le]
    have h' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h (norm_nonneg b))
      (Real.sqrt_nonneg (2*M))
    push_cast at h' ⊢
    change Real.sqrt (2*M)*(M*(87/100)*‖b‖) ≤ Real.sqrt (2*M)*(Real.sqrt (M/2)*
      Real.sqrt (∑ t, ‖d t‖^2)*‖b‖) at h'
    have hmain : M*((87/100)*Real.sqrt (2*M)*‖b‖) ≤ M * Real.sqrt (3+‖a‖^2) := by
      calc
        _ = _ := by ring
        _ ≤ _ := h'
        _ = (Real.sqrt (2*M) * Real.sqrt (M/2)) * (‖b‖ * Real.sqrt (∑ t, ‖d t‖^2)) := by ring
        _ = _ := by rw [hroot, hnorm]
    exact (le_of_mul_le_mul_left hmain hM).trans (Real.sqrt_le_left (by positivity) |>.mpr
      (by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), mul_nonneg (Real.sqrt_nonneg 3) (norm_nonneg a)]))

theorem circle_giroux_cut (w : CircleRow) (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m) (a b : ℂ)
    (hs : emptyStrip (scaledFamily n m a b) (87/100)) (hk : w.test = .giroux) :
    w.cut n m ‖a‖ ‖b‖ :=
  circle_cut_of_bound w n m a b hs hk (giroux_family n m hn hnm)

end Turan
