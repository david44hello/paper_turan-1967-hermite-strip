-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Small34Nodes
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

noncomputable section
open Polynomial Real Set
open scoped ComplexConjugate
namespace Turan

def small34Angle (l r : ℝ) (z : ℂ) : ℝ :=
  arctan ((r-z.re)/z.im) - arctan ((l-z.re)/z.im)

theorem small34Angle_conj (l r : ℝ) (z : ℂ) :
    small34Angle l r (conj z) = -small34Angle l r z := by
  simp [small34Angle, div_neg, arctan_neg]
  ring

theorem small34Angle_pos {l r : ℝ} {z : ℂ} (hlr : l < r) (hy : 0 < z.im) :
    0 < small34Angle l r z ∧ small34Angle l r z < π := by
  unfold small34Angle
  exact ⟨sub_pos.mpr (arctan_strictMono ((div_lt_div_iff_of_pos_right hy).mpr (by linarith))),
    by linarith [arctan_lt_pi_div_two ((r-z.re)/z.im), neg_pi_div_two_lt_arctan ((l-z.re)/z.im)]⟩

private theorem centered_angle (s t : ℝ) (hs : 0 ≤ s) :
    arctan (s+t) + arctan (s-t) ≤ 2*arctan s := by
  let f (x : ℝ) := arctan (s+x) + arctan (s-x)
  have anti : AntitoneOn f (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _) (by dsimp [f]; fun_prop) (fun x _ =>
      ((((hasDerivAt_id x).const_add s).arctan).add (((hasDerivAt_id x).const_sub s).arctan)).differentiableAt.differentiableWithinAt)
    intro x hx
    have hx' : 0 ≤ x := interior_subset hx
    have hd := (((hasDerivAt_id x).const_add s).arctan).add (((hasDerivAt_id x).const_sub s).arctan)
    rw [hd.deriv]
    simp only [id_eq, mul_one, mul_neg, ← sub_eq_add_neg, sub_nonpos]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [mul_nonneg hs hx']
  have h (x : ℝ) (hx : 0 ≤ x) := anti (show 0 ∈ Ici (0:ℝ) from mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
  rcases le_total 0 t with ht | ht
  · simpa [f,two_mul] using h t ht
  · simpa [f,two_mul,sub_eq_add_neg,add_comm] using h (-t) (neg_nonneg.mpr ht)

theorem small34Angle_width {l r : ℝ} {z : ℂ} (hlr : l < r) (hy : 0 < z.im) :
    small34Angle l r z ≤ 2*arctan ((r-l)/(2*z.im)) := by
  let s := (r-l)/(2*z.im)
  let t := ((l+r)/2-z.re)/z.im
  have hs : 0 ≤ s := div_nonneg (sub_nonneg.mpr hlr.le) (by positivity)
  have h := centered_angle s t hs
  rw [show s+t = (r-z.re)/z.im by dsimp [s,t]; field_simp; ring,
    show s-t = -((l-z.re)/z.im) by dsimp [s,t]; field_simp; ring, arctan_neg] at h
  exact h

theorem small34Angle_arg_quotient (l r : ℝ) (z : ℂ) (hy : z.im ≠ 0) :
    (small34Angle l r z : Angle) = ((((r:ℂ)-z)/((l:ℂ)-z)).arg : ℝ) := by
  let v (t : ℝ) : ℂ := ⟨1,(t-z.re)/z.im⟩
  have hv (t : ℝ) : v t ≠ 0 := by intro e; have := congrArg Complex.re e; norm_num [v] at this
  have ha (t : ℝ) : arctan ((t-z.re)/z.im) = (v t).arg := by
    apply arctan_eq_of_tan_eq
    · rw [Complex.tan_arg]; simp [v]
    · exact abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (.inl (by dsimp [v]; norm_num)))
  have he (t : ℝ) : (t:ℂ)-z = v t * (-Complex.I*(z.im:ℂ)) := by
    apply Complex.ext <;> simp [v,Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,hy]
  rw [he r, he l, mul_div_mul_right _ _ (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr hy)), Complex.arg_div_coe_angle (hv _) (hv _)]
  simp [small34Angle, ha, Angle.coe_sub]

theorem small34Angle_sum {a b : ℂ} {l r : ℝ} (hl : 2*l+1 ≠ 0)
    (hn : Small34Node l r) {z : Fin 4 → ℂ} (hy : ∀ i, (z i).im ≠ 0)
    (hf : family 3 4 a b = C (family 3 4 a b).leadingCoeff * ∏ i, (X-C (z i)))
    (hp : family 3 4 a b ≠ 0) :
    ((∑ i, small34Angle l r (z i) : ℝ) : Angle) =
      ((↑((2*r+1)/(2*l+1)) : ℂ).arg : Angle) := by
  let f (i : Fin 4) := ((r:ℂ)-z i)/((l:ℂ)-z i)
  have ne (t : ℝ) (i : Fin 4) : (t:ℂ)-z i ≠ 0 := by
    intro e
    exact hy i (by rw [← sub_eq_zero.mp e]; simp)
  have hlc : 2*(l:ℂ)+1 ≠ 0 := by exact_mod_cast hl
  have hprod : ∏ i, f i = (↑((2*r+1)/(2*l+1)) : ℂ) := by
    have he := hn a b
    rw [hf] at he
    simp only [eval_mul,eval_prod,eval_sub,eval_C,eval_X] at he
    dsimp [f]
    rw [Finset.prod_div_distrib]
    push_cast
    apply (div_eq_div_iff (Finset.prod_ne_zero_iff.mpr (fun i _ => ne l i)) hlc).mpr
    apply mul_left_cancel₀ (leadingCoeff_ne_zero.mpr hp)
    linear_combination -he
  have harg (s : Finset (Fin 4)) :
      (((∏ i ∈ s, f i).arg : ℝ) : Angle) = ∑ i ∈ s, ((f i).arg : Angle) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      have aux (j : Fin 4) : f j ≠ 0 := div_ne_zero (ne r j) (ne l j)
      rw [Finset.prod_insert hi,Finset.sum_insert hi,Complex.arg_mul_coe_angle (aux i)
        (Finset.prod_ne_zero_iff.mpr (fun j _ => aux j)),ih]
  change Angle.coeHom (∑ i, _) = _
  rw [map_sum, ← hprod, harg]
  exact Finset.sum_congr rfl (fun i _ => small34Angle_arg_quotient l r (z i) (hy i))

end Turan
