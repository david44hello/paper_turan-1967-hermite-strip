module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.UpperTailNodesScalar
public import Turan.TailNodes
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

noncomputable section
open Set Filter Real
open scoped Topology
namespace Turan.UpperTailNodes

private theorem weight_deriv (v : ℝ) (hv : 0 < v) :
    HasDerivAt logCoth (-2*alpha/sinh (2*alpha*v)) v := by
  have hx := mul_pos alpha_pos hv
  have hs := sinh_pos_iff.mpr hx
  have hc := cosh_pos (alpha*v)
  have ha := (hasDerivAt_id v).const_mul alpha
  have hd := (ha.cosh.log hc.ne').sub (ha.sinh.log hs.ne')
  apply (hd.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards [lt_mem_nhds hv] with t ht
    simp only [logCoth, log_inv, Real.tanh_eq_sinh_div_cosh,
      log_div (sinh_pos_iff.mpr (mul_pos alpha_pos ht)).ne' (cosh_pos _).ne', neg_sub, Pi.sub_apply, id_eq]
  · dsimp
    rw [mul_assoc 2 alpha v, sinh_two_mul]
    field_simp
    linear_combination -alpha * cosh_sq_sub_sinh_sq (alpha*v)

private theorem weight_deriv2 (v : ℝ) (hv : 0 < v) :
    HasDerivAt (deriv logCoth) (4*alpha^2*cosh (2*alpha*v)/(sinh (2*alpha*v))^2) v := by
  have hs := sinh_pos_iff.mpr (show 0 < 2*alpha*v by have := alpha_pos; positivity)
  have hd := (hasDerivAt_const v (-2*alpha)).div (((hasDerivAt_id v).const_mul (2*alpha)).sinh) hs.ne'
  apply (hd.congr_deriv (by dsimp; ring)).congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hv] with t ht using (weight_deriv t ht).deriv

theorem logCoth_shape :
    StrictAntiOn logCoth (Ioi 0) ∧ StrictConvexOn ℝ (Ioi 0) logCoth ∧
    ∀ v : ℝ, 0 < v → 0 < logCoth v ∧
      HasDerivAt logCoth (-2*alpha/Real.sinh (2*alpha*v)) v ∧
      HasDerivAt (deriv logCoth)
        (4*alpha^2*Real.cosh (2*alpha*v)/(Real.sinh (2*alpha*v))^2) v := by
  have ha := alpha_pos
  have hc : ContinuousOn logCoth (Ioi 0) := fun x hx => (weight_deriv x hx).continuousAt.continuousWithinAt
  refine ⟨strictAntiOn_of_deriv_neg (convex_Ioi _) hc ?_,
    strictConvexOn_of_deriv2_pos' (convex_Ioi _) hc ?_, ?_⟩
  · intro x hx
    have hx' : 0 < x := interior_subset hx
    rw [(weight_deriv x hx').deriv]
    exact div_neg_of_neg_of_pos (by linarith) (sinh_pos_iff.mpr (by positivity))
  · intro x (hx : 0 < x)
    rw [show (deriv^[2] logCoth) x = deriv (deriv logCoth) x from rfl, (weight_deriv2 x hx).deriv]
    have := sinh_pos_iff.mpr (show 0 < 2*alpha*x by positivity)
    positivity
  · intro v hv
    refine ⟨?_, weight_deriv v hv, weight_deriv2 v hv⟩
    rw [logCoth, log_inv]
    apply neg_pos.mpr
    apply log_neg _ (tanh_lt_one _)
    rw [tanh_eq_sinh_div_cosh]; exact div_pos (sinh_pos_iff.mpr (mul_pos ha hv)) (cosh_pos _)

theorem pair_midpoint (d e h : ℝ) (i : ℕ) (hd : 0 < d) (he : 0 < e) (hh : 0 < h)
    (hpair : d+e ≤ (2*(i:ℝ)+1)*h) :
    2*logCoth (((i:ℝ)+1/2)*h) ≤ logCoth d + logCoth e := by
  have hmid := logCoth_shape.2.1.convexOn.2 hd he (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at hmid
  have ha := logCoth_shape.1.antitoneOn (show 0 < (1/2:ℝ)*d+1/2*e by positivity)
    (show 0 < ((i:ℝ)+1/2)*h by positivity) (by linarith only [hpair])
  linarith only [hmid, ha]

private theorem weight_series (x : ℝ) (hx : 0 < x) :
    HasSum (fun l => 2/oddFreq l * exp (-2*(alpha*x)*oddFreq l)) (logCoth x) := by
  let u := exp (-2*(alpha*x))
  have hu : 0 < u := exp_pos _
  have hu' : u < 1 := exp_lt_one_iff.mpr (by have := mul_pos alpha_pos hx; linarith)
  have hs := hasSum_log_sub_log_of_abs_lt_one (show |u| < 1 by rwa [abs_of_pos hu])
  have he : tanh (alpha*x) = (1-u)/(1+u) := by
    rw [tanh_eq]
    dsimp [u]
    rw [show -2*(alpha*x) = -(alpha*x) + -(alpha*x) by ring, exp_add, exp_neg]
    field_simp
  rw [logCoth, log_inv, he, log_div (sub_pos.mpr hu').ne' (by positivity), neg_sub]
  convert hs using 1
  funext k
  dsimp [oddFreq,u]
  rw [← Real.exp_nat_mul]
  push_cast
  ring_nf

theorem full_midpoint_series (N : ℕ) (h : ℝ) (hh : 0 < h) :
    HasSum (oddContribution N h) (midpointSum N h) := by
  let x (i : Fin N) : ℝ := ((i.val:ℝ)+1/2)*h
  have hx (i : Fin N) : 0 < x i := by dsimp [x]; positivity
  have hs := (hasSum_sum (s := Finset.univ) (fun (i : Fin N) _ => weight_series (x i) (hx i))).mul_left 2
  change HasSum _ (2*∑ i, logCoth (x i))
  convert hs using 1
  funext l
  let c := alpha*oddFreq l*h
  have hℓ : 0 < oddFreq l := by dsimp [oddFreq]; positivity
  have hc : 0 < c := mul_pos (mul_pos alpha_pos hℓ) hh
  have hg := tail_odd_lattice_sum N c
  have he (i : Fin N) : -2*(alpha*x i)*oddFreq l = -(2*(i.val:ℝ)+1)*c := by dsimp [x,c]; ring
  simp only [he, ← Finset.mul_sum]
  change 2*(1-exp (-2*alpha*oddFreq l*(N:ℝ)*h))/(oddFreq l*sinh c) = _
  rw [show -2*alpha*oddFreq l*(N:ℝ)*h = -2*(N:ℝ)*c by dsimp [c]; ring, ← hg]
  generalize (∑ i : Fin N, exp (-(2*(i.val:ℝ)+1)*c)) = S
  field_simp [(sinh_pos_iff.mpr hc).ne', hℓ.ne']
  <;> ring

theorem full_node_lower_bound (j : ℕ) (hj : 225 ≤ j) (h0 : psi j (-1/2) ≠ 0) :
    midpointSum (nodeCount j) (eta j) ≤ -Real.log (nodeProduct j) ∧
    (∑' i : ℕ, oddContribution (nodeCount j) (eta j) i) ≤ -Real.log (nodeProduct j) := by
  have pairs := tail_node_pairs j hj h0
  dsimp only at pairs
  rw [show Real.pi / Real.sqrt (2*(j:ℝ)-1125/100) = eta j by norm_num [eta]] at pairs
  rw [← show nodeCount j = ⌊3/eta j⌋₊ from rfl] at pairs
  obtain ⟨d,e,hd,he,hp⟩ := pairs
  have hη := (eta_bounds j hj).1
  have hpair (i : Fin (nodeCount j)) := pair_midpoint _ _ _ i.val (hp i).1 (hp i).2.1 hη (hp i).2.2.2.2
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpair i)
  have hnodes := tail_node_pair_sum_le j _ h0 d e hd he (fun i =>
    ⟨(hp i).1, (hp i).2.1, (hp i).2.2.1, (hp i).2.2.2.1⟩)
  have h : midpointSum (nodeCount j) (eta j) ≤ -log (nodeProduct j) := by
    refine (show midpointSum (nodeCount j) (eta j) ≤ _ from ?_).trans hnodes
    simpa only [midpointSum, Finset.mul_sum, logCoth, log_inv, alpha, sub_eq_add_neg] using hsum
  exact ⟨h, (full_midpoint_series _ _ hη).tsum_eq.trans_le h⟩

end Turan.UpperTailNodes
