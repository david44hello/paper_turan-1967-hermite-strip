module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs
public import Mathlib.Tactic

@[expose] public section

open Polynomial
namespace Turan

/-- A node equality gives a product over all roots with multiplicities,
in the shifted variable w = z + 1/2. -/
theorem shifted_node_product (p : Polynomial ℂ) (l r : ℝ)
    (hnode : p.eval ((l:ℂ)-1/2)*r = p.eval ((r:ℂ)-1/2)*l)
    (hr : r ≠ 0) (hev : p.eval ((r:ℂ)-1/2) ≠ 0) :
    (p.roots.map (fun z => ‖(z+1/2)-(l:ℂ)‖ / ‖(z+1/2)-(r:ℂ)‖)).prod = |l| / |r| := by
  let P (u : ℝ) := (p.roots.map (fun z => ‖(z+1/2)-(u:ℂ)‖)).prod
  have he (u : ℝ) : ‖p.eval ((u:ℂ)-1/2)‖ = ‖p.leadingCoeff‖ * P u := by
    rw [(IsAlgClosed.splits p).eval_eq_prod_roots, norm_mul, Multiset.norm_prod, Multiset.map_map]
    congr 1
    apply congrArg Multiset.prod
    apply Multiset.map_congr rfl
    intro z _
    change ‖(u:ℂ)-1/2-z‖ = ‖(z+1/2)-(u:ℂ)‖
    rw [norm_sub_rev (z+1/2) _]
    congr 1
    ring
  have hn : ‖p.leadingCoeff‖ * P r ≠ 0 := he r ▸ (norm_ne_zero_iff.mpr hev)
  have hab := congrArg norm hnode
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, he] at hab
  rw [Multiset.prod_map_div]
  change P l / P r = |l| / |r|
  apply (div_eq_div_iff (right_ne_zero_of_mul hn) (abs_ne_zero.mpr hr)).mpr
  apply mul_left_cancel₀ (left_ne_zero_of_mul hn)
  linear_combination hab

/-- Moving a real node by at most ε changes its distance factor by a
multiplicative factor at most 1 + ε/H at height at least H. -/
theorem real_node_dist_le (w : ℂ) (l r ε H : ℝ) (hH : 0 < H)
    (hw : H ≤ |w.im|) (hlr : |l-r| ≤ ε) :
    ‖w-(l:ℂ)‖ ≤ (1+ε/H)*‖w-(r:ℂ)‖ := by
  have hdist : H ≤ ‖w-(r:ℂ)‖ := hw.trans (by simpa using Complex.abs_im_le_norm (w-(r:ℂ)))
  have hε : 0 ≤ ε/H := div_nonneg ((abs_nonneg _).trans hlr) hH.le
  have he : ε/H*H = ε := div_mul_cancel₀ _ hH.ne'
  have htri := dist_triangle w (r:ℂ) (l:ℂ)
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_sub_comm r l] at htri
  linarith only [htri,hlr,he,mul_le_mul_of_nonneg_left hdist hε]

end Turan
