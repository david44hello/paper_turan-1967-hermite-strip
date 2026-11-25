-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.WindingDefs
import Turan.ChartReduction
import Turan.Transfer
import Turan.Rouche
import Turan.Polygon

noncomputable section
open Polynomial
namespace Turan

private theorem winding_real_mul (j m : ℕ) :
    ∃ s : ℝ, s ≠ 0 ∧ windingMode j m = C (s:ℂ)*hermite j := by
  obtain ⟨s, hs, hrep⟩ := transferMode_eq_real_mul j
  by_cases he : Even j
  · exact ⟨s,hs, by simpa [windingMode, transferMode, he] using hrep⟩
  have hn : (chartScale m : ℝ) ≠ 0 := by
    exact_mod_cast (show chartScale m ≠ 0 by unfold chartScale; omega)
  refine ⟨(chartScale m : ℝ)/2*s, mul_ne_zero (div_ne_zero hn (by norm_num)) hs, ?_⟩
  have hwind : windingMode j m = C ((chartScale m:ℂ)/2)*transferMode j := by
    simp only [windingMode, transferMode, if_neg he, ← mul_assoc, ← map_mul]
    congr 2
    ring
  rw [hwind,hrep,← mul_assoc,← map_mul]
  push_cast
  rfl

theorem strip_disk_forces_zero (p : Polynomial ℂ) (h : ℝ) (check : StripDiskCheck p h) :
    ∃ z : ℂ, p.eval z = 0 ∧ |z.im| < h := by
  obtain ⟨w,r,k,hr,hgeo,hk,hmargin⟩ := check
  let q := diskExpansion p w r
  have hcount := dominant_polynomial_term q k hk (sub_pos.mp hmargin)
  obtain ⟨v, hv⟩ := Multiset.card_pos_iff_exists_mem.mp (hcount.symm ▸ hk)
  obtain ⟨hvroot,hvsmall⟩ := Multiset.mem_filter.mp hv
  refine ⟨w+(r:ℂ)*v, by simpa [q,diskExpansion,eval_comp,eval_mul] using isRoot_of_mem_roots hvroot, ?_⟩
  apply disk_in_strip _ _ _ h hgeo
  rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_of_nonneg hr.le]
  exact mul_le_of_le_one_right hr.le hvsmall.le

theorem winding_certificate_gap (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m)
    (check : WindingCertificate n m) (a b : ℂ) :
    ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| < 87/100 := by
  obtain ⟨s, hs, hP⟩ := winding_real_mul n m
  obtain ⟨t, ht, hQ⟩ := winding_real_mul m m
  have chart (i j : ℕ) (hij : (i=n ∧ j=m) ∨ (i=m ∧ j=n)) (χ κ : ℂ)
      (hχ : ‖χ‖ ≤ 1) (him : 0 ≤ χ.im) :
      ∃ z : ℂ, (chartPoly (windingMode i m) (windingMode j m) χ κ).eval z = 0 ∧ |z.im| < 87/100 := by
    obtain ⟨r, hr, hrh, hcert⟩ := check i j hij χ hχ him
    by_contra! outside
    have cap := affine_chart_cap (windingMode i m) (windingMode j m) χ κ r hr hrh
      (fun z hz hzero => hz.not_ge (outside z hzero))
    rcases hcert κ cap with hw | hd
    · obtain ⟨z, hz, hstrip⟩ := polygon_forces_zero _ _ hw
      exact hstrip.not_ge (outside z hz)
    · obtain ⟨z, hz, hstrip⟩ := strip_disk_forces_zero _ _ hd
      exact hstrip.not_ge (outside z hz)
  apply high_chart_reduction n m _ _ s t hs ht hP hQ _ a b
  rintro _ _ (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
  · exact chart n m (.inl ⟨rfl,rfl⟩)
  · exact chart m n (.inr ⟨rfl,rfl⟩)

end Turan
