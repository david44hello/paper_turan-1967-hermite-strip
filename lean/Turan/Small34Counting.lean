-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Small34Roots
import Turan.Small34Angles
import Mathlib.Algebra.Order.Ring.Interval

noncomputable section
open Real Polynomial Set
open scoped ComplexConjugate
namespace Turan

private def phases (z : Fin 4 → ℂ) : Prop :=
  ∀ l r : ℝ, 2*l+1 ≠ 0 → Small34Node l r →
    ((∑ i, small34Angle l r (z i) : ℝ) : Angle) = ((↑((2*r+1)/(2*l+1)):ℂ).arg : Angle)

private theorem reverse_phases {z : Fin 4 → ℂ} (hp : phases z) :
    phases (fun i => conj (z (Fin.revPerm i))) := by
  intro l r hl hn
  simp only [small34Angle_conj, Finset.sum_neg_distrib, Angle.coe_neg]
  rw [Equiv.sum_comp Fin.revPerm (fun i => small34Angle l r (z i)), hp l r hl hn,
    ← Complex.arg_conj_coe_angle, Complex.conj_ofReal]

private theorem pin {x base : ℝ} (he : (x : Angle) = (base : Angle))
    (hl : base-2*π < x) (hr : x < base+2*π) : x = base := by
  obtain ⟨k,hk⟩ := Angle.angle_eq_iff_two_pi_dvd_sub.mp he
  have hk0 : k = 0 := IsStrictOrderedRing.int_eq_of_mul_mem_Ioo (by positivity : 0 < 2*π)
    (by rw [← hk]; constructor <;> push_cast <;> linarith)
  simp [hk0] at hk
  linarith

private theorem triple_angle_gap : 3*arctan (1/44) < arctan (1/14) := by
  have hd := two_mul_arctan (by norm_num : (-1:ℝ) < 1/44) (by norm_num : (1:ℝ)/44 < 1)
  rw [show 2*(1/44:ℝ)/(1-(1/44:ℝ)^2) = 88/1935 by norm_num] at hd
  have ht := arctan_add (by norm_num : (88/1935:ℝ)*(1/44) < 1)
  rw [show ((88/1935:ℝ)+1/44)/(1-(88/1935:ℝ)*(1/44)) = 5807/85052 by norm_num] at ht
  linarith [arctan_strictMono (show (5807/85052:ℝ)<1/14 by norm_num)]

private theorem width_bound {l r k : ℝ} (h : r-l < (10/7)*k) (hk : 0 < k) (hlr : l < r)
    {z : ℂ} (hz : 5/7 ≤ z.im) : small34Angle l r z < 2*arctan k := by
  have hy : 0 < z.im := lt_of_lt_of_le (by norm_num) hz
  have hs : (r-l)/(2*z.im) < k := (div_lt_iff₀ (by positivity)).mpr (by
    nlinarith [mul_nonneg (sub_nonneg.mpr hz) hk.le])
  linarith [arctan_strictMono hs,small34Angle_width hlr hy]

private theorem lower_angle {l r c : ℝ} {z : ℂ} (hz : z.im ≤ -(5/7))
    (hp : ∀ w : ℂ, 5/7 ≤ w.im → 0 < small34Angle l r w ∧ small34Angle l r w < c) :
    -c < small34Angle l r z ∧ small34Angle l r z < 0 := by
  have h := hp (conj z) (by simp; linarith)
  rw [small34Angle_conj] at h
  constructor <;> linarith [h.1,h.2]

/-- The argument sums on the three intervals force one lower and three upper
roots, after reflection. The weighted upper and lower bounds are incompatible
with their exact argument sums. -/
theorem small34_quartic_bound (a b : ℂ) (hb : b ≠ 0)
    (bounds : ∀ l₁ r₁ l₂ r₂ l₃ r₃ : ℝ,
      l₁ ∈ Icc (-1.311446) (-1.311445) → r₁ ∈ Icc (-0.096252) (-0.096251) →
      l₂ ∈ Icc (-1.553003) (-1.553002) → r₂ ∈ Icc 1.794300 1.794301 →
      l₃ ∈ Icc (-0.308319) (-0.308318) → r₃ ∈ Icc 2.074717 2.074718 →
      ∀ z : ℂ, 5/7 ≤ z.im →
        let g := 5*small34Angle l₁ r₁ z - 4*small34Angle l₂ r₂ z + 2*small34Angle l₃ r₃ z;
        -π + arctan (1/14) < g ∧ g < arctan (1/44)) :
    ∃ z : ℂ, (family 3 4 a b).eval z = 0 ∧ |z.im| < 5/7 := by
  by_contra! hh
  obtain ⟨u,hm,hu0,hu3,hu,hfac⟩ := small34_roots a b hb hh
  have hne : family 3 4 a b ≠ 0 := ne_zero_of_natDegree_gt
    (show 0 < (family 3 4 a b).natDegree by simp [family_degree 3 4 (by decide) (by decide),hb])
  have hpr : phases u := fun _ _ hl hn => small34Angle_sum hl hn (fun i he => by
    have h := hu i; rw [he,abs_zero] at h; norm_num at h) hfac hne
  obtain ⟨z, hz0, hz2, hz3, hz1abs, hp⟩ : ∃ z : Fin 4 → ℂ,
      (z 0).im ≤ -(5/7) ∧ 5/7 ≤ (z 2).im ∧ 5/7 ≤ (z 3).im ∧ 5/7 ≤ |(z 1).im| ∧ phases z := by
    rcases le_abs.mp (hu 2) with ht | ht
    · exact ⟨u,hu0,ht,hu3,hu 1,hpr⟩
    · refine ⟨fun i => conj (u (Fin.revPerm i)), ?_, ?_, ?_, ?_, reverse_phases hpr⟩
      · change -(u 3).im ≤ -(5/7); linarith
      · change 5/7 ≤ -(u 1).im; linarith [hm (show (1:Fin 4) ≤ 2 by decide)]
      · change 5/7 ≤ -(u 0).im; linarith
      · change 5/7 ≤ |-(u 2).im|; simpa using hu 2
  obtain ⟨l,r,hl,hr,hn⟩ := small34_node1
  obtain ⟨L,R,hL,hR,hN⟩ := small34_node2
  obtain ⟨s,t,hs,ht,hT⟩ := small34_node3
  have hR' : R ∈ Icc 1.794300 1.794301 := by
    rw [show (1.794300 : ℝ) = 1.7943 by norm_num]
    exact hR
  have hbnd := bounds l r L R s t hl hr hL hR' hs ht
  obtain ⟨hl₀,hl₁⟩ := hl
  obtain ⟨hr₀,hr₁⟩ := hr
  obtain ⟨hL₀,hL₁⟩ := hL
  obtain ⟨hR₀,hR₁⟩ := hR
  obtain ⟨hs₀,hs₁⟩ := hs
  obtain ⟨ht₀,ht₁⟩ := ht
  have oddPhase (l r : ℝ) (hl : 2*l+1 < 0) (hr : 0 < 2*r+1) (hn : Small34Node l r) :
      ((∑ i, small34Angle l r (z i) : ℝ) : Angle) = π := by
    rw [hp l r hl.ne hn, Complex.arg_ofReal_of_neg (div_neg_of_pos_of_neg hr hl)]
  have p1 := oddPhase l r (by linarith) (by linarith) hn
  have p2 := oddPhase L R (by linarith) (by linarith) hN
  have p3 := hp s t (by linarith) hT
  rw [Complex.arg_ofReal_of_nonneg (div_nonneg (by linarith) (by linarith))] at p3
  have upper1 (w : ℂ) (hw : 5/7 ≤ w.im) : 0 < small34Angle l r w ∧ small34Angle l r w < π/2 := by
    refine ⟨(small34Angle_pos (by linarith) (by linarith : 0 < w.im)).1, ?_⟩
    have := width_bound (k := 1) (l := l) (r := r) (by linarith) (by norm_num) (by linarith) hw
    rw [arctan_one] at this
    linarith
  have upper3 (w : ℂ) (hw : 5/7 ≤ w.im) : 0 < small34Angle s t w ∧ small34Angle s t w < 2*π/3 := by
    refine ⟨(small34Angle_pos (by linarith) (by linarith : 0 < w.im)).1, ?_⟩
    have hk : (17/10:ℝ) < sqrt 3 := by nlinarith [sq_sqrt (by norm_num : (0:ℝ) ≤ 3),sqrt_nonneg 3]
    have := width_bound (k := sqrt 3) (l := s) (r := t) (by linarith) (by positivity) (by linarith) hw
    rw [arctan_sqrt_three] at this
    linarith
  have hz1 : 5/7 ≤ (z 1).im := by
    rcases le_abs.mp hz1abs with h | h
    · exact h
    have h₀ := lower_angle hz0 upper1
    have h₁ := lower_angle (show (z 1).im ≤ -(5/7) by linarith) upper1
    have h₂ := upper1 _ hz2
    have h₃ := upper1 _ hz3
    rw [Fin.sum_univ_four] at p1
    have he := pin p1 (by linarith [h₀.1,h₁.1,h₂.1,h₃.1]) (by linarith [h₀.2,h₁.2,h₂.2,h₃.2,pi_pos])
    linarith [h₀.2,h₁.2,h₂.2,h₃.2]
  have sum_odd (l r : ℝ) (hlr : l < r)
      (h : ((∑ i, small34Angle l r (z i) : ℝ) : Angle) = π) :
      ∑ i, small34Angle l r (z i) = π := by
    have upp (w : ℂ) (hw : 5/7 ≤ w.im) := small34Angle_pos hlr (show 0 < w.im by linarith)
    have h₀ := lower_angle hz0 upp
    have h₁ := upp _ hz1
    have h₂ := upp _ hz2
    have h₃ := upp _ hz3
    apply pin h <;> rw [Fin.sum_univ_four] <;> linarith [h₀.1,h₀.2,h₁.1,h₁.2,h₂.1,h₂.2,h₃.1,h₃.2]
  have he1 := sum_odd l r (by linarith) p1
  have he2 := sum_odd L R (by linarith) p2
  have he3 : ∑ i, small34Angle s t (z i) = 0 := by
    have h₀ := lower_angle hz0 upper3
    have h₁ := upper3 _ hz1
    have h₂ := upper3 _ hz2
    have h₃ := upper3 _ hz3
    apply pin p3 <;> rw [Fin.sum_univ_four] <;> linarith [h₀.1,h₀.2,h₁.1,h₁.2,h₂.1,h₂.2,h₃.1,h₃.2,pi_pos]
  have h₀ := (hbnd (conj (z 0)) (by simp; linarith)).1
  simp only [small34Angle_conj] at h₀
  have h₁ := (hbnd _ hz1).2
  have h₂ := (hbnd _ hz2).2
  have h₃ := (hbnd _ hz3).2
  rw [Fin.sum_univ_four] at he1 he2 he3
  linarith only [h₀,h₁,h₂,h₃,he1,he2,he3,triple_angle_gap]

end Turan
