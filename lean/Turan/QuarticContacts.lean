module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.QuarticContactsAlgebra

@[expose] public section

noncomputable section
open Polynomial Filter
open scoped Topology
namespace Turan
namespace QuarticContacts

/-- Put two noncontacts first, retaining all multiplicities. -/
private theorem order_roots (M : Multiset ℂ) (y : ℝ) (hm : M.card = 4)
    (hh : (M.filter (fun z => |z.im| = y)).card < 3) :
    ∃ r w u v : ℂ, M = {r,w,u,v} ∧ |r.im| ≠ y ∧ |w.im| ≠ y := by
  classical
  let H := M.filter (fun z => |z.im| = y)
  let N := M.filter (fun z => ¬ |z.im| = y)
  have hsplit : H + N = M := Multiset.filter_add_not _ _
  have hcard : H.card + N.card = 4 := by simpa [← hsplit] using hm
  change H.card < 3 at hh
  obtain ⟨r, N₁, h₁, hc₁⟩ := Multiset.card_eq_succ_iff.mp
    (show N.card = (N.card-1)+1 by omega)
  obtain ⟨w, N₂, h₂, hc₂⟩ := Multiset.card_eq_succ_iff.mp
    (show N₁.card = (N₁.card-1)+1 by omega)
  obtain ⟨u, v, huv⟩ := Multiset.card_eq_two.mp
    (show (H + N₂).card = 2 by rw [Multiset.card_add]; omega)
  have hr : r ∈ N := by rw [← h₁]; simp
  have hw : w ∈ N := by rw [← h₁, ← h₂]; simp
  refine ⟨r,w,u,v, ?_, (Multiset.mem_filter.mp hr).2, (Multiset.mem_filter.mp hw).2⟩
  rw [← hsplit, ← h₁, ← h₂, Multiset.add_cons, Multiset.add_cons, huv]
  rfl

private theorem strip_separation (z v : ℂ) (y δ : ℝ)
    (hz : |z.im| ≤ y) (hv : y+δ < |v.im|) : δ < ‖z-v‖ := by
  have htri : |v.im| ≤ |(z-v).im| + |z.im| := by
    simpa [Complex.sub_im, abs_sub_comm v.im z.im] using abs_add_le (v.im-z.im) z.im
  linarith [Complex.abs_im_le_norm (z-v)]

/-- Translating both old roots gives the right linear coefficient for the new
quadratic. The remaining error is constant in z and tends to zero. -/
private theorem residual_clear (s q : ℝ → ℂ) (r w : ℂ) (y : ℝ)
    (hs : ContinuousAt s 1) (hq : ContinuousAt q 1)
    (hs₁ : r+w = -s 1) (hq₁ : q 1 = r*w) (hr : y < |r.im|) (hw : y < |w.im|) :
    ∀ᶠ t in 𝓝 (1 : ℝ), ∀ z : ℂ, z^2+s t*z+q t = 0 → y < |z.im| := by
  obtain ⟨Y, hyY, hY⟩ := exists_between (lt_min hr hw)
  let δ := Y-y
  have hδ : 0 < δ := sub_pos.mpr hyY
  let R := fun t => r-(s t-s 1)/2
  let W := fun t => w-(s t-s 1)/2
  have hR : ContinuousAt R 1 := by dsimp [R]; fun_prop
  have hW : ContinuousAt W 1 := by dsimp [W]; fun_prop
  have hR₁ : R 1 = r := by simp [R]
  have hW₁ : W 1 = w := by simp [W]
  have hRi : ContinuousAt (fun t => |(R t).im|) 1 := by fun_prop
  have hWi : ContinuousAt (fun t => |(W t).im|) 1 := by fun_prop
  have herr : ContinuousAt (fun t => ‖R t*W t-q t‖) 1 := by fun_prop
  have hr' := hRi.tendsto.eventually_const_lt
    (show Y < |(R 1).im| by rw [hR₁]; exact (lt_min_iff.mp hY).1)
  have hw' := hWi.tendsto.eventually_const_lt
    (show Y < |(W 1).im| by rw [hW₁]; exact (lt_min_iff.mp hY).2)
  have he' := herr.tendsto.eventually_lt_const
    (show ‖R 1*W 1-q 1‖ < δ*δ by rw [hR₁, hW₁, hq₁, sub_self, norm_zero]; positivity)
  filter_upwards [hr', hw', he'] with t htR htW htE
  intro z hz
  by_contra! hzstrip
  have hsep (v : ℂ) (hv : Y < |v.im|) : δ < ‖z-v‖ :=
    strip_separation z v y δ hzstrip (by simpa [δ] using hv)
  have heq : (z-R t)*(z-W t) = R t*W t-q t := by
    dsimp [R,W]
    linear_combination hz - z*hs₁
  have hnorm := congrArg norm heq
  rw [norm_mul] at hnorm
  have hprod : δ*δ < ‖z-R t‖*‖z-W t‖ :=
    (mul_lt_mul_of_pos_right (hsep (R t) htR) hδ).trans_le
      (mul_le_mul_of_nonneg_left (hsep (W t) htW).le (norm_nonneg _))
  exact (hprod.trans_eq hnorm).not_gt htE

private theorem move_pair (u v r w : ℂ) (y : ℝ) (hy : 4/5 < y)
    (hu : y ≤ |u.im|) (hv : y ≤ |v.im|) (hr : y < |r.im|) (hw : y < |w.im|)
    (hsum : r+w = -(u+v)) (hc : denom (u+v) (u*v)*(r*w) = numer (u+v) (u*v))
    (hlin : (u+v)*(u*v-r*w) ≠ 0) :
    ∃ a b : ℂ, ∀ z : ℂ, (family 2 4 a b).eval z = 0 → y < |z.im| := by
  let U := fun t : ℝ => (t : ℂ)*u
  let V := fun t : ℝ => (t : ℂ)*v
  let s := fun t => U t + V t
  let p := fun t => U t * V t
  let q := fun t => numer (s t) (p t) / denom (s t) (p t)
  have hs₁ : s 1 = u+v := by simp [s,U,V]
  have hp₁ : p 1 = u*v := by simp [p,U,V]
  have hd : denom (s 1) (p 1) ≠ 0 := hs₁ ▸ hp₁ ▸ denom_ne u v (hy.trans_le hu) (hy.trans_le hv)
  have hq₁ : q 1 = r*w := by
    apply (div_eq_iff hd).2
    rw [hs₁,hp₁,← hc, mul_comm]
  have hs : ContinuousAt s 1 := by dsimp [s,U,V]; fun_prop
  have hp : ContinuousAt p 1 := by dsimp [p,U,V]; fun_prop
  have hn : ContinuousAt (fun t => numer (s t) (p t)) 1 := by unfold numer; fun_prop
  have hD : ContinuousAt (fun t => denom (s t) (p t)) 1 := by unfold denom; fun_prop
  have hq : ContinuousAt q 1 := hn.div hD hd
  have hL : ContinuousAt (fun t => s t*(p t-q t)) 1 := by fun_prop
  have hl := hL.eventually_ne (show s 1*(p 1-q 1) ≠ 0 by simpa [hs₁,hp₁,hq₁] using hlin)
  have hres := residual_clear s q r w y hs hq (hs₁ ▸ hsum) hq₁ hr hw
  have good : ∀ᶠ t in 𝓝[>] (1 : ℝ), 1 < t ∧ denom (s t) (p t) ≠ 0 ∧
      s t*(p t-q t) ≠ 0 ∧ ∀ z : ℂ, z^2+s t*z+q t = 0 → y < |z.im| := by
    filter_upwards [self_mem_nhdsWithin, (hD.eventually_ne hd).filter_mono nhdsWithin_le_nhds,
      hl.filter_mono nhdsWithin_le_nhds, hres.filter_mono nhdsWithin_le_nhds] with t ht h₁ h₂ h₃
    exact ⟨ht,h₁,h₂,h₃⟩
  obtain ⟨t, ht, hdt, hlt, hqt⟩ := good.exists
  have hct : denom (s t) (p t)*q t = numer (s t) (p t) := by
    dsimp only [q]
    field_simp
  obtain ⟨a,b,hb,he⟩ := realize (U t) (V t) (q t) hct hlt
  refine ⟨a,b,?_⟩
  intro z hz
  rw [he] at hz
  have raise (x : ℂ) (hx : y ≤ |x.im|) : y < |((t : ℂ)*x).im| := by
    simp [Complex.mul_im, abs_mul, abs_of_pos (show 0<t by linarith)]
    nlinarith [mul_pos (sub_pos.mpr ht) (show 0 < |x.im| by linarith)]
  rcases (by simpa [mul_eq_zero, hb, sub_eq_zero, or_assoc] using hz :
    z = U t ∨ z = V t ∨ z^2+s t*z+q t = 0) with h | h | h
  · exact h ▸ raise u hu
  · exact h ▸ raise v hv
  · exact hqt z h

end QuarticContacts

/-- Appendix A.3, Lemma 19(iv). At least three roots of a maximizing quartic
lie on the boundary of its root-free strip, counted with multiplicity. -/
theorem quartic_three_contacts (a b : ℂ) (y : ℝ) (hy : 4/5 < y) (hb : b ≠ 0)
    (hbound : ∀ z : ℂ, (family 2 4 a b).eval z = 0 → y ≤ |z.im|)
    (hmax : ∀ c d : ℂ, ∃ z : ℂ, (family 2 4 c d).eval z = 0 ∧ |z.im| ≤ y) :
    3 ≤ (((family 2 4 a b).roots.filter (fun z => |z.im| = y)).card) := by
  classical
  by_contra! hfew
  let F := family 2 4 a b
  have hd : F.natDegree = 4 := by simp [F, family_degree 2 4 (by decide) (by decide), hb]
  have hcard := (IsAlgClosed.splits F).natDegree_eq_card_roots.symm.trans hd
  obtain ⟨r,w,u,v,hM,hr,hw⟩ := QuarticContacts.order_roots F.roots y hcard hfew
  have bound (x : ℂ) (hx : x ∈ ({r,w,u,v} : Multiset ℂ)) : y ≤ |x.im| := by
    apply hbound
    rw [← hM] at hx
    exact (mem_roots (ne_zero_of_natDegree_gt (n := 0) (by omega : 0 < F.natDegree))).mp hx
  obtain ⟨hs,hc,hl⟩ := QuarticContacts.root_data a b u v r w hb hM
  obtain ⟨c,d,hm⟩ := QuarticContacts.move_pair u v r w y hy
    (bound u (by simp)) (bound v (by simp)) (lt_of_le_of_ne (bound r (by simp)) hr.symm)
    (lt_of_le_of_ne (bound w (by simp)) hw.symm) hs hc hl
  obtain ⟨z,hz,hzy⟩ := hmax c d
  exact (hm z hz).not_ge hzy

#print axioms quartic_three_contacts

end Turan
