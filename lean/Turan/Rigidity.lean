module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Merge
public import Turan.Third

@[expose] public section

noncomputable section
open scoped ComplexConjugate
namespace Turan

private theorem cubic_two_upper (x y v : ℂ) (hr : rootRelation x y v)
    (hx : h ≤ x.im) (hy : h ≤ y.im) (hv : h ≤ |v.im|) : x=W ∧ y=W ∧ v=W := by
  have hh := constants_spec.2.2.2.2.2
  obtain ⟨_, w, _, hw, hrel, hcontact⟩ := lemma_six x y v hr hx hy
  have hvf : v = third w := by
    apply (eq_div_iff (third_den_ne w (hh.trans_le hw))).2
    unfold rootRelation at hrel
    linear_combination hrel
  obtain ⟨_, hbound, heq⟩ := lemma_seven.1 w hw
  have hwW : w=W := heq.mp (le_antisymm hbound (hvf ▸ hv))
  subst w
  have hvW := hvf.trans lemma_seven.2
  rw [hvW] at hcontact ⊢
  have ht : (-1/(4*W)).im < h := by
    have hden : 1 < 4 * (u*u+h*h) := by nlinarith [sq_nonneg u]
    have hx : (-1/(4*W)).im = h / (4 * (u*u+h*h)) := by
      norm_num [Complex.div_im, Complex.normSq_mul, Complex.normSq_apply,
        Complex.mul_re, Complex.mul_im, W]
      ring_nf
      rw [show h^2*16+u^2*16 = 4*(h^2*4+u^2*4) by ring, mul_inv_rev]
      ring
    rw [hx]
    apply (div_lt_iff₀ (by linarith)).2
    nlinarith [mul_pos (show 0 < h by linarith) (sub_pos.mpr hden)]
  obtain ⟨h₁,h₂⟩ := hcontact ht rfl
  exact ⟨h₁,h₂,rfl⟩

private theorem cubic_upper_pair (x y v : ℂ) (hr : rootRelation x y v)
    (hx : h ≤ |x.im|) (hy : h ≤ |y.im|) (hv : h ≤ |v.im|)
    (hp : (h ≤ x.im ∧ h ≤ y.im) ∨ (h ≤ y.im ∧ h ≤ v.im) ∨ (h ≤ v.im ∧ h ≤ x.im)) :
    x=W ∧ y=W ∧ v=W := by
  rcases hp with p | p | p
  · exact cubic_two_upper x y v hr p.1 p.2 hv
  · have hrot : rootRelation y v x := by unfold rootRelation at *; linear_combination hr
    obtain ⟨h₁,h₂,h₃⟩ := cubic_two_upper y v x hrot p.1 p.2 hx
    exact ⟨h₃,h₁,h₂⟩
  · have hrot : rootRelation v x y := by unfold rootRelation at *; linear_combination hr
    obtain ⟨h₁,h₂,h₃⟩ := cubic_two_upper v x y hrot p.1 p.2 hy
    exact ⟨h₂,h₃,h₁⟩

theorem proposition_five (x y v : ℂ) (hr : rootRelation x y v)
    (hx : h ≤ |x.im|) (hy : h ≤ |y.im|) (hv : h ≤ |v.im|) :
    (x = W ∧ y = W ∧ v = W) ∨ (x = conj W ∧ y = conj W ∧ v = conj W) := by
  by_cases hp : (h ≤ x.im ∧ h ≤ y.im) ∨ (h ≤ y.im ∧ h ≤ v.im) ∨ (h ≤ v.im ∧ h ≤ x.im)
  · exact Or.inl (cubic_upper_pair x y v hr hx hy hv hp)
  · right
    have hc : rootRelation (conj x) (conj y) (conj v) := by
      unfold rootRelation at hr ⊢
      simpa [Complex.conj_ofNat] using congrArg (starRingEnd ℂ) hr
    have hp' : (h ≤ (conj x).im ∧ h ≤ (conj y).im) ∨
        (h ≤ (conj y).im ∧ h ≤ (conj v).im) ∨ (h ≤ (conj v).im ∧ h ≤ (conj x).im) := by
      simp only [Complex.conj_im]
      simp only [abs_eq_max_neg, le_max_iff] at hx hy hv
      tauto
    obtain ⟨h₁,h₂,h₃⟩ := cubic_upper_pair (conj x) (conj y) (conj v) hc
      (by simpa using hx) (by simpa using hy) (by simpa using hv) hp'
    exact ⟨by simpa using congrArg (starRingEnd ℂ) h₁,
      by simpa using congrArg (starRingEnd ℂ) h₂, by simpa using congrArg (starRingEnd ℂ) h₃⟩

end Turan
