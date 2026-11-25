-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.QuarticPositionBalanced
import Turan.QuarticPositionMotion
import Turan.QuarticPencil

noncomputable section
open scoped ComplexConjugate
namespace Turan
open QuarticPosition

private theorem repeated_parameters {w a b p r s : ℂ} {y : ℝ}
    (hw : 0<w.im ∧ 12*w^4+16*w^3+12*w^2-3=0) (hy : w.im ≤ y)
    (hb : b ≠ 0) (hf : Factors a b p p r s) (hp : p.im=y) (hr : r.im=y) :
    a=(12-24*w^2)*(64*w^3)⁻¹ ∧ b=(64*w^3)⁻¹ := by
  let d := r.re-p.re
  have er : r=p+(d:ℂ) := by apply Complex.ext <;> simp [d,hr,hp]
  have es : s= -3*p-(d:ℂ) := by
    have hs := roots_sum hb hf
    rw [er] at hs
    linear_combination hs
  let c₂ := -6*p^2-4*p*(d:ℂ)-(d:ℂ)^2
  let c₁ := 8*p^3+8*p^2*(d:ℂ)+2*p*(d:ℂ)^2
  let c₀ := -3*p^4-4*p^3*(d:ℂ)-p^2*(d:ℂ)^2
  have hfac (z : ℂ) : model a b z = 16*b*(z^4+0*z^3+c₂*z^2+c₁*z+c₀) := by
    rw [hf z,er,es]; dsimp only [c₂,c₁,c₀]; ring
  have hcon := (constraint hb hfac).1
  dsimp only [c₂,c₁,c₀] at hcon
  have he : (2*p+(d:ℂ))^2*(4*p^2+4*p+2)-(4*p^4-4*p^2+3)=0 := by
    linear_combination -hcon
  have hd : d=0 := by
    by_contra hn
    exact lemma_eighteen w hw d hn p (hp.symm ▸ hy) he
  have he' : 12*p^4+16*p^3+12*p^2-3=0 := by rw [hd] at he; push_cast at he; linear_combination he
  have ep : p=w := quartic_upper_root.unique ⟨by linarith [hw.1], he'⟩ hw
  obtain ⟨_,h2,h1,_⟩ := coefficients hfac
  simp only [c₂,c₁,hd,Complex.ofReal_zero,mul_zero,sub_zero,add_zero,zero_pow (by decide : 2≠0),ep] at h2 h1
  have hb' : b=(64*w^3)⁻¹ := by apply eq_inv_of_mul_eq_one_left; linear_combination h1/2
  refine ⟨?_,hb'⟩
  rw [← hb']
  linear_combination -h2/4

private theorem oriented_parameters {w a b p q r s : ℂ} {y : ℝ}
    (hw : 0<w.im ∧ 12*w^4+16*w^3+12*w^2-3=0) (hy : w.im ≤ y)
    (hb : b ≠ 0) (hmax : ∀ c d : ℂ, ∃ z : ℂ, (family 2 4 c d).eval z=0 ∧ |z.im|≤y)
    (hf : Factors a b p q r s) (hp : p.im=y) (hq : |q.im|=y) (hr : |r.im|=y) :
    a=(12-24*w^2)*(64*w^3)⁻¹ ∧ b=(64*w^3)⁻¹ := by
  have hy₀ := hw.1.trans_le hy
  have hy₁ : 4/5 < y := by linarith [(quartic_root_height w hw).1]
  have hi := congrArg Complex.im (roots_sum hb hf)
  simp only [Complex.add_im,Complex.zero_im] at hi
  have side (t : ℝ) (h : |t|=y) : t=y ∨ t= -y := by
    rcases le_or_gt 0 t with ht|ht
    · exact Or.inl ((abs_of_nonneg ht).symm.trans h)
    · exact Or.inr (by rw [abs_of_neg ht] at h; linarith)
  rcases side _ hq with hq'|hq' <;> rcases side _ hr with hr'|hr'
  · rcases upper_repeat hb hy₀ hmax hf hp hq' hr' with eq|eq|eq
    · subst q; exact repeated_parameters hw hy hb hf hp hr'
    · subst r; exact repeated_parameters (s:=s) hw hy hb (fun z => by rw [hf z]; ring) hp hq'
    · subst r; exact repeated_parameters (s:=s) hw hy hb (fun z => by rw [hf z]; ring) hq' hp
  · exact (balanced_impossible hb hy₁ hf hp hq' hr' (by linarith)).elim
  · exact (balanced_impossible (a:=a) (s:=s) hb hy₁ (fun z => by rw [hf z]; ring)
      hp hr' hq' (by linarith)).elim
  · exact (balanced_impossible (a:=a) (q:=s) hb hy₁ (fun z => by rw [hf z]; ring)
      hp (by linarith) hq' hr').elim

/-- Three contacts at maximal height determine the quartic parameters up to conjugation. -/
theorem quartic_contact_parameters (w a b : ℂ)
    (hw : 0<w.im ∧ 12*w^4+16*w^3+12*w^2-3=0)
    (y : ℝ) (hy : w.im≤y) (hb : b ≠ 0)
    (hbound : ∀ z : ℂ, (family 2 4 a b).eval z=0 → y≤|z.im|)
    (hmax : ∀ c d : ℂ, ∃ z : ℂ, (family 2 4 c d).eval z=0 ∧ |z.im|≤y)
    (hcnt : 3 ≤ ((family 2 4 a b).roots.filter (fun z => |z.im|=y)).card) :
    (a=(12-24*w^2)*(64*w^3)⁻¹ ∧ b=(64*w^3)⁻¹) ∨
    (a=conj ((12-24*w^2)*(64*w^3)⁻¹) ∧ b=conj ((64*w^3)⁻¹)) := by
  -- The zero sum already determines the fourth imaginary part from the three contacts.
  clear hbound
  obtain ⟨p,q,r,s,hf,hp,hq,hr⟩ := three_contacts a b hb y hcnt
  rcases le_or_gt 0 p.im with h|h
  · exact Or.inl (oriented_parameters hw hy hb hmax hf ((abs_of_nonneg h).symm.trans hp) hq hr)
  · have e := oriented_parameters hw hy (show conj b ≠ 0 by simpa using hb)
      hmax (factors_conj hf) (by simpa [abs_of_neg h] using hp) (by simpa using hq) (by simpa using hr)
    exact Or.inr ⟨by simpa only [Complex.conj_conj] using congrArg conj e.1,
      by simpa only [Complex.conj_conj] using congrArg conj e.2⟩

#print axioms quartic_contact_parameters

end Turan
