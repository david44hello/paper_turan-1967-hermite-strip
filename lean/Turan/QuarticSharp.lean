module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.CubicRoots
public import Turan.QuarticMaximum
public import Turan.QuarticContacts
public import Turan.QuarticPosition
public import Turan.QuarticCandidate

@[expose] public section

noncomputable section
open scoped ComplexConjugate
namespace Turan

private theorem maximizing_params (w a b : ℂ) (hw : 0<w.im ∧ 12*w^4+16*w^3+12*w^2-3=0)
    (y : ℝ) (hy : w.im≤y)
    (hbound : ∀ z : ℂ, (family 2 4 a b).eval z=0 → y≤|z.im|)
    (hmax : ∀ c d : ℂ, ∃ z : ℂ, (family 2 4 c d).eval z=0 ∧ |z.im|≤y) :
    (a=(12-24*w^2)*(64*w^3)⁻¹ ∧ b=(64*w^3)⁻¹) ∨
    (a=conj ((12-24*w^2)*(64*w^3)⁻¹) ∧ b=conj ((64*w^3)⁻¹)) := by
  have hh := (quartic_root_height w hw).1
  have hb : b≠0 := by
    rintro rfl
    obtain ⟨z,hz,hz'⟩ := cubic_zero_b_half_strip a
    have := hbound z (by simpa [family] using hz)
    linarith
  have hcnt := quartic_three_contacts a b y (by linarith) hb hbound hmax
  exact quartic_contact_parameters w a b hw y hy hb hbound hmax hcnt

theorem lemma_nineteen (w : ℂ) (hw : 0 < w.im ∧ 12*w^4+16*w^3+12*w^2-3=0) :
    let b₀ := (64*w^3)⁻¹
    let a₀ := (12-24*w^2)*b₀
    (8286/10000 < w.im ∧ w.im < 8287/10000 ∧ w.im < Real.sqrt 3/2) ∧
    (∀ a b : ℂ, ∃ z : ℂ, (family 2 4 a b).eval z = 0 ∧ |z.im| ≤ w.im) ∧
    (∀ a b : ℂ, (∀ z : ℂ, (family 2 4 a b).eval z = 0 → w.im ≤ |z.im|) ↔
      (a=a₀ ∧ b=b₀) ∨ (a=conj a₀ ∧ b=conj b₀)) ∧
    family 2 4 a₀ b₀ ≠ family 2 4 (conj a₀) (conj b₀) ∧ b₀ ≠ 0 ∧
    (∀ z : ℂ, (family 2 4 a₀ b₀).eval z = 16*b₀*(z-w)^3*(z+3*w) ∧
      (family 2 4 (conj a₀) (conj b₀)).eval z = 16*conj b₀*(z-conj w)^3*(z+3*conj w)) := by
  let b₀ := (64*w^3)⁻¹
  let a₀ := (12-24*w^2)*b₀
  obtain ⟨h₀,hc₀,hroot,hcroot⟩ := quartic_candidate_heights w hw
  obtain ⟨y,A,B,hwy,hbound,hmax⟩ := quartic_height_attained w.im
    (by linarith [(quartic_root_height w hw).1]) a₀ b₀ h₀
  have hmaxheight : y ≤ w.im := by
    rcases maximizing_params w A B hw y hwy hbound hmax with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simpa [abs_of_pos hw.1] using hbound w hroot
    · simpa [abs_of_pos hw.1] using hbound (conj w) hcroot
  have heq : y = w.im := le_antisymm hmaxheight hwy
  subst y
  refine ⟨quartic_root_height w hw,hmax,?_,quartic_candidate w hw⟩
  intro a b
  constructor
  · intro hn
    exact maximizing_params w a b hw w.im le_rfl hn hmax
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · exact h₀
    · exact hc₀

end Turan
