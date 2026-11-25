-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.CubicRoots
import Turan.Extremal
import Turan.Rigidity

noncomputable section
open Polynomial
open scoped ComplexConjugate
namespace Turan

theorem cubic_open_strip (a b : ℂ) :
    (∀ z : ℂ, (family 2 3 a b).eval z = 0 → h ≤ |z.im|) ↔
      (a = extremalA ∧ b = extremalB) ∨ (a = conj extremalA ∧ b = conj extremalB) := by
  obtain ⟨_, _, _, heq, h₁, h₂⟩ := extremal_cubics
  constructor
  · intro hout
    have hb : b ≠ 0 := by
      rintro rfl
      obtain ⟨z, hz, hsmall⟩ := cubic_zero_b_half_strip a
      exact (not_lt_of_ge (hout z hz)) (hsmall.trans_lt constants_spec.2.2.2.2.2)
    obtain ⟨x, y, v, hr, hf⟩ := cubic_shifted_factorization a b hb
    have high (r : ℂ) (hmem : r = x ∨ r = y ∨ r = v) : h ≤ |r.im| := by
      have hroot := (cubic_shifted_zero_iff a b x y v hb hf (r - 1/2)).mpr (by simpa using hmem)
      simpa [Complex.sub_im] using hout (r - 1/2) hroot
    have triple (r : ℂ) (hx : x = r) (hy : y = r) (hv : v = r) :
        b = (12*r^2-12*r+9)⁻¹ ∧ a = (3-6*r)*b := by
      obtain ⟨hscale, ha⟩ := cubic_triple_root_coefficients a b r (by
        rw [hf, hx, hy, hv]
        ring)
      exact ⟨eq_inv_of_mul_eq_one_left hscale, ha⟩
    rcases proposition_five x y v hr (high x (.inl rfl)) (high y (.inr (.inl rfl)))
        (high v (.inr (.inr rfl))) with ⟨hx, hy, hv⟩ | ⟨hx, hy, hv⟩
    · obtain ⟨hb', ha⟩ := triple W hx hy hv
      exact Or.inl ⟨by rw [ha, hb']; rfl, hb'⟩
    · obtain ⟨hb', ha⟩ := triple (conj W) hx hy hv
      right
      simp only [extremalA, extremalB, map_mul, map_sub, map_add, map_pow, map_inv₀, map_ofNat]
      exact ⟨by rw [ha, hb'], hb'⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) z hz
    · rw [((heq z).1.mp hz), h₁]
    · rw [((heq z).2.mp hz), h₂]

theorem cubic_closed_strip (a b : ℂ) :
    ∃ z : ℂ, (family 2 3 a b).eval z = 0 ∧ |z.im| ≤ h := by
  by_contra! outside
  obtain ⟨_, _, _, heq, h₁, h₂⟩ := extremal_cubics
  rcases (cubic_open_strip a b).mp (fun z hz => (outside z hz).le) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (not_lt_of_ge h₁.le) (outside _ ((heq _).1.mpr rfl))
  · exact (not_lt_of_ge h₂.le) (outside _ ((heq _).2.mpr rfl))

end Turan
