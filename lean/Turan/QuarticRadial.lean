module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.QuarticEscape
public import Turan.QuarticPolar

@[expose] public section

noncomputable section
open Polynomial
namespace Turan

/-- The positive radial threshold in Lemma 19(ii), for y > 0 and 0 < θ < π. -/
def quarticRadialThreshold (y θ : ℝ) : ℝ :=
  2 * y * (y * Real.cos θ + Real.sqrt (y ^ 2 + (1 / 2) * Real.sin θ ^ 2)) /
    Real.sin θ ^ 2

private theorem radial_discriminant (y θ : ℝ) :
    Real.sqrt (y ^ 2 + (1 / 2) * Real.sin θ ^ 2) ^ 2 - (y * Real.cos θ) ^ 2 =
      (y ^ 2 + 1 / 2) * Real.sin θ ^ 2 := by
  rw [Real.sq_sqrt (by positivity)]
  linear_combination -y ^ 2 * Real.sin_sq_add_cos_sq θ

/-- Apply at either angle to a square root of the corresponding X. -/
theorem quartic_shifted_square_radial_bound (z : ℂ) (y ρ θ : ℝ)
    (hy : 0 < y) (hz : y ≤ |z.im|) (hρ : 0 ≤ ρ) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (hpolar : z ^ 2 - 1 / 2 = (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) :
    0 ≤ ρ ^ 2 * Real.sin θ ^ 2 - 4 * y ^ 2 * ρ * Real.cos θ -
        4 * y ^ 2 * (y ^ 2 + 1 / 2) ∧
    0 < quarticRadialThreshold y θ ∧ quarticRadialThreshold y θ ≤ ρ := by
  have hre : z.re ^ 2 - z.im ^ 2 - 1 / 2 = ρ * Real.cos θ := by
    simpa [pow_two, Complex.sub_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re]
      using congrArg Complex.re hpolar
  have him : 2 * z.re * z.im = ρ * Real.sin θ := by
    have h := congrArg Complex.im hpolar
    norm_num [pow_two, Complex.sub_im, Complex.mul_im, Complex.exp_ofReal_mul_I_im] at h
    linarith
  have hzsq : y ^ 2 ≤ z.im ^ 2 := by
    simpa using (sq_le_sq₀ hy.le (abs_nonneg z.im)).2 hz
  have hquad : 0 ≤ ρ ^ 2 * Real.sin θ ^ 2 - 4 * y ^ 2 * ρ * Real.cos θ -
      4 * y ^ 2 * (y ^ 2 + 1 / 2) := by
    calc
      0 ≤ 4 * (z.im ^ 2 - y ^ 2) * (z.re ^ 2 + y ^ 2) := by
        have := sub_nonneg.mpr hzsq
        positivity
      _ = _ := by
        rw [← mul_pow, ← him, mul_assoc (4 * y ^ 2), ← hre]
        ring
  refine ⟨hquad, ?_⟩
  let D := Real.sqrt (y ^ 2 + (1 / 2) * Real.sin θ ^ 2)
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ hπ
  have hd : D ^ 2 - (y * Real.cos θ) ^ 2 = (y ^ 2 + 1 / 2) * Real.sin θ ^ 2 :=
    radial_discriminant y θ
  have hlt : (y * Real.cos θ) ^ 2 < D ^ 2 := by
    linarith only [hd, show 0 < (y ^ 2 + 1 / 2) * Real.sin θ ^ 2 by positivity]
  obtain ⟨hminus, hplus⟩ := abs_lt_of_sq_lt_sq' hlt (Real.sqrt_nonneg _)
  change 0 < 2 * y * (y * Real.cos θ + D) / Real.sin θ ^ 2 ∧
    2 * y * (y * Real.cos θ + D) / Real.sin θ ^ 2 ≤ ρ
  constructor
  · exact div_pos (mul_pos (by positivity) (by linarith)) (by positivity)
  · apply (div_le_iff₀ (by positivity)).2
    have hfac :
        (ρ * Real.sin θ ^ 2 - 2 * y * (y * Real.cos θ + D)) *
          (ρ * Real.sin θ ^ 2 + 2 * y * (D - y * Real.cos θ)) =
        Real.sin θ ^ 2 * (ρ ^ 2 * Real.sin θ ^ 2 - 4 * y ^ 2 * ρ * Real.cos θ -
          4 * y ^ 2 * (y ^ 2 + 1 / 2)) := by
      linear_combination -4 * y ^ 2 * hd
    have hpos : 0 < ρ * Real.sin θ ^ 2 + 2 * y * (D - y * Real.cos θ) :=
      add_pos_of_nonneg_of_pos (by positivity) (mul_pos (by positivity) (sub_pos.mpr hplus))
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_left
      (hfac.symm ▸ mul_nonneg (sq_nonneg _) hquad) hpos)

private theorem radial_threshold_product (y θ : ℝ) (hs : 0 < Real.sin θ) :
    quarticRadialThreshold y θ * quarticRadialThreshold y (Real.pi - θ) =
      4 * y ^ 2 * (y ^ 2 + 1 / 2) / Real.sin θ ^ 2 := by
  have hnum :
      2 * y * (y * Real.cos θ + Real.sqrt (y ^ 2 + (1 / 2) * Real.sin θ ^ 2)) *
      (2 * y * (y * (-Real.cos θ) + Real.sqrt (y ^ 2 + (1 / 2) * Real.sin θ ^ 2))) =
      4 * y ^ 2 * ((y ^ 2 + 1 / 2) * Real.sin θ ^ 2) := by
    linear_combination 4 * y ^ 2 * radial_discriminant y θ
  simp only [quarticRadialThreshold, Real.cos_pi_sub, Real.sin_pi_sub, div_mul_div_comm, hnum]
  field_simp [hs.ne']

/-- The shifted-square factorization used in QuarticEscape, retaining both roots. -/
private theorem radial_pencil_factors (a b : ℂ) (hb : b ≠ 0) :
    ∃ u v : ℂ, u * v = -1 / 2 ∧ ∀ z : ℂ, z ^ 2 - 1 / 2 = u ∨ z ^ 2 - 1 / 2 = v →
      a * (hermite 2).eval z + b * (hermite 4).eval z = 0 := by
  let p : Polynomial ℂ := C (16*b)*X^2+C (4*a-32*b)*X+C (-8*b)
  have hl : 16*b ≠ 0 := mul_ne_zero (by norm_num) hb
  have hd : p.roots.card = 2 :=
    (IsAlgClosed.splits p).natDegree_eq_card_roots.symm.trans (natDegree_quadratic hl)
  obtain ⟨u,v,huv⟩ := Multiset.card_eq_two.mp hd
  have hfac := (IsAlgClosed.splits p).eq_prod_roots
  rw [show p.leadingCoeff=16*b from leadingCoeff_quadratic hl,huv] at hfac
  have hfac' : p=C (16*b)*((X-C u)*(X-C v)) := by simpa using hfac
  refine ⟨u, v, ?_, ?_⟩
  · have he := congrArg (eval 0) hfac'
    simp [p,eval_add,eval_mul,eval_pow,eval_sub] at he
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show (16*b)*(u*v- -1/2)=0 by linear_combination -he)).resolve_left hl
  · intro z hx
    have he : p.eval (z^2-1/2)=0 := by
      rw [hfac']
      rcases hx with hx | hx <;> rw [hx] <;> simp [eval_sub, eval_mul]
    norm_num [p,eval_add,eval_sub,eval_pow,eval_mul] at he
    norm_num [hermite,nsmul_eq_mul,eval_sub,eval_mul]
    linear_combination he

private theorem radial_bound_for_factor (x : ℂ) (y θ : ℝ) (hy : 0 < y)
    (hθ : 0 < θ) (hπ : θ < Real.pi)
    (hheight : ∀ z : ℂ, z ^ 2 - 1 / 2 = x → y ≤ |z.im|)
    (hpolar : x = (‖x‖ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∨
         star x = (‖x‖ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) :
    0 < quarticRadialThreshold y θ ∧ quarticRadialThreshold y θ ≤ ‖x‖ := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x + 1 / 2) (by decide : 0 < 2)
  have he : z ^ 2 - 1 / 2 = x := by linear_combination hz
  have hh := hheight z he
  rcases hpolar with hp | hp
  · exact (quartic_shifted_square_radial_bound z y ‖x‖ θ hy hh (norm_nonneg _) hθ hπ
      (he.trans hp)).2
  · have hc : (starRingEnd ℂ z) ^ 2 - 1 / 2 = star x := by
      simpa [map_ofNat] using congrArg (starRingEnd ℂ) he
    exact (quartic_shifted_square_radial_bound (starRingEnd ℂ z) y ‖x‖ θ hy
      (by simpa using hh) (norm_nonneg _) hθ hπ (hc.trans hp)).2

/-- The least absolute imaginary part among zeros of the homogeneous pencil. -/
theorem quartic_homogeneous_height_sq_bound (a b : ℂ) (hab : a ≠ 0 ∨ b ≠ 0)
    (y : ℝ) (hy : IsLeast {r : ℝ | ∃ z : ℂ,
      a * (hermite 2).eval z + b * (hermite 4).eval z = 0 ∧ |z.im| = r} y) :
    8 * y ^ 4 + 4 * y ^ 2 - 1 ≤ 0 ∧ y ^ 2 ≤ (Real.sqrt 3 - 1) / 4 := by
  obtain ⟨w, _, hw⟩ := hy.1
  have hy₀ : 0 ≤ y := hw ▸ abs_nonneg _
  have hheight (z : ℂ) (hz : a * (hermite 2).eval z + b * (hermite 4).eval z = 0) :
      y ≤ |z.im| := hy.2 ⟨z, hz, rfl⟩
  suffices hpoly : 8 * y ^ 4 + 4 * y ^ 2 - 1 ≤ 0 by
    have hsq : (4 * y ^ 2 + 1) ^ 2 ≤ Real.sqrt 3 ^ 2 := by
      nlinarith only [hpoly, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    have := (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).1 hsq
    exact ⟨hpoly, by linarith⟩
  rcases hy₀.eq_or_lt with h | hpos
  · simp [← h]
  by_cases hb : b = 0
  · have ha : a ≠ 0 := hab.resolve_right (fun h => h hb)
    let t := Real.sqrt 2 / 2
    have ht : a * (hermite 2).eval (t : ℂ) + b * (hermite 4).eval (t : ℂ) = 0 := by
      norm_num [t, hb, ha, hermite, eval_mul, nsmul_eq_mul]
      have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
        exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      linear_combination hs
    have hzero := hheight _ ht
    simp at hzero
    linarith
  obtain ⟨u, v, huv, hroot⟩ := radial_pencil_factors a b hb
  by_cases hu : u.im = 0
  · obtain ⟨_, _, _, t, ht⟩ := quartic_shifted_squares_real u v huv hu
    have hzero := hheight (t : ℂ) (hroot _ (by
      rcases ht with ht | ht
      · left; linear_combination ht
      · right; linear_combination ht))
    simp at hzero
    linarith
  obtain ⟨hnorm, θ, hθ, hπ, hp⟩ := quartic_shifted_squares_polar u v huv hu
  have hu' := radial_bound_for_factor u y θ hpos hθ hπ
    (fun z hz => hheight z (hroot z (Or.inl hz)))
    (hp.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
  have hv' := radial_bound_for_factor v y (Real.pi - θ) hpos (sub_pos.mpr hπ) (by linarith)
    (fun z hz => hheight z (hroot z (Or.inr hz)))
    (hp.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2))
  have hprod := mul_le_mul hu'.2 hv'.2 hv'.1.le (norm_nonneg _)
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ hπ
  rw [radial_threshold_product y θ hs, hnorm] at hprod
  have hclear := (div_le_iff₀ (sq_pos_of_pos hs)).1 hprod
  nlinarith only [hclear, Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)]

#print axioms quarticRadialThreshold
#print axioms quartic_shifted_square_radial_bound
#print axioms quartic_homogeneous_height_sq_bound

end Turan
