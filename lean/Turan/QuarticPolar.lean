module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

@[expose] public section

noncomputable section
namespace Turan

/-- The two quadratic factors are indexed by their shifted squares u and v. -/
theorem quartic_shifted_squares_real (u v : ℂ) (huv : u * v = -1 / 2)
    (hu : u.im = 0) :
    v.im = 0 ∧ u.re * v.re < 0 ∧
    (1 / 2 < (u + 1 / 2).re ∨ 1 / 2 < (v + 1 / 2).re) ∧
    ∃ t : ℝ, (t : ℂ) ^ 2 = u + 1 / 2 ∨ (t : ℂ) ^ 2 = v + 1 / 2 := by
  have hr := congrArg Complex.re huv
  have hi := congrArg Complex.im huv
  norm_num [Complex.mul_re, Complex.mul_im, hu] at hr hi
  have hneg : u.re * v.re < 0 := by linarith
  have hv := hi.resolve_left (left_ne_zero_of_mul hneg.ne)
  have pos : 0 < u.re ∨ 0 < v.re := by
    by_contra! hn
    exact hneg.not_ge (mul_nonneg_of_nonpos_of_nonpos hn.1 hn.2)
  have root (z : ℂ) (hz : z.im = 0) (hp : 0 < z.re) :
      ((Real.sqrt (z.re + 1 / 2) : ℝ) : ℂ) ^ 2 = z + 1 / 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]
    apply Complex.ext <;> norm_num [hz]
  refine ⟨hv, hneg, ?_, ?_⟩
  · simpa using pos
  · rcases pos with hp | hp
    · exact ⟨_, Or.inl (root u hu hp)⟩
    · exact ⟨_, Or.inr (root v hv hp)⟩

/-- Both shifted squares use the same choice of conjugation. -/
theorem quartic_shifted_squares_polar (u v : ℂ) (huv : u * v = -1 / 2)
    (hu : u.im ≠ 0) :
    ‖u‖ * ‖v‖ = 1 / 2 ∧ ∃ φ : ℝ, 0 < φ ∧ φ < Real.pi ∧
      let U := (‖u‖ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)
      let V := (‖v‖ : ℂ) * Complex.exp (((Real.pi - φ : ℝ) : ℂ) * Complex.I)
      (u = U ∧ v = V) ∨ (star u = U ∧ star v = V) := by
  have hn : ‖u‖ * ‖v‖ = 1 / 2 := by
    rw [← norm_mul, huv]
    norm_num
  refine ⟨hn, ?_⟩
  obtain ⟨x, hx, hor⟩ : ∃ x : ℂ, 0 < x.im ∧ (x = u ∨ x = star u) := by
    rcases lt_or_gt_of_ne hu with h | h
    · exact ⟨star u, by simpa [Complex.star_def] using neg_pos.mpr h, Or.inr rfl⟩
    · exact ⟨u, h, Or.inl rfl⟩
  have hφ : 0 < x.arg := (Complex.arg_nonneg_iff.mpr hx.le).lt_of_ne
    (fun h => hx.ne' (Complex.arg_eq_zero_iff.mp h.symm).2)
  refine ⟨x.arg, hφ, Complex.arg_lt_pi_iff.mpr (Or.inr hx.ne'), ?_⟩
  let U := (‖u‖ : ℂ) * Complex.exp ((x.arg : ℂ) * Complex.I)
  let V := (‖v‖ : ℂ) * Complex.exp (((Real.pi - x.arg : ℝ) : ℂ) * Complex.I)
  change (u = U ∧ v = V) ∨ (star u = U ∧ star v = V)
  have hU : x = U := by
    have hn' : ‖x‖ = ‖u‖ := by rcases hor with h | h <;> simp [h]
    simpa only [U, hn'] using (Complex.norm_mul_exp_arg_mul_I x).symm
  have hUV : U * V = -1 / 2 := by
    dsimp [U, V]
    rw [mul_mul_mul_comm, ← Complex.ofReal_mul, hn, ← Complex.exp_add,
      ← add_mul, ← Complex.ofReal_add, add_sub_cancel, Complex.exp_pi_mul_I]
    norm_num
  have eqV (y : ℂ) (hy : x * y = -1 / 2) : y = V :=
    mul_left_cancel₀ (fun h : x = 0 => hx.ne' (by simp [h]))
      (hy.trans (hU ▸ hUV).symm)
  rcases hor with h | h
  · exact Or.inl ⟨h ▸ hU, eqV v (h ▸ huv)⟩
  · refine Or.inr ⟨h ▸ hU, eqV (star v) ?_⟩
    rw [h, ← star_mul', huv]
    norm_num

#print axioms quartic_shifted_squares_real
#print axioms quartic_shifted_squares_polar

end Turan
