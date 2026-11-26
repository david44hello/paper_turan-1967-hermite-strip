module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Volterra
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

open Set
namespace Turan

/-- If the solution has no interior zero, the Wronskian mean value theorem
gives a point where the potential is at most the comparison frequency squared.
Equality at that point forces both endpoint values to vanish. -/
private theorem sturm_of_no_zero {y v Q : ℝ → ℝ} {a k : ℝ} (hk : 0 < k)
    (hy : ∀ t ∈ Icc a (a + Real.pi / k), HasDerivAt y (v t) t)
    (hv : ∀ t ∈ Icc a (a + Real.pi / k), HasDerivAt v (-Q t * y t) t)
    (hn : ∀ t ∈ Ioo a (a + Real.pi / k), y t ≠ 0) :
    ∃ c ∈ Ioo a (a + Real.pi / k), Q c ≤ k ^ 2 ∧
      (Q c = k ^ 2 → y a = 0 ∧ y (a + Real.pi / k) = 0) := by
  let b := a + Real.pi / k
  have hab : a < b := lt_add_of_pos_right _ (div_pos Real.pi_pos hk)
  have hyc : ContinuousOn y (Icc a b) := fun t ht => (hy t ht).continuousAt.continuousWithinAt
  obtain ⟨s, hs, hpos⟩ : ∃ s : ℝ, s ≠ 0 ∧ ∀ t ∈ Ioo a b, 0 < s * y t := by
    rcases isPreconnected_Ioo.mapsTo_Ioi_or_Iio (hyc.mono Ioo_subset_Icc_self) hn with h | h
    · exact ⟨1, one_ne_zero, fun t ht => by simpa using h ht⟩
    · exact ⟨-1, by norm_num, fun t ht => by simpa using neg_pos.mpr (show y t < 0 from h ht)⟩
  have hclosed (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ s * y t := by
    apply le_on_closure (f := fun _ => 0) (g := fun r => s * y r)
      (fun r hr => (hpos r hr).le) continuousOn_const
    · rw [closure_Ioo hab.ne]
      exact continuousOn_const.mul hyc
    · rwa [closure_Ioo hab.ne]
  let θ (t : ℝ) := k * (t - a)
  have hθ (t : ℝ) : HasDerivAt θ k t := by
    simpa [θ] using ((hasDerivAt_id t).sub_const a).const_mul k
  have hθb : θ b = Real.pi := by dsimp [θ, b]; field_simp; ring
  let W (t : ℝ) := (s * y t) * (k * Real.cos (θ t)) - (s * v t) * Real.sin (θ t)
  let W' (t : ℝ) := (Q t - k ^ 2) * (s * y t * Real.sin (θ t))
  have hW (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt W (W' t) t := by
    convert (((hy t ht).const_mul s).mul ((hθ t).cos.const_mul k)).sub
      (((hv t ht).const_mul s).mul (hθ t).sin) using 1
    dsimp [W']
    ring
  obtain ⟨c, hc, hm⟩ := exists_hasDerivAt_eq_slope W W' hab
    (fun t ht => (hW t ht).continuousAt.continuousWithinAt)
    (fun t ht => hW t (Ioo_subset_Icc_self ht))
  have hsin : 0 < Real.sin (θ c) := by
    apply Real.sin_pos_of_pos_of_lt_pi (mul_pos hk (sub_pos.mpr hc.1))
    rw [← hθb]
    exact mul_lt_mul_of_pos_left (sub_lt_sub_right hc.2 a) hk
  have hfactor := mul_pos (hpos c hc) hsin
  have ha := hclosed a (left_mem_Icc.mpr hab.le)
  have hb := hclosed b (right_mem_Icc.mpr hab.le)
  have hWa : W a = k * (s * y a) := by simp [W, θ, mul_comm]
  have hWb : W b = -(k * (s * y b)) := by simp [W, hθb]; ring
  rw [hWa, hWb, eq_div_iff (sub_ne_zero.mpr hab.ne')] at hm
  change ((Q c - k ^ 2) * (s * y c * Real.sin (θ c))) * (b - a) = _ at hm
  have hsum : (Q c - k ^ 2) * ((s * y c * Real.sin (θ c)) * (b - a)) =
      -(k * (s * y a + s * y b)) := by linear_combination hm
  have hfactor' := mul_pos hfactor (sub_pos.mpr hab)
  refine ⟨c, hc, ?_, ?_⟩
  · by_contra! h
    have hp := mul_pos (sub_pos.mpr h) hfactor'
    rw [hsum] at hp
    linarith [mul_nonneg hk.le (add_nonneg ha hb)]
  · intro he
    rw [he, sub_self, zero_mul, eq_neg_iff_add_eq_zero] at hsum
    have hz : s * y a + s * y b = 0 := by
      exact (mul_eq_zero.mp (by linarith : k * (s * y a + s * y b) = 0)).resolve_left hk.ne'
    exact ⟨(mul_eq_zero.mp (by linarith : s * y a = 0)).resolve_left hs,
      (mul_eq_zero.mp (by linarith : s * y b = 0)).resolve_left hs⟩

theorem sturm_interval {y v Q : ℝ → ℝ} {a k : ℝ} (hk : 0 < k)
    (hy : ∀ t ∈ Icc a (a + Real.pi / k), HasDerivAt y (v t) t)
    (hv : ∀ t ∈ Icc a (a + Real.pi / k), HasDerivAt v (-Q t * y t) t)
    (hQ : ∀ t ∈ Ioo a (a + Real.pi / k), k ^ 2 < Q t) :
    ∃ t ∈ Ioo a (a + Real.pi / k), y t = 0 := by
  by_contra! hn
  obtain ⟨c, hc, hle, _⟩ := sturm_of_no_zero hk hy hv hn
  exact (hQ c hc).not_ge hle

theorem sturm_closed_interval {y v Q : ℝ → ℝ} {a k : ℝ} (hk : 0 < k)
    (hy : ∀ t ∈ Icc a (a + Real.pi / k), HasDerivAt y (v t) t)
    (hv : ∀ t ∈ Icc a (a + Real.pi / k), HasDerivAt v (-Q t * y t) t)
    (hQ : ∀ t ∈ Ioo a (a + Real.pi / k), k ^ 2 ≤ Q t) :
    (∃ t ∈ Ioo a (a + Real.pi / k), y t = 0) ∨
      (y a = 0 ∧ y (a + Real.pi / k) = 0) := by
  by_cases hz : ∃ t ∈ Ioo a (a + Real.pi / k), y t = 0
  · exact Or.inl hz
  · push Not at hz
    obtain ⟨c, hc, hle, heq⟩ := sturm_of_no_zero hk hy hv hz
    exact Or.inr (heq (hle.antisymm (hQ c hc)))

theorem hermite_sturm_interval (j : ℕ) (a k : ℝ) (hk : 0 < k)
    (hQ : ∀ t ∈ Ioo a (a + Real.pi / k), k ^ 2 < 2 * (j : ℝ) + 1 - t ^ 2) :
    ∃ t ∈ Ioo a (a + Real.pi / k), psi j (t : ℂ) = 0 := by
  obtain ⟨h₁, h₂⟩ := phi_equation j
  have hv (t : ℝ) : HasDerivAt (fun x : ℝ => (deriv (phi j) x).re)
      (-(2 * (j : ℝ) + 1 - t ^ 2) * (phi j t).re) t := by
    have hcoeff : (t : ℂ) ^ 2 - (2 * (j : ℂ) + 1) = ((-(2 * (j : ℝ) + 1 - t ^ 2) : ℝ) : ℂ) := by
      push_cast
      ring
    simpa only [hcoeff, Complex.re_ofReal_mul] using (h₂ t).real_of_complex
  obtain ⟨t, ht, hzero⟩ := sturm_interval (y := fun t : ℝ => (phi j t).re)
    (v := fun t : ℝ => (deriv (phi j) t).re) hk
    (fun t _ => (h₁ t).real_of_complex) (fun t _ => hv t) hQ
  refine ⟨t, ht, Complex.ext ?_ ?_⟩
  · have hgauss : Complex.exp (-(t : ℂ) ^ 2 / 2) = (Real.exp (-t ^ 2 / 2) : ℂ) := by
      simp [Complex.ofReal_exp]
    change (Complex.exp (-(t : ℂ) ^ 2 / 2) * psi j t).re = 0 at hzero
    rw [hgauss, Complex.re_ofReal_mul] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (Real.exp_pos _).ne'
  · have him : ((hermite j).eval (t : ℂ)).im = 0 := by
      apply Complex.conj_eq_iff_im.mp
      simpa using (hermite_symmetry j (t : ℂ)).1.symm
    simp only [psi, Complex.div_ofReal_im, him, zero_div, Complex.zero_im]

end Turan
