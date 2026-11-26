module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TailLinesHermite
public import Turan.TailLinesBounds

@[expose] public section

noncomputable section
namespace Turan
open TailLines

/-- Eliminate the affine part and the other Hermite mode, then bound the
remaining mode. The roles of the two indices may be exchanged. -/
private theorem tail_line_mode {j k : ℕ} {z f u v A B : ℂ} {W gap : ℝ}
    (hj : 225 ≤ j) (hk : 225 ≤ k) (hz : |z.im| = 7/11)
    (hf : f ≠ 0) (hF : f = 1+2*z+u+v)
    (hA : A*f = -2*z - j*u - k*v) (hB : B*f = 2*z + (j:ℂ)^2*u + (k:ℂ)^2*v)
    (hlarge : 900 ≤ W^2) (hkW : (k:ℝ) ≤ W^2/2)
    (hAn : ‖A‖ ≤ 64*W^2) (hBn : ‖B‖ ≤ 4035*W^4)
    (hgap : ‖(k:ℂ)-j‖ = gap) (hg : 0 < gap) :
    ‖u/f‖ ≤ 4200*W^4/((j:ℝ)*gap) := by
  obtain ⟨q, h1q, hq, hcancel⟩ := affine_quotient hj hk hz
  have hj0 : 0 < (j:ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hjc : (j:ℂ) ≠ 0 := by exact_mod_cast hj0.ne'
  have hqj := div_mul_cancel₀ q hjc
  have ident : (1-q)*(A+k) - q/j*(B+k*A) = ((k:ℂ)-j)*(u/f) := by
    calc
      _ = ((1-q)*(A*f+k*f) - q/j*(B*f+k*(A*f)))/f := by field_simp [hf]
      _ = (((k:ℂ)-j)*u)/f := by
        congr 1
        rw [hA, hB, hF]
        linear_combination hcancel + ((k:ℂ)-j)*u*hqj
      _ = _ := by ring
  have hAk : ‖A+(k:ℂ)‖ ≤ 64.5*W^2 := by
    have h := norm_add_le A (k:ℂ)
    simp only [Complex.norm_natCast] at h
    linarith
  have hBk : ‖B+(k:ℂ)*A‖ ≤ 4067*W^4 := by
    calc
      _ ≤ ‖B‖ + ‖(k:ℂ)*A‖ := norm_add_le _ _
      _ = ‖B‖ + (k:ℝ)*‖A‖ := by rw [norm_mul, Complex.norm_natCast]
      _ ≤ 4035*W^4 + (W^2/2)*(64*W^2) := by gcongr
      _ = _ := by ring
  have hqdiv : ‖q/(j:ℂ)‖ ≤ (46/45)/(j:ℝ) := by
    rw [norm_div, Complex.norm_natCast]
    gcongr
  apply (le_div_iff₀ (mul_pos hj0 hg)).mpr
  calc
    _ = (j:ℝ)*(gap*‖u/f‖) := by ring
    _ = (j:ℝ)*‖(1-q)*(A+k) - q/j*(B+k*A)‖ := by rw [ident, norm_mul, hgap]
    _ ≤ (j:ℝ)*(‖(1-q)*(A+k)‖ + ‖q/j*(B+k*A)‖) := by
      gcongr
      exact norm_sub_le _ _
    _ = (j:ℝ)*(‖1-q‖*‖A+k‖ + ‖q/j‖*‖B+k*A‖) := by simp only [norm_mul]
    _ ≤ (j:ℝ)*((5/j)*(64.5*W^2) + ((46/45)/j)*(4067*W^4)) := by gcongr
    _ = 322.5*W^2 + (46/45)*4067*W^4 := by field_simp; ring
    _ ≤ _ := by
      nlinarith only [mul_nonneg (sq_nonneg W) (sub_nonneg.mpr hlarge), sq_nonneg (W^2)]

theorem lemma_fifteen_of_derivative_bounds (n m : ℕ) (hm : 450 ≤ m)
    (hhalf : m ≤ 2*n) (hnm : n < m) (a b : ℂ)
    (hs : emptyStrip (normalizedFamily n m a b) (87/100))
    (hderiv : ∀ (z : ℂ), |z.im| ≤ 7/11 → ∀ (l : ℕ), 1 ≤ l → l ≤ 4 →
      ‖iteratedDeriv l (normalizedFamily n m a b) z / normalizedFamily n m a b z‖ ≤
        (11 * omega m z)^l)
    (j : ℕ) (hj : j = n ∨ j = m) (z : ℂ) (hz : |z.im| = 7/11) :
    ‖modeQuotient n m j a b z‖ ≤ 4200 * (omega m z)^4 / ((j:ℝ)*(m-n:ℝ)) := by
  let f := normalizedFamily n m a b z
  let d := fun l => iteratedDeriv l (normalizedFamily n m a b) z / f
  let A := d 2/2 - z*d 1
  let B := d 4/4 - z*d 3 + (z^2-1)*d 2 + z*d 1
  let u := a * psi n z
  let v := b * psi m z
  have hf : f ≠ 0 := hs z (by rw [hz]; norm_num)
  have hF : f = 1+2*z+u+v := rfl
  obtain ⟨hlarge, hmW, hzW⟩ := omega_bounds hm hz
  obtain ⟨hAn, hBn⟩ := jet_bounds (Real.sqrt_nonneg _) hlarge hzW d (hderiv z hz.le)
  obtain ⟨h1, h2⟩ := family_jets n m a b z
  have hA : A*f = -2*z - n*u - m*v := by
    dsimp only [A, d]
    convert h1 using 1
    field_simp [hf]
  have hB : B*f = 2*z + (n:ℂ)^2*u + (m:ℂ)^2*v := by
    dsimp only [B, d]
    convert h2 using 1
    field_simp [hf]
  have hn : 225 ≤ n := by omega
  have hm' : 225 ≤ m := by omega
  have hnm' : (n:ℝ) < m := by exact_mod_cast hnm
  have hg : 0 < (m:ℝ)-n := sub_pos.mpr hnm'
  have hgap : ‖(m:ℂ)-n‖ = (m:ℝ)-n := by
    change ‖((m:ℝ):ℂ)-((n:ℝ):ℂ)‖ = _
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg]
  rcases hj with rfl | rfl
  · simpa [modeQuotient, f, u] using
      tail_line_mode hn hm' hz hf hF hA hB hlarge hmW hAn hBn hgap hg
  · simpa [modeQuotient, hnm.ne', f, v] using
      tail_line_mode (u := v) (v := u) (f := f) (A := A) (B := B) hm' hn hz hf
        (by rw [hF]; ring) (by rw [hA]; ring) (by rw [hB]; ring)
        hlarge (hnm'.le.trans hmW) hAn hBn (by rw [norm_sub_rev]; exact hgap) hg

end Turan
