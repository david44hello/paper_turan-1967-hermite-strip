module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Constants
public import Mathlib.Tactic

@[expose] public section

noncomputable section
namespace Turan

/-- The square root with nonnegative imaginary part preserves an upper
height bound shared by the two factors. At contact the factors agree. -/
private theorem sqrt_product_height (U V S : ℂ) (k : ℝ) (hk : 0 < k)
    (hU : k ≤ U.im) (hV : k ≤ V.im) (hS : 0 ≤ S.im) (he : S^2 = U*V) :
    k ≤ S.im ∧ (S.im = k → U = V) := by
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  simp only [pow_two, Complex.mul_re, Complex.mul_im] at hre him
  have hid : (S.im^2 - U.im*V.im)*(S.re^2 + U.im*V.im) =
      (U.re*V.im-U.im*V.re)^2/4 := by
    linear_combination -U.im*V.im*hre + (2*S.re*S.im+U.re*V.im+U.im*V.re)/4*him
  have hUV := mul_pos (hk.trans_le hU) (hk.trans_le hV)
  have hfac : 0 < S.re^2+U.im*V.im := by positivity
  have hp : 0 ≤ S.im^2 - U.im*V.im := by
    apply nonneg_of_mul_nonneg_left _ hfac
    rw [hid]; positivity
  have hprod : k*k ≤ U.im*V.im := mul_le_mul hU hV hk.le (hk.trans_le hU).le
  refine ⟨by nlinarith, ?_⟩
  intro hcontact
  have hub : U.im = k := by
    by_contra! hne
    have hgt := lt_of_le_of_ne hU (Ne.symm hne)
    have hlt := mul_lt_mul_of_pos_right hgt hk
    have hle := mul_le_mul_of_nonneg_left hV (hk.trans_le hU).le
    nlinarith
  have hvb : V.im = k := by
    rw [hub,hcontact] at hp
    exact le_antisymm ((mul_le_mul_iff_right₀ hk).mp (by nlinarith)) hV
  rw [hub,hvb,hcontact] at hid
  have halign : U.re*k-k*V.re = 0 := by nlinarith [sq_nonneg (U.re*k-k*V.re)]
  apply Complex.ext _ (hub.trans hvb.symm)
  apply (mul_right_cancel₀ hk.ne' : _ * k = _ * k → _)
  linarith

theorem lemma_six (x y v : ℂ)
    (hr : rootRelation x y v) (hx : h ≤ x.im) (hy : h ≤ y.im) :
    v ≠ 0 ∧ ∃ w : ℂ,
      (w - (-1 / (4*v))) ^ 2 = (x - (-1 / (4*v))) * (y - (-1 / (4*v))) ∧
      h ≤ w.im ∧ rootRelation w w v ∧
      ((-1 / (4*v)).im < h → w.im = h → x = w ∧ y = w) := by
  have hh := constants_spec.2.2.2.2.2
  unfold rootRelation at hr ⊢
  have hv : v ≠ 0 := by
    rintro rfl
    have hi := congrArg Complex.im hr
    simp at hi
    linarith
  let τ : ℂ := -1/(4*v)
  have hτ : 4*v*τ + 1 = 0 := by dsimp [τ]; field_simp; norm_num
  obtain ⟨S₀, hs₀⟩ := IsAlgClosed.exists_pow_nat_eq ((x-τ)*(y-τ)) (by decide : 0 < 2)
  obtain ⟨S, hs, hsnonneg⟩ : ∃ S : ℂ, S^2 = (x-τ)*(y-τ) ∧ 0 ≤ S.im := by
    by_cases hn : 0 ≤ S₀.im
    · exact ⟨S₀,hs₀,hn⟩
    · exact ⟨-S₀, by simpa using hs₀, by simpa using (le_of_not_ge hn)⟩
  let w := τ+S
  have hsq : (w-τ)^2 = (x-τ)*(y-τ) := by simpa [w] using hs
  have hrel : 4*w*w*v+w+w+v+1=0 := by
    linear_combination hr + 4*v*hsq + (2*w-x-y)*hτ
  refine ⟨hv, w, hsq, ?_, hrel, ?_⟩
  · by_cases hτh : h ≤ τ.im
    · change h ≤ τ.im+S.im; linarith
    · have hheight := sqrt_product_height (x-τ) (y-τ) S (h-τ.im) (by linarith)
          (by simpa using sub_le_sub_right hx τ.im) (by simpa using sub_le_sub_right hy τ.im) hsnonneg hs
      change h ≤ τ.im+S.im
      linarith [hheight.1]
  · intro hτh hw
    have hheight := sqrt_product_height (x-τ) (y-τ) S (h-τ.im) (by linarith)
      (by simpa using sub_le_sub_right hx τ.im) (by simpa using sub_le_sub_right hy τ.im) hsnonneg hs
    change τ.im+S.im=h at hw
    change τ.im<h at hτh
    have hsame := hheight.2 (by linarith)
    have hxy : x = y := by linear_combination hsame
    subst y
    rw [← sq] at hsq
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hsame | hopp
    · have eq : w = x := by linear_combination hsame
      exact ⟨eq.symm,eq.symm⟩
    · have hi := congrArg Complex.im hopp
      simp only [Complex.sub_im, Complex.neg_im] at hi
      change τ.im + S.im - τ.im = _ at hi
      exfalso; linarith

end Turan
