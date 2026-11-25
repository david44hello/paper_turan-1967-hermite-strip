-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Small56Algebra

noncomputable section
namespace Turan.Small56

/-- A node and its rational enclosure, in the shifted coordinate. -/
def Node (G D : ℤ) (g d : ℝ) : Prop :=
  |g - (G:ℝ)/1000000| ≤ 2/1000000 ∧ |d - (D:ℝ)/1000000| ≤ 2/1000000 ∧
  ∀ a b : ℂ, (family 5 6 a b).eval ((g:ℂ)-1/2) * d =
    (family 5 6 a b).eval ((d:ℂ)-1/2) * g

private theorem bracket {f : ℝ → ℝ} {l u : ℝ} (hc : Continuous f) (hlu : l ≤ u)
    (hs : f l * f u ≤ 0) : ∃ x ∈ Set.Icc l u, f x = 0 := by
  rcases mul_nonpos_iff.mp hs with h | h
  · exact intermediate_value_Icc' hlu hc.continuousOn h.symm
  · exact intermediate_value_Icc hlu hc.continuousOn h

-- Uniform variation on the isolating intervals of width 10⁻¹⁸.
private theorem nearby {S c : ℝ} (hc : |c| ≤ 3) (hS : |S| ≤ 3)
    (h : |S-c| ≤ 1/10^18) :
    |denominator S - denominator c| ≤ 1/10^12 ∧
    |numerator S - numerator c| ≤ 1/10^12 := by
  have hp (k : ℕ) : |S^k-c^k| ≤ (1/10^18:ℝ)*k*3^(k-1) :=
    (abs_pow_sub_pow_le S c k).trans (by gcongr; exact max_le hS hc)
  have h1 := abs_le.mp h
  have h2 := abs_le.mp (hp 2)
  have h3 := abs_le.mp (hp 3)
  have h4 := abs_le.mp (hp 4)
  have h5 := abs_le.mp (hp 5)
  have h6 := abs_le.mp (hp 6)
  norm_num at h2 h3 h4 h5 h6
  unfold denominator numerator
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

private theorem enclosed_root {S p m : ℝ}
    (h : ((m-2/1000000)^2-S*(m-2/1000000)+p) *
         ((m+2/1000000)^2-S*(m+2/1000000)+p) ≤ 0) :
    ∃ w : ℝ, |w-m| ≤ 2/1000000 ∧ w^2-S*w+p=0 := by
  obtain ⟨w, hw, he⟩ := bracket (f := fun x => x^2-S*x+p) (by fun_prop)
    (show m-2/1000000 ≤ m+2/1000000 by linarith) h
  exact ⟨w, abs_le.mpr ⟨by linarith [hw.1], by linarith [hw.2]⟩, he⟩

-- Rows are oriented according to the signs of the five exponents in Appendix A.3.
theorem nodes1 : ∃ g d : ℝ, Node (-2048845) (-75660) g d := by
  let c : ℝ := -2124504535835401781/10^18
  obtain ⟨S, hS, hT⟩ := bracket (f := eliminant) (l := c) (u := c+1/10^18)
    (by unfold eliminant; fun_prop) (by linarith) (by norm_num [eliminant,c])
  have hsl := hS.1
  have hsu := hS.2
  have hb := nearby (c := c) (S := S) (by norm_num [c])
    (by apply abs_le.mpr; dsimp [c] at *; constructor <;> linarith only [hsl, hsu])
    (by rw [abs_of_nonneg (sub_nonneg.mpr hsl)]; exact (sub_le_iff_le_add).2 (by simpa only [add_comm] using hsu))
  obtain ⟨hd₁,hd₂⟩ := abs_le.mp hb.1
  obtain ⟨hn₁,hn₂⟩ := abs_le.mp hb.2
  norm_num [c, denominator, numerator] at hd₁ hd₂ hn₁ hn₂
  have hD : 0 < denominator S := by unfold denominator; linarith only [hd₁,hd₂]
  have hp : (15501491/10^8:ℝ) ≤ nodeProduct S ∧ nodeProduct S ≤ (15501494/10^8:ℝ) := by
    unfold nodeProduct
    constructor
    · apply (le_div_iff₀ hD).2
      unfold numerator denominator
      linarith only [hd₁,hd₂,hn₁,hn₂]
    · apply (div_le_iff₀ hD).2
      unfold numerator denominator
      linarith only [hd₁,hd₂,hn₁,hn₂]
  change c ≤ S at hsl
  change S ≤ c+1/10^18 at hsu
  dsimp [c] at hsl hsu
  obtain ⟨g, hg, qg⟩ := enclosed_root (S := S) (p := nodeProduct S)
    (m := (-2048845:ℝ)/1000000) (by apply mul_nonpos_of_nonneg_of_nonpos <;> linarith only [hp.1, hp.2, hsl, hsu])
  obtain ⟨d, hd, qd⟩ := enclosed_root (S := S) (p := nodeProduct S)
    (m := (-75660:ℝ)/1000000) (by apply mul_nonpos_of_nonpos_of_nonneg <;> linarith only [hp.1, hp.2, hsl, hsu])
  refine ⟨g, d, ?_, ?_, node_value hT hD.ne' qg qd⟩
  · simpa only [Int.cast_neg, Int.cast_ofNat] using hg
  · simpa only [Int.cast_neg, Int.cast_ofNat] using hd

theorem nodes2 : ∃ g d : ℝ, Node (2907699) (-1805569) g d := by
  let c : ℝ := 1102129937575390874/10^18
  obtain ⟨S, hS, hT⟩ := bracket (f := eliminant) (l := c) (u := c+1/10^18)
    (by unfold eliminant; fun_prop) (by linarith) (by norm_num [eliminant,c])
  have hsl := hS.1
  have hsu := hS.2
  have hb := nearby (c := c) (S := S) (by norm_num [c])
    (by apply abs_le.mpr; dsimp [c] at *; constructor <;> linarith only [hsl, hsu])
    (by rw [abs_of_nonneg (sub_nonneg.mpr hsl)]; exact (sub_le_iff_le_add).2 (by simpa only [add_comm] using hsu))
  obtain ⟨hd₁,hd₂⟩ := abs_le.mp hb.1
  obtain ⟨hn₁,hn₂⟩ := abs_le.mp hb.2
  norm_num [c, denominator, numerator] at hd₁ hd₂ hn₁ hn₂
  have hD : 0 < denominator S := by unfold denominator; linarith only [hd₁,hd₂]
  have hp : (-525005031/10^8:ℝ) ≤ nodeProduct S ∧ nodeProduct S ≤ (-525005028/10^8:ℝ) := by
    unfold nodeProduct
    constructor
    · apply (le_div_iff₀ hD).2
      unfold numerator denominator
      linarith only [hd₁,hd₂,hn₁,hn₂]
    · apply (div_le_iff₀ hD).2
      unfold numerator denominator
      linarith only [hd₁,hd₂,hn₁,hn₂]
  change c ≤ S at hsl
  change S ≤ c+1/10^18 at hsu
  dsimp [c] at hsl hsu
  obtain ⟨g, hg, qg⟩ := enclosed_root (S := S) (p := nodeProduct S)
    (m := (2907699:ℝ)/1000000) (by apply mul_nonpos_of_nonpos_of_nonneg <;> linarith only [hp.1, hp.2, hsl, hsu])
  obtain ⟨d, hd, qd⟩ := enclosed_root (S := S) (p := nodeProduct S)
    (m := (-1805569:ℝ)/1000000) (by apply mul_nonpos_of_nonneg_of_nonpos <;> linarith only [hp.1, hp.2, hsl, hsu])
  refine ⟨g, d, ?_, ?_, node_value hT hD.ne' qg qd⟩
  · simpa only [Int.cast_neg, Int.cast_ofNat] using hg
  · simpa only [Int.cast_neg, Int.cast_ofNat] using hd

theorem nodes3 : ∃ g d : ℝ, Node (2222962) (-626158) g d := by
  let c : ℝ := 1596804296801012811/10^18
  obtain ⟨S, hS, hT⟩ := bracket (f := eliminant) (l := c) (u := c+1/10^18)
    (by unfold eliminant; fun_prop) (by linarith) (by norm_num [eliminant,c])
  have hsl := hS.1
  have hsu := hS.2
  have hb := nearby (c := c) (S := S) (by norm_num [c])
    (by apply abs_le.mpr; dsimp [c] at *; constructor <;> linarith only [hsl, hsu])
    (by rw [abs_of_nonneg (sub_nonneg.mpr hsl)]; exact (sub_le_iff_le_add).2 (by simpa only [add_comm] using hsu))
  obtain ⟨hd₁,hd₂⟩ := abs_le.mp hb.1
  obtain ⟨hn₁,hn₂⟩ := abs_le.mp hb.2
  norm_num [c, denominator, numerator] at hd₁ hd₂ hn₁ hn₂
  have hD : denominator S < 0 := by unfold denominator; linarith only [hd₁,hd₂]
  have hp : (-139192600/10^8:ℝ) ≤ nodeProduct S ∧ nodeProduct S ≤ (-139192597/10^8:ℝ) := by
    unfold nodeProduct
    constructor
    · apply (le_div_iff_of_neg hD).2
      unfold numerator denominator
      linarith only [hd₁,hd₂,hn₁,hn₂]
    · apply (div_le_iff_of_neg hD).2
      unfold numerator denominator
      linarith only [hd₁,hd₂,hn₁,hn₂]
  change c ≤ S at hsl
  change S ≤ c+1/10^18 at hsu
  dsimp [c] at hsl hsu
  obtain ⟨g, hg, qg⟩ := enclosed_root (S := S) (p := nodeProduct S)
    (m := (2222962:ℝ)/1000000) (by apply mul_nonpos_of_nonpos_of_nonneg <;> linarith only [hp.1, hp.2, hsl, hsu])
  obtain ⟨d, hd, qd⟩ := enclosed_root (S := S) (p := nodeProduct S)
    (m := (-626158:ℝ)/1000000) (by apply mul_nonpos_of_nonneg_of_nonpos <;> linarith only [hp.1, hp.2, hsl, hsu])
  refine ⟨g, d, ?_, ?_, node_value hT hD.ne qg qd⟩
  · simpa only [Int.cast_neg, Int.cast_ofNat] using hg
  · simpa only [Int.cast_neg, Int.cast_ofNat] using hd

theorem nodes4 : ∃ g d : ℝ, Node (-555650) (2384521) g d := by
  let c : ℝ := 1828871501724025363/10^18
  obtain ⟨S, hS, hT⟩ := bracket (f := eliminant) (l := c) (u := c+1/10^18)
    (by unfold eliminant; fun_prop) (by linarith) (by norm_num [eliminant,c])
  have hsl := hS.1
  have hsu := hS.2
  have hb := nearby (c := c) (S := S) (by norm_num [c])
    (by apply abs_le.mpr; dsimp [c] at *; constructor <;> linarith only [hsl, hsu])
    (by rw [abs_of_nonneg (sub_nonneg.mpr hsl)]; exact (sub_le_iff_le_add).2 (by simpa only [add_comm] using hsu))
  obtain ⟨hd₁,hd₂⟩ := abs_le.mp hb.1
  obtain ⟨hn₁,hn₂⟩ := abs_le.mp hb.2
  norm_num [c, denominator, numerator] at hd₁ hd₂ hn₁ hn₂
  have hD : denominator S < 0 := by unfold denominator; linarith only [hd₁,hd₂]
  have hp : (-132495844/10^8:ℝ) ≤ nodeProduct S ∧ nodeProduct S ≤ (-132495841/10^8:ℝ) := by
    unfold nodeProduct
    constructor
    · apply (le_div_iff_of_neg hD).2
      unfold numerator denominator
      linarith only [hd₁,hd₂,hn₁,hn₂]
    · apply (div_le_iff_of_neg hD).2
      unfold numerator denominator
      linarith only [hd₁,hd₂,hn₁,hn₂]
  change c ≤ S at hsl
  change S ≤ c+1/10^18 at hsu
  dsimp [c] at hsl hsu
  obtain ⟨g, hg, qg⟩ := enclosed_root (S := S) (p := nodeProduct S)
    (m := (-555650:ℝ)/1000000) (by apply mul_nonpos_of_nonneg_of_nonpos <;> linarith only [hp.1, hp.2, hsl, hsu])
  obtain ⟨d, hd, qd⟩ := enclosed_root (S := S) (p := nodeProduct S)
    (m := (2384521:ℝ)/1000000) (by apply mul_nonpos_of_nonpos_of_nonneg <;> linarith only [hp.1, hp.2, hsl, hsu])
  refine ⟨g, d, ?_, ?_, node_value hT hD.ne qg qd⟩
  · simpa only [Int.cast_neg, Int.cast_ofNat] using hg
  · simpa only [Int.cast_neg, Int.cast_ofNat] using hd

theorem nodes5 : ∃ g d : ℝ, Node (360845) (2327565) g d := by
  let c : ℝ := 2688409977411881745/10^18
  obtain ⟨S, hS, hT⟩ := bracket (f := eliminant) (l := c) (u := c+1/10^18)
    (by unfold eliminant; fun_prop) (by linarith) (by norm_num [eliminant,c])
  have hsl := hS.1
  have hsu := hS.2
  have hb := nearby (c := c) (S := S) (by norm_num [c])
    (by apply abs_le.mpr; dsimp [c] at *; constructor <;> linarith only [hsl, hsu])
    (by rw [abs_of_nonneg (sub_nonneg.mpr hsl)]; exact (sub_le_iff_le_add).2 (by simpa only [add_comm] using hsu))
  obtain ⟨hd₁,hd₂⟩ := abs_le.mp hb.1
  obtain ⟨hn₁,hn₂⟩ := abs_le.mp hb.2
  norm_num [c, denominator, numerator] at hd₁ hd₂ hn₁ hn₂
  have hD : denominator S < 0 := by unfold denominator; linarith only [hd₁,hd₂]
  have hp : (83989048/10^8:ℝ) ≤ nodeProduct S ∧ nodeProduct S ≤ (83989051/10^8:ℝ) := by
    unfold nodeProduct
    constructor
    · apply (le_div_iff_of_neg hD).2
      unfold numerator denominator
      linarith only [hd₁,hd₂,hn₁,hn₂]
    · apply (div_le_iff_of_neg hD).2
      unfold numerator denominator
      linarith only [hd₁,hd₂,hn₁,hn₂]
  change c ≤ S at hsl
  change S ≤ c+1/10^18 at hsu
  dsimp [c] at hsl hsu
  obtain ⟨g, hg, qg⟩ := enclosed_root (S := S) (p := nodeProduct S)
    (m := (360845:ℝ)/1000000) (by apply mul_nonpos_of_nonneg_of_nonpos <;> linarith only [hp.1, hp.2, hsl, hsu])
  obtain ⟨d, hd, qd⟩ := enclosed_root (S := S) (p := nodeProduct S)
    (m := (2327565:ℝ)/1000000) (by apply mul_nonpos_of_nonpos_of_nonneg <;> linarith only [hp.1, hp.2, hsl, hsu])
  refine ⟨g, d, ?_, ?_, node_value hT hD.ne qg qd⟩
  · simpa only [Int.cast_neg, Int.cast_ofNat] using hg
  · simpa only [Int.cast_neg, Int.cast_ofNat] using hd

end Turan.Small56
