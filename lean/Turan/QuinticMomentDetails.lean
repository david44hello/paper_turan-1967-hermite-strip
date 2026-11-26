module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs
public import Mathlib.Tactic

@[expose] public section

noncomputable section
namespace Turan

/-- Lower bounds for the cleared difference, with the signed cross term. -/
theorem quintic_difference_sqrt_chain (σ x₅ X s : ℝ)
    (hproj : x₅ ^ 2 ≤ 3 + (3 / 5) * σ) (hX : |X| < 1 / 2)
    (hσ : 4 * (87 / 100 : ℝ) ^ 2 ≤ σ) (hs₀ : 1 / 2 < s) (hs₁ : s < 511 / 1000) :
    let D := 10 + 2 * σ - 2 * x₅ ^ 2 + 4 * X * x₅ + 3 * X ^ 2 - 3 * s ^ 2
    let B := 4 + (4 / 5) * σ - 2 * Real.sqrt (3 + (3 / 5) * σ) - 3 * s ^ 2
    let C := 1 / 2 + σ / 2 - 3 * s ^ 2
    B ≤ D ∧ C ≤ B ∧ 0 < C := by
  dsimp only
  let v := 3 + (3/5)*σ
  have hv : 0 ≤ v := (sq_nonneg _).trans hproj
  have hx : |x₅| ≤ Real.sqrt v := by
    rw [← Real.sqrt_sq_eq_abs x₅]; exact Real.sqrt_le_sqrt hproj
  have cross : -(Real.sqrt v/2) ≤ X*x₅ := by
    have hm := mul_le_mul_of_nonneg_right hX.le (abs_nonneg x₅)
    have hn := neg_abs_le (X*x₅)
    rw [abs_mul] at hn
    linarith
  have hs := (sq_lt_sq₀ (by linarith : 0 ≤ s) (by norm_num : (0:ℝ) ≤ 511/1000)).2 hs₁
  change _ ≤ _ ∧ _ ≤ _ ∧ _
  refine ⟨?_,?_,?_⟩
  · dsimp [v] at cross
    nlinarith only [cross,hproj,sq_nonneg X]
  · have hsqrt := sq_nonneg (Real.sqrt v-2)
    have hsqr := Real.sq_sqrt hv
    dsimp [v] at hsqrt hsqr
    nlinarith only [hsqrt,hsqr]
  · linarith only [hs,hσ]

/-- The half-length domain includes the comparison endpoint 0.511. -/
theorem quintic_rectangle_quadratic_monotonicity :
    let g := fun s y : ℝ => s ^ 2 + (56 / 45) * s * y - y ^ 2
    (∀ y : ℝ, 87 / 100 ≤ y → StrictMonoOn (fun s => g s y) (Set.Icc (1 / 2) (511 / 1000))) ∧
      ∀ s ∈ Set.Icc (1 / 2) (511 / 1000), StrictAntiOn (g s) (Set.Ici (87 / 100)) := by
  constructor
  · intro y hy a ha b hb hab
    change a^2+56/45*a*y-y^2 < b^2+56/45*b*y-y^2
    have h := mul_pos (sub_pos.mpr hab) (show 0 < a+b+56/45*y by linarith [ha.1,hb.1])
    nlinarith only [h]
  · intro s hs a ha b hb hab
    change s^2+56/45*s*b-b^2 < s^2+56/45*s*a-a^2
    have h := mul_pos (sub_pos.mpr hab) (show 0 < a+b-56/45*s by
      have ha' : 87/100 ≤ a := ha
      have hb' : 87/100 ≤ b := hb
      linarith [hs.2])
    nlinarith only [h]

private theorem square_bounds_detail (w : ℂ) (A B : ℝ) (hx : |w.re| < A) (hy : |w.im| < B) :
    (w^2).re < A^2 ∧ |(w^2).im| < 2*A*B := by
  have hx2 := (sq_lt_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hx.le)).2 hx
  rw [sq_abs] at hx2
  have hxy := mul_lt_mul_of_nonneg hx hy (abs_nonneg _) (abs_nonneg _)
  constructor
  · simp only [pow_two, Complex.mul_re]
    nlinarith only [hx2, sq_nonneg w.im]
  · rw [show (w^2).im = 2*(w.re*w.im) by simp [pow_two, Complex.mul_im]; ring,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul]
    linarith only [hxy]

/-- Strict real margin and the division step for vertical separation. -/
theorem quintic_discriminant_sqrt_separation (z : Fin 5 → ℂ)
    (hz : ∑ i, z i = 0) (hz2 : ∑ i, (z i) ^ 2 = 10)
    (hrect : ∀ i : Fin 5, i < 3 →
      |(z i).re| < 4 / 5 ∧ 87 / 100 ≤ (z i).im ∧ (z i).im < 1) :
    let w := z 3 - z 4
    let Δ := w ^ 2
    52 / 5 < Δ.re ∧ Δ.re ≤ w.re ^ 2 ∧ Real.sqrt 10 < |w.re| ∧
      |w.im| = |Δ.im| / (2 * |w.re|) ∧
      |Δ.im| / (2 * |w.re|) < 24 / (2 * Real.sqrt 10) ∧ 24 / (2 * Real.sqrt 10) < 4 := by
  let a := z 0
  let b := z 1
  let c := z 2
  let u := z 3
  let v := z 4
  obtain ⟨har,hai,haj⟩ := hrect 0 (by decide)
  obtain ⟨hbr,hbi,hbj⟩ := hrect 1 (by decide)
  obtain ⟨hcr,hci,hcj⟩ := hrect 2 (by decide)
  have ha' : |a.im| < 1 := by
    rw [abs_of_nonneg (show 0 ≤ a.im by dsimp [a]; linarith)]
    exact haj
  have hb' : |b.im| < 1 := by
    rw [abs_of_nonneg (show 0 ≤ b.im by dsimp [b]; linarith)]
    exact hbj
  have hc' : |c.im| < 1 := by
    rw [abs_of_nonneg (show 0 ≤ c.im by dsimp [c]; linarith)]
    exact hcj
  have hz' : a+b+c+u+v = 0 := by simpa [a,b,c,u,v,Fin.sum_univ_succ,add_assoc] using hz
  have hz₂ : a^2+b^2+c^2+u^2+v^2 = 10 := by simpa [a,b,c,u,v,Fin.sum_univ_succ,add_assoc] using hz2
  have hpair : u+v = -(a+b+c) := by linear_combination hz'
  have hd : (u-v)^2 = 20-2*(a^2+b^2+c^2)-(a+b+c)^2 := by
    calc
      _ = 2*(u^2+v^2)-(u+v)^2 := by ring
      _ = _ := by rw [hpair]; linear_combination 2*hz₂
  obtain ⟨ar,ai⟩ := square_bounds_detail a _ _ har ha'
  obtain ⟨br,bi⟩ := square_bounds_detail b _ _ hbr hb'
  obtain ⟨cr,ci⟩ := square_bounds_detail c _ _ hcr hc'
  have hx : |(a+b+c).re| < 12/5 := by
    simp only [Complex.add_re]
    change |a.re| < 4/5 at har
    change |b.re| < 4/5 at hbr
    change |c.re| < 4/5 at hcr
    linarith only [abs_add_le (a.re+b.re) c.re, abs_add_le a.re b.re, har,hbr,hcr]
  have hy : |(a+b+c).im| < 3 := by
    simp only [Complex.add_im]
    linarith only [abs_add_le (a.im+b.im) c.im, abs_add_le a.im b.im,ha',hb',hc']
  obtain ⟨sr,si⟩ := square_bounds_detail (a+b+c) _ _ hx hy
  have hdr := congrArg Complex.re hd
  have hdi := congrArg Complex.im hd
  simp only [Complex.sub_re, Complex.mul_re, show (20 : ℂ).re = 20 from rfl,
    show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl,
    zero_mul, sub_zero, Complex.add_re] at hdr
  simp only [Complex.sub_im, Complex.mul_im, show (20 : ℂ).im = 0 from rfl,
    show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl,
    zero_mul, add_zero, Complex.add_im] at hdi
  have hR : 52/5 < ((u-v)^2).re := by linarith only [ar, br, cr, sr, hdr]
  have hI : |((u-v)^2).im| < 24 := by
    obtain ⟨aiLo, aiHi⟩ := abs_lt.mp ai
    obtain ⟨biLo, biHi⟩ := abs_lt.mp bi
    obtain ⟨ciLo, ciHi⟩ := abs_lt.mp ci
    obtain ⟨siLo, siHi⟩ := abs_lt.mp si
    exact abs_lt.mpr ⟨by linarith only [hdi, aiHi, biHi, ciHi, siHi],
      by linarith only [hdi, aiLo, biLo, ciLo, siLo]⟩
  let w := u-v
  have hre : (w^2).re ≤ w.re^2 := by simp [pow_two,Complex.mul_re]; nlinarith [sq_nonneg w.im]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 10)
  have hxw : Real.sqrt 10 < |w.re| := by
    apply (sq_lt_sq₀ (Real.sqrt_nonneg _) (abs_nonneg _)).mp
    rw [sq_abs,hs]
    linarith only [hR,hre]
  have hw : 0 < |w.re| := (Real.sqrt_nonneg _).trans_lt hxw
  have haim : |(w^2).im| = 2 * |w.re| * |w.im| := by
    rw [show (w^2).im=2*w.re*w.im by simp [pow_two,Complex.mul_im]; ring, abs_mul,abs_mul]
    norm_num
  refine ⟨hR,hre,hxw,?_,?_,?_⟩
  · exact (eq_div_iff (by positivity : 2*|w.re| ≠ 0)).mpr (by rw [haim]; ring)
  · change |(w^2).im|/(2*|w.re|) < _
    calc
      _ < 24/(2*|w.re|) := by gcongr
      _ ≤ 24/(2*Real.sqrt 10) := by gcongr
  · apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith only [hs,Real.sqrt_nonneg 10,sq_nonneg (Real.sqrt 10-3)]

/-- Sum both second moments over all five indexed roots. -/
theorem quintic_all_five_moment_bounds (z : Fin 5 → ℂ)
    (hz : ∑ i, z i = 0) (hz2 : ∑ i, (z i) ^ 2 = 10)
    (hh : ∀ i, 87 / 100 ≤ |(z i).im|)
    (hupper : ∀ i : Fin 5, i < 3 → 0 < (z i).im ∧ (z i).im < 1)
    (hlower : (z 3).im < 0 ∧ (z 4).im < 0) :
    let I := ∑ i, (z i).im ^ 2
    let R := ∑ i, (z i).re ^ 2
    let B := 3 + (213 / 100) * (|(z 3).im| + |(z 4).im|)
    I < B ∧ B < 939 / 100 ∧ R = 10 + I ∧ R < 20 := by
  obtain ⟨ha,ha'⟩ := hupper 0 (by decide)
  obtain ⟨hb,hb'⟩ := hupper 1 (by decide)
  obtain ⟨hc,hc'⟩ := hupper 2 (by decide)
  obtain ⟨hu,hv⟩ := hlower
  have h3 := hh 3
  have h4 := hh 4
  rw [abs_of_neg hu] at h3
  rw [abs_of_neg hv] at h4
  have hi := congrArg Complex.im hz
  have hre := congrArg Complex.re hz2
  simp [Fin.sum_univ_succ,Complex.add_im] at hi
  simp [Fin.sum_univ_succ,Complex.add_re,pow_two,Complex.mul_re] at hre
  dsimp only
  rw [abs_of_neg hu,abs_of_neg hv]
  simp [Fin.sum_univ_succ]
  have htot : -3 < (z 3).im + (z 4).im := by linarith only [hi,ha',hb',hc']
  have hu' : -(213/100) < (z 3).im := by linarith only [htot,h4]
  have hv' : -(213/100) < (z 4).im := by linarith only [htot,h3]
  have hs3 := mul_lt_mul_of_neg_right hu' hu
  have hs4 := mul_lt_mul_of_neg_right hv' hv
  have hs0 := (sq_lt_sq₀ ha.le (by norm_num : (0:ℝ)≤1)).2 ha'
  have hs1 := (sq_lt_sq₀ hb.le (by norm_num : (0:ℝ)≤1)).2 hb'
  have hs2 := (sq_lt_sq₀ hc.le (by norm_num : (0:ℝ)≤1)).2 hc'
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith only [hs0,hs1,hs2,hs3,hs4,htot,hre]

#print axioms quintic_difference_sqrt_chain
#print axioms quintic_rectangle_quadratic_monotonicity
#print axioms quintic_discriminant_sqrt_separation
#print axioms quintic_all_five_moment_bounds

end Turan
