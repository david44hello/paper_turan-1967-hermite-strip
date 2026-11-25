-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.TailStripCore

noncomputable section
open Set Polynomial
namespace Turan.UpperTailStrip

def stripWeight (m : ℕ) (z : ℂ) : ℂ :=
  (1-4*Complex.I*z/(Real.sqrt (2*(m:ℝ)) : ℂ))^4

private theorem weight_eq (m : ℕ) (hm : 450 ≤ m) (z : ℂ) :
    stripWeight m z = (TailStrip.weightBase m z / (Real.sqrt (2*(m:ℝ)) : ℂ))^4 := by
  have h : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hn : (Real.sqrt (2*(m:ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by positivity)).ne'
  unfold stripWeight TailStrip.weightBase
  congr 1
  field_simp

theorem variable_weight_lower (m : ℕ) (hm : 450 ≤ m) (z : ℂ) (hz : z ∈ TailStrip.strip) :
    let A := Real.sqrt (2*(m:ℝ))
    stripWeight m z = (TailStrip.weightBase m z / (A : ℂ))^4 ∧ stripWeight m z ≠ 0 ∧
    (1-4*TailStrip.height/A)^4*(omega m z)^4/(4*(m:ℝ)^2) ≤ ‖stripWeight m z‖ := by
  intro A
  let r := 1-4*TailStrip.height/A
  have hm' : (450:ℝ) ≤ m := by exact_mod_cast hm
  have hA : 30 ≤ A := Real.le_sqrt_of_sq_le (by linarith)
  have hp : 0 < A := by linarith
  have hs : A^2 = 2*(m:ℝ) := Real.sq_sqrt (by positivity)
  have hr : 0 ≤ r := sub_nonneg.mpr ((div_le_iff₀ hp).mpr (by dsimp [TailStrip.height]; linarith))
  have hr1 : r ≤ 1 := sub_le_self _ (by dsimp [TailStrip.height]; positivity)
  have he : r*A = A-4*TailStrip.height := by dsimp [r]; field_simp
  have hy := (abs_le.mp (show |z.im| ≤ TailStrip.height from hz)).1
  have hle : r*A ≤ A+4*z.im := by rw [he]; linarith
  have hw := TailStrip.weight_sq m z
  have h : r * omega m z ≤ ‖TailStrip.weightBase m z‖ := by
    apply (sq_le_sq₀ (mul_nonneg hr (Real.sqrt_nonneg _)) (norm_nonneg _)).mp
    change (r*Real.sqrt (2*(m:ℝ)+16*z.re^2))^2 ≤ ‖TailStrip.weightBase m z‖^2
    rw [mul_pow, Real.sq_sqrt (by positivity), hw]
    change r^2*(2*(m:ℝ)+16*z.re^2) ≤ (A+4*z.im)^2+16*z.re^2
    rw [show 2*(m:ℝ)+16*z.re^2 = A^2+16*z.re^2 by rw [hs]]
    calc
      _ = (r*A)^2 + r^2*(16*z.re^2) := by ring
      _ ≤ _ := add_le_add (pow_le_pow_left₀ (mul_nonneg hr hp.le) hle 2)
        (mul_le_of_le_one_left (by positivity) (pow_le_one₀ hr hr1))
  refine ⟨weight_eq m hm z, ?_, ?_⟩
  · rw [weight_eq m hm z]
    apply pow_ne_zero
    apply div_ne_zero (norm_pos_iff.mp ((by norm_num : (0:ℝ)<1).trans_le (TailStrip.one_le_weight hm hz)))
    exact Complex.ofReal_ne_zero.mpr hp.ne'
  · rw [weight_eq m hm z, norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg hp.le, div_pow]
    have hA4 : A^4 = 4*(m:ℝ)^2 := by rw [show A^4 = (A^2)^2 by ring, hs]; ring
    change r^4 * (omega m z)^4 / _ ≤ _ / A^4
    rw [← hA4, ← mul_pow]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg hr (Real.sqrt_nonneg _)) h 4) (by positivity)

def selectedRoots (j : ℕ) := (hermite j).roots.toFinset.filter
  (fun s => s.im = 0 ∧ -(7:ℝ)/2 ≤ s.re ∧ s.re ≤ 5/2)

private theorem product_lower (S : Finset ℂ) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ |z.re| → (1/3:ℝ)^S.card ≤ ‖∏ s ∈ S, TailStrip.factor s.re z‖ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert s S hs ih =>
    obtain ⟨R,hR⟩ := ih
    obtain ⟨P,hP⟩ := TailStrip.far_factor s.re
    refine ⟨max R P, fun z hz => ?_⟩
    rw [Finset.card_insert_of_notMem hs, pow_succ', Finset.prod_insert hs, norm_mul]
    exact mul_le_mul (hP z ((le_max_right ..).trans hz)) (hR z ((le_max_left ..).trans hz))
      (by positivity) (norm_nonneg _)

private theorem weight_grows (m : ℕ) (hm : 450 ≤ m) (B : ℝ) (hb : 1 ≤ B) :
    ∃ X : ℝ, 0 < X ∧ ∀ z : ℂ, X ≤ |z.re| → B < ‖stripWeight m z‖ := by
  let A := Real.sqrt (2*(m:ℝ))
  have hpos : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have ha : 0 < A := by dsimp [A]; positivity
  refine ⟨A*(B+1), by positivity, fun z hz => ?_⟩
  have he : (TailStrip.weightBase m z).im = -4*z.re := by
    simp [TailStrip.weightBase, Complex.mul_re, Complex.mul_im]
  have hn := Complex.abs_im_le_norm (TailStrip.weightBase m z)
  rw [he, abs_mul] at hn
  norm_num at hn
  have hgt : B < ‖TailStrip.weightBase m z‖/A := (lt_div_iff₀ ha).mpr (by
    nlinarith only [hz, hn, ha, abs_nonneg z.re])
  rw [weight_eq m hm z, norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg ha.le]
  apply hgt.trans_le
  simpa using (pow_le_pow_right₀ (hb.trans hgt.le) (by decide : 1 ≤ 4))

theorem weighted_decay (n m j : ℕ) (hm : 450 ≤ m) (hh : m ≤ 2*n) (hnm : n < m)
    (hj : j=n ∨ j=m) (a b : ℂ) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, 0 < X ∧ ∀ z ∈ TailStrip.strip, X ≤ |z.re| →
      ‖modeQuotient n m j a b z / stripWeight m z‖ < ε ∧
      ‖modeQuotient n m j a b z /
        (stripWeight m z * ∏ s ∈ selectedRoots j, TailStrip.factor s.re z)‖ < ε := by
  intro ε hε
  obtain ⟨P,Q,hdeg,_,hrep⟩ := TailStrip.mode_representation (by omega) hnm hj a b
  obtain ⟨L,hL⟩ := Asymptotics.isBigO_iff.mp (Polynomial.isBigO_cobounded_of_degree_le hdeg)
  obtain ⟨R,_,hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp hL
  let δ := (1/3:ℝ)^(selectedRoots j).card
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨U,hU⟩ := product_lower (selectedRoots j)
  let B := max 1 ((|L|+1)/(ε*δ))
  obtain ⟨T,hT,hW⟩ := weight_grows m hm B (le_max_left ..)
  refine ⟨max T (max R U), hT.trans_le (le_max_left ..), fun z _ hz => ?_⟩
  have hw := hW z ((le_max_left ..).trans hz)
  have hu := hU z ((le_max_right R U).trans ((le_max_right ..).trans hz))
  have hq : ‖modeQuotient n m j a b z‖ ≤ |L| := by
    rw [hrep, norm_div]
    by_cases hzero : Q.eval z = 0
    · simp [hzero]
    apply (div_le_iff₀ (norm_pos_iff.mpr hzero)).mpr
    exact (hR ((le_max_left R U).trans ((le_max_right ..).trans (hz.trans (Complex.abs_re_le_norm z))))).trans
      (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _))
  have hwpos := (zero_lt_one.trans_le (le_max_left 1 ((|L|+1)/(ε*δ)))).trans hw
  have hmain := (div_lt_iff₀ (mul_pos hε hδ)).mp ((le_max_right ..).trans_lt hw)
  have hl : ‖modeQuotient n m j a b z‖ < ε*‖stripWeight m z‖*δ := by linarith only [hq,hmain]
  constructor
  · rw [norm_div, div_lt_iff₀ hwpos]
    exact hl.trans_le (mul_le_of_le_one_right (mul_pos hε hwpos).le hδ1)
  · rw [norm_div, norm_mul, div_lt_iff₀ (mul_pos hwpos (hδ.trans_le hu)), ← mul_assoc]
    exact hl.trans_le (mul_le_mul_of_nonneg_left hu (mul_pos hε hwpos).le)

end Turan.UpperTailStrip
