-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.TrinomialDefs
import Turan.Rouche
import Turan.RealZeros

noncomputable section
open Polynomial
open scoped ComplexConjugate
namespace Turan

private theorem chartScale_pos (n : ℕ) : 0 < chartScale n := Nat.succ_pos _

private theorem odd_hermite_at_zero (m : ℕ) (hm : Odd m) : (hermite m).eval 0 = 0 := by
  have h := (hermite_symmetry m 0).2
  rw [neg_zero, hm.neg_one_pow, neg_one_mul] at h
  linear_combination (1/2 : ℂ) * h

/-- Parity selects a nonvanishing value or derivative at the origin. -/
theorem chartMode_eq_real_mul (n : ℕ) (hn : 4 ≤ n) :
    ∃ s : ℝ, s ≠ 0 ∧ chartMode n = C (s : ℂ) * hermite n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hreal (i : ℕ) : conj ((hermite i).eval 0) = (hermite i).eval 0 := by
    simpa using (hermite_symmetry i 0).1.symm
  by_cases he : Even (m+1)
  · have hprev := odd_hermite_at_zero m (Nat.not_even_iff_odd.mp (Nat.even_add_one.mp he))
    have hder : (hermite (m+1)).derivative.eval 0 = 0 := by
      rw [hermite_derivative, eval_smul, hprev, smul_zero]
    obtain ⟨v, hv⟩ := Complex.conj_eq_iff_real.mp (hreal (m+1))
    have hv0 : v ≠ 0 := by
      intro h
      exact (hermite_real_simple _ _ (by simpa [h] using hv)).2 hder
    exact ⟨v⁻¹, inv_ne_zero hv0, by simp [chartMode, he, hv]⟩
  · have hz := odd_hermite_at_zero (m+1) (Nat.not_even_iff_odd.mp he)
    have hd := (hermite_real_simple _ _ hz).2
    have hreal' : conj ((hermite (m+1)).derivative.eval 0) =
        (hermite (m+1)).derivative.eval 0 := by
      simp [hermite_derivative, nsmul_eq_mul, hreal, map_ofNat]
    obtain ⟨v, hv⟩ := Complex.conj_eq_iff_real.mp hreal'
    have hv0 : v ≠ 0 := fun h => hd (by simpa [h] using hv)
    exact ⟨(chartScale (m+1) : ℝ)/v, div_ne_zero (by exact_mod_cast (chartScale_pos _).ne') hv0,
      by simp [chartMode, he, hv]⟩

/-- Pull a root counted by Rouché back to the certified rectangle. -/
private theorem chart_root_upper (check : TrinomialDiskCheck) (n : ℕ) (hn : 4 ≤ n)
    (hn' : n ≤ 79) (swap : Bool) (θ : ℂ) (hθ : ‖θ‖ ≤ 1) (him : 0 ≤ θ.im) :
    ∃ c : ℂ, (trinomialChart n swap θ).eval c = 0 ∧ |c.re| ≤ 2 ∧ |c.im| < 76/100 := by
  classical
  obtain ⟨x, y, t, k, _, hk, _, cert⟩ := check n hn hn' swap θ
    ((Complex.abs_re_le_norm θ).trans hθ) him ((Complex.im_le_norm θ).trans hθ)
  let w : ℂ := ⟨(x : ℝ)/16384, (y : ℝ)/16384⟩
  let r : ℝ := (t : ℝ)/(16*chartScale n)
  let p := (trinomialChart n swap θ).comp (C w + C (r : ℂ)*X)
  change ‖w‖ + r < 9/10 ∧ |w.im| + r < 76/100 ∧
    (∑ d ∈ p.support.erase k, ‖p.coeff d‖) < ‖p.coeff k‖ at cert
  obtain ⟨hw, hwi, hdom⟩ := cert
  have hcount := dominant_polynomial_term p k hk hdom
  obtain ⟨z, hz⟩ := Multiset.card_pos_iff_exists_mem.mp (hcount.symm ▸ hk)
  obtain ⟨hzroot, hznorm⟩ := Multiset.mem_filter.mp hz
  have heval : p.eval z = 0 := isRoot_of_mem_roots hzroot
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hstep : ‖(r : ℂ)*z‖ ≤ r := by
    rw [norm_mul, Complex.norm_of_nonneg hr]
    exact mul_le_of_le_one_right hr hznorm.le
  refine ⟨w + (r : ℂ)*z, ?_, ?_, ?_⟩
  · simpa [p, eval_comp, eval_mul] using heval
  · have hnorm := (norm_add_le w ((r : ℂ)*z)).trans (add_le_add le_rfl hstep)
    linarith [Complex.abs_re_le_norm (w + (r : ℂ)*z)]
  · rw [Complex.add_im]
    exact (abs_add_le ..).trans_lt ((add_le_add le_rfl
      ((Complex.abs_im_le_norm _).trans hstep)).trans_lt hwi)

private theorem chart_root_unit (check : TrinomialDiskCheck) (n : ℕ) (hn : 4 ≤ n)
    (hn' : n ≤ 79) (s : ℝ) (hs : chartMode n = C (s : ℂ) * hermite n)
    (swap : Bool) (θ : ℂ) (hθ : ‖θ‖ ≤ 1) :
    ∃ c : ℂ, (trinomialChart n swap θ).eval c = 0 ∧ |c.re| ≤ 2 ∧ |c.im| < 76/100 := by
  by_cases him : 0 ≤ θ.im
  · exact chart_root_upper check n hn hn' swap θ hθ him
  obtain ⟨z, hz, hx, hy⟩ := chart_root_upper check n hn hn' swap (conj θ)
    (by simpa using hθ) (by simpa using (le_of_not_ge him))
  refine ⟨conj z, ?_, by simpa using hx, by simpa using hy⟩
  have h := congrArg (fun v : ℂ => conj v) hz
  cases swap <;> simpa [trinomialChart, hs, eval_mul, (hermite_symmetry n z).1, map_ofNat] using h

theorem trinomial_finite (check : TrinomialDiskCheck) (n : ℕ) (hn : 4 ≤ n)
    (hn' : n ≤ 79) (a : ℂ) :
    ∃ c : ℂ, 1 + 2*c + a*psi n c = 0 ∧ |c.re| ≤ 2 ∧ |c.im| < 76/100 := by
  obtain ⟨s, hs0, hs⟩ := chartMode_eq_real_mul n hn
  let d := Real.sqrt (2^n * (n.factorial : ℝ))
  have hd : 0 < d := by
    have := Nat.factorial_pos n
    dsimp [d]
    positivity
  let θ := a * (chartScale n : ℂ) / (2 * (s : ℂ) * (d : ℂ))
  have hroot : ∃ c : ℂ, (trinomialChart n false θ).eval c = 0 ∧
      |c.re| ≤ 2 ∧ |c.im| < 76/100 := by
    by_cases hθ : ‖θ‖ ≤ 1
    · exact chart_root_unit check n hn hn' s hs false θ hθ
    have hne : θ ≠ 0 := fun h => hθ (by simp [h])
    have hinv : ‖θ⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_not_ge hθ)
    obtain ⟨z, hz, hx, hy⟩ := chart_root_unit check n hn hn' s hs true θ⁻¹ hinv
    have hswap : trinomialChart n false θ = C θ * trinomialChart n true θ⁻¹ := by
      simp [trinomialChart, mul_add, ← mul_assoc, ← C_mul, hne]
    exact ⟨z, by rw [hswap, eval_mul, hz, mul_zero], hx, hy⟩
  obtain ⟨c, hc, hx, hy⟩ := hroot
  refine ⟨c, ?_, hx, hy⟩
  have he : (chartScale n : ℂ) * (c + 1/2) + θ * ((s : ℂ) * (hermite n).eval c) = 0 := by
    simpa [trinomialChart, hs, eval_mul] using hc
  have hscale : (chartScale n : ℂ) ≠ 0 := by exact_mod_cast (chartScale_pos n).ne'
  apply mul_left_cancel₀ hscale
  change (chartScale n : ℂ) * (1 + 2*c + a*((hermite n).eval c / (d : ℂ))) =
    (chartScale n : ℂ) * 0
  calc
    _ = 2 * ((chartScale n : ℂ) * (c + 1/2) + θ * ((s : ℂ) * (hermite n).eval c)) := by
      dsimp only [θ]
      field_simp [Complex.ofReal_ne_zero.mpr hs0, Complex.ofReal_ne_zero.mpr hd.ne']
      ring
    _ = _ := by rw [he, mul_zero, mul_zero]

end Turan
