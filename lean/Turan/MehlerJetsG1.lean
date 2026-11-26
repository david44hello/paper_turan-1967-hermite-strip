module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TrinomialFinite
public import Turan.Degree
public import Turan.TransferDefs
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Data.Nat.Sqrt

@[expose] public section

noncomputable section
open Polynomial
open scoped ComplexConjugate
namespace Turan.MehlerJets

def g1Jet (n : ℕ) (ω : ℂ) (l : ℕ) : ℂ :=
  (diskExpansion (chartMode n) ω (1/(chartScale n : ℝ))).coeff l

private theorem factorial_disk_coeff (p : Polynomial ℂ) (w : ℂ) (r : ℝ) (l : ℕ) :
    (l.factorial:ℂ)*(diskExpansion p w r).coeff l = (derivative^[l] p).eval w * (r:ℂ)^l := by
  have h : diskExpansion p w r = (taylor w p).comp (C (r:ℂ)*X) := by
    simp [diskExpansion,taylor_apply,comp_assoc,add_comm (C w)]
  rw [h, comp_C_mul_X_coeff, taylor_coeff, ← mul_assoc, ← factorial_smul_hasseDeriv]
  simp [eval_smul,nsmul_eq_mul]

private theorem chart_deriv_step (n : ℕ) (hn : 4 ≤ n) (w : ℂ) (l : ℕ) :
    let d := fun i => (derivative^[i] (chartMode n)).eval w
    d (l+2) = 2*w*d (l+1) + 2*((l:ℂ)-n)*d l := by
  let H := hermite n
  have he : H.derivative.derivative = C 2*(H.derivative*X) - C (2*(n:ℂ))*H := by
    have h := hermite_equation n
    simp only [nsmul_eq_mul, Nat.cast_mul,Nat.cast_ofNat] at h
    simp [H,map_ofNat]
    linear_combination h
  have h := congrArg (fun p : Polynomial ℂ => (derivative^[l] p).eval w) he
  simp only [iterate_derivative_sub,iterate_derivative_C_mul,iterate_derivative_derivative_mul_X,
    eval_sub,eval_mul,eval_C,eval_add,eval_X,nsmul_eq_mul,eval_natCast] at h
  obtain ⟨s,_,hs⟩ := chartMode_eq_real_mul n hn
  dsimp only
  simp only [hs,iterate_derivative_C_mul,eval_mul,eval_C]
  change (derivative^[l+2] H).eval w = _ at h
  change (s:ℂ)*((derivative^[l+2] H).eval w) = _
  linear_combination (s:ℂ)*h

theorem g1_derivative_recurrence (n : ℕ) (hn : 4 ≤ n) (hn' : n ≤ 79)
    (ω : ℂ) (hω : 2*‖ω‖ ≤ (chartScale n : ℝ)) :
    let N := (chartScale n : ℂ)
    let γ := g1Jet n ω
    (∀ l : ℕ, (l.factorial:ℂ)*γ l = (derivative^[l] (chartMode n)).eval ω / N^l) ∧
    (∀ l : ℕ, ((l+2).factorial:ℂ)*γ (l+2) =
      (2*ω/N)*((l+1).factorial:ℂ)*γ (l+1) +
      (2*((l:ℂ)-(n:ℂ))/N^2)*(l.factorial:ℂ)*γ l) ∧
    ‖2*ω/N‖ ≤ 1 ∧ (∀ l : ℕ, l ≤ n → ‖2*((l:ℂ)-(n:ℂ))/N^2‖ ≤ 1) ∧
    (∀ l : ℕ, n < l → γ l = 0) := by
  intro N γ
  have hN : 0 < chartScale n := Nat.succ_pos _
  have hNC : N ≠ 0 := by dsimp [N]; exact_mod_cast hN.ne'
  have hNR : 0 < (chartScale n : ℝ) := by exact_mod_cast hN
  have hNsq : 2*n ≤ chartScale n ^ 2 := by
    have h := Nat.lt_succ_sqrt' (2*n-1)
    simp only [Nat.succ_eq_add_one] at h
    change 2*n ≤ ((2*n-1).sqrt+1)^2
    omega
  have hjet (l : ℕ) : (l.factorial:ℂ)*γ l = (derivative^[l] (chartMode n)).eval ω / N^l := by
    simpa [γ,g1Jet,N,div_eq_mul_inv] using factorial_disk_coeff (chartMode n) ω (1/(chartScale n:ℝ)) l
  refine ⟨hjet, ?_, ?_, ?_, ?_⟩
  · intro l
    have hstep := chart_deriv_step n hn ω l
    dsimp only at hstep
    rw [hjet, mul_assoc (2*ω/N), hjet, mul_assoc (2*((l:ℂ)-n)/N^2), hjet,
      hstep]
    simp only [pow_succ]
    field_simp
  · dsimp [N]; rw [norm_div,norm_mul,Complex.norm_natCast,Complex.norm_ofNat,div_le_one hNR]
    exact hω
  · intro l hl
    have hR : 2*(n:ℝ) ≤ (chartScale n:ℝ)^2 := by exact_mod_cast hNsq
    have hlR : (l:ℝ) ≤ n := by exact_mod_cast hl
    rw [norm_div, norm_mul, norm_pow, Complex.norm_ofNat]
    have hd : ‖(l:ℂ)-(n:ℂ)‖ = (n:ℝ)-l := by
      rw [← Complex.ofReal_natCast l, ← Complex.ofReal_natCast n, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hlR)]; ring
    dsimp only [N]; rw [hd, Complex.norm_natCast, div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α:=ℝ) l]
  · intro l hl
    obtain ⟨s,hs0,hs⟩ := chartMode_eq_real_mul n hn
    have hdeg : (chartMode n).natDegree = n := by
      rw [hs, natDegree_C_mul (Complex.ofReal_ne_zero.mpr hs0), (hermite_degree n).1]
    have h := hjet l
    rw [iterate_derivative_eq_zero (hdeg.trans_lt hl), eval_zero, zero_div] at h
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast Nat.factorial_ne_zero l)

theorem g1_factorial_tail (n : ℕ) (hn : 4 ≤ n) (hn' : n ≤ 79)
    (ω : ℂ) (hω : 2*‖ω‖ ≤ (chartScale n : ℝ)) (l : ℕ) :
    let γ := g1Jet n ω
    (l.factorial:ℝ)*‖γ l‖ ≤ (2:ℝ)^l * max ‖γ 0‖ ‖γ 1‖ := by
  intro γ
  let B := max ‖γ 0‖ ‖γ 1‖
  have hB : 0 ≤ B := (norm_nonneg _).trans (le_max_left ..)
  obtain ⟨_,hr,ha,hb,hz⟩ := g1_derivative_recurrence n hn hn' ω hω
  let N := (chartScale n : ℂ)
  change (l.factorial:ℝ)*‖γ l‖ ≤ 2^l*B
  induction l using Nat.twoStepInduction with
  | zero => simp [B]
  | one =>
    have h₁ : ‖γ 1‖ ≤ B := le_max_right ..
    simp; linarith
  | more i h₀ h₁ =>
    by_cases hi : i ≤ n
    · have he := congrArg norm (hr i)
      have ht := he.trans_le (norm_add_le ..)
      simp only [norm_mul, Complex.norm_natCast] at ht
      change _ ≤ ‖2*ω/N‖ * _ * _ + ‖2*((i:ℂ)-n)/N^2‖ * _ * _ at ht
      rw [mul_assoc ‖2*ω/N‖, mul_assoc ‖2*((i:ℂ)-n)/N^2‖] at ht
      have h (a b : ℝ) (ha : a ≤ 1) (hb : 0 ≤ b) : a*b ≤ b := mul_le_of_le_one_left hb ha
      have h' := ht.trans (add_le_add (h _ _ ha (by positivity)) (h _ _ (hb i hi) (by positivity)))
      change ((i+2).factorial:ℝ)*‖γ (i+2)‖ ≤ ((i+1).factorial:ℝ)*‖γ (i+1)‖ + (i.factorial:ℝ)*‖γ i‖ at h'
      simp only [pow_succ] at h₁ ⊢
      nlinarith only [h',h₀,h₁,mul_nonneg (by positivity : 0 ≤ (2:ℝ)^i) hB]
    · have hzero : γ (i+2)=0 := hz _ (by omega)
      rw [hzero,norm_zero,mul_zero]
      positivity

end Turan.MehlerJets
