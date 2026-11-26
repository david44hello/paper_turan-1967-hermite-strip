module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Turan.Hermite
public import Turan.Normalized
public import Turan.GeneratingKernel
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

noncomputable section
open Filter Metric Set Polynomial
open scoped ComplexConjugate Topology
namespace Turan.LowerTailSteps

def logTail (M : ℝ) : ℝ :=
  Real.log 2200000 + 5 * Real.log M + 8 + (76/100 : ℝ) * Real.sqrt (2*M) - (197/1000 : ℝ) * M

theorem logTail_rate :
    (∀ M ∈ Ici (450 : ℝ), HasDerivAt logTail
      (5/M + (76/100 : ℝ) / Real.sqrt (2*M) - 197/1000) M) ∧
    StrictAntiOn (deriv logTail) (Ici 450) ∧
    -(1606/10000 : ℝ) < deriv logTail 450 ∧ deriv logTail 450 < -(1605/10000 : ℝ) := by
  have hd (M : ℝ) (hM : 450 ≤ M) : HasDerivAt logTail
      (5/M + 0.76 / Real.sqrt (2*M) - 0.197) M := by
    have hp : 0 < M := by linarith
    have hs := (((hasDerivAt_id M).const_mul 2).sqrt (by simpa using (mul_pos (by norm_num : (0:ℝ)<2) hp).ne'))
    convert (((((Real.hasDerivAt_log hp.ne').const_mul 5).const_add (Real.log 2200000)).add_const 8).add
      (hs.const_mul (76/100))).sub ((hasDerivAt_id M).const_mul (197/1000)) using 1
    · funext t; simp [logTail,Pi.sub_apply,Pi.add_apply,id]
    · simp [id, div_eq_mul_inv]; ring
  have h450 := (hd 450 le_rfl).deriv
  refine ⟨fun M hM => by convert hd M hM using 1 <;> ring, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [(hd x hx).deriv, (hd y hy).deriv]
    have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
    have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hxy.le (by norm_num : (0:ℝ) ≤ 2))
    linarith only [div_lt_div_of_pos_left (by norm_num : (0:ℝ)<5) hx0 hxy,
      div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤0.76) (Real.sqrt_pos.mpr (by positivity : 0<2*x)) hs]
  all_goals rw [h450]; norm_num [show Real.sqrt (2*450:ℝ) = 30 by norm_num]

theorem logTail_decreases : logTail 450 < -12 ∧ StrictAntiOn logTail (Ici 450) := by
  have ⟨hd,hanti,_,hub⟩ := logTail_rate
  constructor
  · have hExp (n : ℕ) (r : ℝ) :
        (2.718:ℝ)^n*(1+r) ≤ Real.exp ((n:ℝ)+r) := by
      rw [Real.exp_add, ← mul_one (n:ℝ), Real.exp_nat_mul]
      by_cases hr : 0 ≤ 1+r
      · exact mul_le_mul (pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) n)
          (by linarith [Real.add_one_le_exp r]) hr (by positivity)
      · exact le_trans (mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_ge hr)) (by positivity)
    have hc : Real.log 2200000 < 14.9 := (Real.log_lt_iff_lt_exp (by norm_num)).mpr
      ((by norm_num : (2200000:ℝ) < 2.718^14*(1+0.9)).trans_le (by convert hExp 14 0.9 using 1 <;> norm_num))
    have hm : Real.log 450 < 6.15 := (Real.log_lt_iff_lt_exp (by norm_num)).mpr
      ((by norm_num : (450:ℝ) < 2.718^6*(1+0.15)).trans_le (by convert hExp 6 0.15 using 1 <;> norm_num))
    norm_num [logTail]
    linarith
  · apply strictAntiOn_of_deriv_neg (convex_Ici _) (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    intro t ht
    have h := hanti.antitoneOn (show (450:ℝ) ∈ Ici 450 by simp) (interior_subset ht) (interior_subset ht : t ∈ Ici (450:ℝ))
    linarith

def factorDistanceSq (x r s t : ℝ) : ℝ := (x-s)^2 + r^2 + 2*(x-s)*r*t

def gaussianLog (x r t : ℝ) : ℝ := -(x^2 + 2*x*r*t + r^2*(2*t^2-1))/2

theorem polar_log_concavity (x r s : ℝ) (hr : 0 < r) :
    ConcaveOn ℝ {t : ℝ | t ∈ Icc (-1 : ℝ) 1 ∧ 0 < factorDistanceSq x r s t}
      (fun t => Real.log (factorDistanceSq x r s t)/2) ∧
    ConcaveOn ℝ (Icc (-1 : ℝ) 1) (gaussianLog x r) := by
  have hlin (a b t u : ℝ) (hab : a+b=1) :
      factorDistanceSq x r s (a*t+b*u) = a*factorDistanceSq x r s t + b*factorDistanceSq x r s u := by
    unfold factorDistanceSq
    linear_combination -((x-s)^2+r^2)*hab
  constructor
  · constructor
    · intro t ht u hu a b ha hb hab
      refine ⟨convex_Icc _ _ ht.1 hu.1 ha hb hab, ?_⟩
      rw [smul_eq_mul, smul_eq_mul, hlin _ _ _ _ hab]
      rcases eq_or_lt_of_le ha with h | h
      · subst a; simp_all
      · exact add_pos_of_pos_of_nonneg (mul_pos h ht.2) (mul_nonneg hb hu.2.le)
    · intro t ht u hu a b ha hb hab
      simp only [smul_eq_mul, hlin _ _ _ _ hab]
      have H := strictConcaveOn_log_Ioi.concaveOn.2 ht.2 hu.2 ha hb hab
      simp only [smul_eq_mul] at H
      linarith
  · refine ⟨convex_Icc _ _, ?_⟩
    intro t ht u hu a b ha hb hab
    have he : b = 1-a := by linarith
    subst b
    simp only [gaussianLog, smul_eq_mul]
    nlinarith only [mul_nonneg (mul_nonneg ha hb) (mul_nonneg (sq_nonneg r) (sq_nonneg (t-u)))]

theorem polar_log_values (x r s θ : ℝ) (hr : 0 < r) :
    let z := (x : ℂ) + r * Complex.exp ((θ : ℂ)*Complex.I)
    (z ≠ (s : ℂ) → Real.log ‖z-(s : ℂ)‖ = Real.log (factorDistanceSq x r s (Real.cos θ))/2) ∧
    Real.log ‖Complex.exp (-z^2/2)‖ = gaussianLog x r (Real.cos θ) := by
  let z := (x:ℂ) + r * Complex.exp ((θ:ℂ)*Complex.I)
  have hre : z.re = x + r*Real.cos θ := by simp [z, Complex.exp_mul_I, Complex.cos_ofReal_re, Complex.add_re, Complex.mul_re]
  have him : z.im = r*Real.sin θ := by simp [z, Complex.exp_mul_I, Complex.sin_ofReal_re, Complex.add_im, Complex.mul_im]
  have hd : ‖z-(s:ℂ)‖^2 = factorDistanceSq x r s (Real.cos θ) := by
    rw [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,
      Complex.ofReal_im, hre, him]
    unfold factorDistanceSq
    linear_combination r^2 * Real.sin_sq_add_cos_sq θ
  change (_ → Real.log ‖z-(s:ℂ)‖ = _) ∧ Real.log ‖Complex.exp (-z^2/2)‖ = _
  constructor
  · intro _
    rw [← hd,Real.log_pow]; ring
  · rw [Complex.norm_exp,Real.log_exp,Complex.div_ofNat_re,Complex.neg_re,sq,Complex.mul_re,hre,him]
    unfold gaussianLog
    linear_combination r^2/2 * Real.sin_sq_add_cos_sq θ

theorem mehler_diagonal_term (n : ℕ) (z : ℂ) :
    let term := fun k : ℕ => (1/5 : ℝ)^k * ‖psi k z‖^2
    let K := (Real.sqrt (1 - 1/25 : ℝ))⁻¹ * Real.exp (z.re^2/3 + z.im^2/2)
    (∀ k : ℕ, ((1/5 : ℂ)^k * psi k z * psi k (conj z)) = (term k : ℂ)) ∧
    HasSum term K ∧ term n ≤ ∑' k, term k ∧ term n ≤ K := by
  dsimp only
  have ht (k : ℕ) : (1/5:ℂ)^k * psi k z * psi k (conj z) = (((1/5:ℝ)^k*‖psi k z‖^2:ℝ):ℂ) := by
    have hc : psi k (conj z) = conj (psi k z) := by simp [psi, (hermite_symmetry k z).1]
    rw [hc, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have hk := mehler_kernel (1/5) (by norm_num) (by norm_num) z (conj z)
  have hcast : (((1/5:ℝ):ℂ)) = (1/5:ℂ) := by norm_num
  simp only [hcast, ht] at hk
  have he : (2*z*conj z*((1/5:ℝ):ℂ) - (z^2+(conj z)^2)*((1/5:ℝ):ℂ)^2)/(1-((1/5:ℝ):ℂ)^2) =
      ((z.re^2/3+z.im^2/2:ℝ):ℂ) := by
    apply Complex.ext <;> norm_num [sq, Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,
      Complex.add_re,Complex.add_im,Complex.div_re,Complex.div_im,Complex.normSq_apply] <;> ring
  simp only [hcast] at he
  rw [he, ← Complex.ofReal_exp, ← Complex.ofReal_inv, ← Complex.ofReal_mul] at hk
  have H := Complex.hasSum_ofReal.mp hk
  norm_num at H
  have H' : HasSum (fun k : ℕ => (1/5:ℝ)^k * ‖psi k z‖^2)
      ((Real.sqrt (1-1/25:ℝ))⁻¹ * Real.exp (z.re^2/3+z.im^2/2)) := by convert H using 1 <;> norm_num
  have hl := H'.summable.le_tsum n (fun k _ => by positivity)
  exact ⟨ht,H',hl,hl.trans_eq H'.tsum_eq⟩

end Turan.LowerTailSteps
