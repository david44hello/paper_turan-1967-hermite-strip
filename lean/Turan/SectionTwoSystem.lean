module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.SectionTwoNormalForm

@[expose] public section

noncomputable section
open Polynomial Filter Metric
open scoped Topology BigOperators Classical
namespace Turan.SectionTwo
variable {s : ℕ}

private def polyArgs (k : Fin s → ℕ) : Fin (s+2) → Polynomial ℂ :=
  Fin.cons (C (frequency k : ℂ)⁻¹ * X) (Fin.cons (C (topLambda k : ℂ)⁻¹)
    (fun v : Fin s => C ((lambda (k v) / topLambda k : ℝ) : ℂ)))

private theorem eval_polyArgs (k : Fin s → ℕ) (z : ℂ) (i : Fin (s+2)) :
    (polyArgs k i).eval z = odeArguments k z i := by
  refine Fin.cases ?_ (Fin.cases ?_ ?_) i
  · simp [polyArgs, odeArguments, eval_mul, div_eq_inv_mul]
  · simp [polyArgs, odeArguments]
  · intro v
    simp [polyArgs, odeArguments]

private def specializeCoeff (k : Fin s → ℕ) : MvPolynomial (Fin (s+2)) ℂ →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom C (polyArgs k)

private theorem eval_specializeCoeff (k : Fin s → ℕ) (z : ℂ) (Q : MvPolynomial (Fin (s+2)) ℂ) :
    (specializeCoeff k Q).eval z = MvPolynomial.eval (odeArguments k z) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [specializeCoeff]
  | add p q hp hq => simp [hp, hq]
  | mul_X p t hp => simp [eval_mul, hp, specializeCoeff, eval_polyArgs] at *

theorem scaledJet_deriv (ω : ℝ) (hω : 0 < ω) (p : Polynomial ℂ) (l : ℕ) (z : ℂ) :
    deriv (scaledJet ω p l) z = (ω : ℂ)*scaledJet ω p (l+1) z := by
  have hd := (((derivative^[l] p).hasDerivAt z).div_const ((ω : ℂ)^l)).deriv
  change deriv (fun w => (derivative^[l] p).eval w / (ω : ℂ)^l) z = _
  rw [hd]
  simp only [scaledJet, Function.iterate_succ_apply', pow_succ]
  field_simp [Complex.ofReal_ne_zero.mpr hω.ne']

theorem scaled_jet_system (s : ℕ) (hs : s ∈ Set.Icc 2 4) :
    ∃ A : (Fin s → ℕ) → Fin (2*s) → Fin (2*s) → Polynomial ℂ,
      (∀ (k : Fin s → ℕ), 1 ≤ topLambda k → ∀ (a : Fin s → ℂ) (l : Fin (2*s)) (z : ℂ),
        deriv (scaledJet (frequency k) (slotSum k a) l) z =
          ∑ t : Fin (2*s), (A k l t).eval z * scaledJet (frequency k) (slotSum k a) t z) ∧
      ∀ R : ℝ, 0 ≤ R → ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (k : Fin s → ℕ), 1 ≤ topLambda k →
        ∀ z : ℂ, ‖z‖ ≤ R → ∀ l t, ‖(A k l t).eval z‖ ≤ C₀ * frequency k := by
  obtain ⟨P, heq, hb, hzero⟩ := scaled_annihilator_normal_form s hs
  let A (k : Fin s → ℕ) (l t : Fin (2*s)) : Polynomial ℂ :=
    if h : l.val+1 < 2*s then
      if t = ⟨l.val+1,h⟩ then C (frequency k : ℂ) else 0
    else -C (frequency k : ℂ) * specializeCoeff k (P t)
  refine ⟨A, ?_, ?_⟩
  · intro k hk a l z
    rw [scaledJet_deriv _ (zero_lt_one.trans_le (one_le_frequency hk))]
    by_cases hl : l.val+1 < 2*s
    · simp [A, hl, apply_ite (eval z), ite_mul]
    · have hlast : l.val+1 = 2*s := by have := l.isLt; omega
      have h := heq k hk (slotSum k a) z
      rw [hzero, eval_zero] at h
      simp only [A, dite_eq_right hl, eval_neg, eval_mul, eval_C, eval_specializeCoeff, hlast,
        mul_assoc, ← Finset.mul_sum]
      linear_combination -(frequency k : ℂ) * h
  · intro R hR
    obtain ⟨b, hbpos, hbound⟩ := hb R hR
    refine ⟨max 1 b, lt_of_lt_of_le zero_lt_one (le_max_left ..), ?_⟩
    intro k hk z hz l t
    have hω := (zero_le_one.trans (one_le_frequency hk))
    unfold A
    split_ifs
    · rw [eval_C, Complex.norm_of_nonneg hω]
      exact le_mul_of_one_le_left hω (le_max_left ..)
    · simp only [eval_zero, norm_zero]
      positivity
    · rw [eval_mul, eval_neg, eval_C, norm_mul, norm_neg, Complex.norm_of_nonneg hω,
        eval_specializeCoeff, mul_comm]
      exact mul_le_mul_of_nonneg_right ((hbound k hk z hz t).trans (le_max_right ..)) hω

end Turan.SectionTwo
