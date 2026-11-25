-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.SectionTwoShifts
import Turan.SectionTwoExpansion
import Mathlib.Topology.Algebra.MvPolynomial

noncomputable section
open Polynomial Filter Metric Turan.SectionTwo.Expansion
open scoped Topology BigOperators Classical
namespace Turan.SectionTwo
variable {s : ℕ}

theorem frequency_sq (k : Fin s → ℕ) : frequency k ^ 2 = topLambda k :=
  Real.sq_sqrt (by unfold topLambda lambda; positivity)

theorem one_le_frequency {k : Fin s → ℕ} (h : 1 ≤ topLambda k) : 1 ≤ frequency k := by
  unfold frequency
  exact (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using h)

theorem lambda_le_top (k : Fin s → ℕ) (v : Fin s) : lambda (k v) ≤ topLambda k := by
  unfold topLambda lambda
  gcongr
  exact Finset.le_sup (Finset.mem_univ v)

theorem word_on_jets (k : Fin s → ℕ) (w : List (Fin s)) (p : Polynomial ℂ)
    (z : ℂ) (hω : 0 < frequency k) (l : ℕ) :
    scaledJet (frequency k) (w.foldr (fun v q => scaledShift (topLambda k) (lambda (k v)) q) p) l z =
    applyWord (z/(frequency k : ℂ)) (topLambda k : ℂ)⁻¹
      (fun v => ((lambda (k v)/topLambda k : ℝ) : ℂ))
      (fun t => scaledJet (frequency k) p t z) w l := by
  induction w generalizing l with
  | nil => rfl
  | cons t w ih =>
    rw [List.foldr_cons, ← frequency_sq k, scaledJet_shift _ hω, frequency_sq, applyWord]
    rw [ih, ih, ih]

private def coeff (s i : ℕ) : MvPolynomial (Fin (s+2)) ℂ :=
  applyWord (MvPolynomial.X 0) (MvPolynomial.X (0 : Fin (s+1)).succ)
    (fun v : Fin s => MvPolynomial.X v.succ.succ) (delta i) (List.finRange s) 0

private theorem coeff_eval (k : Fin s → ℕ) (z : ℂ) (i : ℕ) :
    MvPolynomial.eval (odeArguments k z) (coeff s i) =
    applyWord (z/(frequency k : ℂ)) (topLambda k : ℂ)⁻¹
      (fun v => ((lambda (k v)/topLambda k : ℝ) : ℂ)) (delta i) (List.finRange s) 0 := by
  rw [coeff, map_word]
  congr 1
  · simp [odeArguments]
  · simp [odeArguments]
  · funext v; simp [odeArguments]
  · funext l; by_cases hl : l = i <;> simp [delta, hl]

private theorem normal_form (k : Fin s → ℕ) (h : 1 ≤ topLambda k) (p : Polynomial ℂ) (z : ℂ) :
    (annihilator k p).eval z = scaledJet (frequency k) p (2*s) z +
      ∑ l : Fin (2*s), MvPolynomial.eval (odeArguments k z) (coeff s l) *
        scaledJet (frequency k) p l z := by
  let x := z/(frequency k : ℂ)
  let y := (topLambda k : ℂ)⁻¹
  let d (v : Fin s) : ℂ := ((lambda (k v)/topLambda k : ℝ) : ℂ)
  let J (t : ℕ) := scaledJet (frequency k) p t z
  let w := List.finRange s
  have hlen : w.length = s := List.length_finRange
  have hword : (annihilator k p).eval z = applyWord x y d J w 0 := by
    simpa only [annihilator, x, y, d, J, w, scaledJet, Function.iterate_zero_apply, pow_zero, div_one] using
      word_on_jets k w p z (zero_lt_one.trans_le (one_le_frequency h)) 0
  rw [hword, sum_coordinates x y d J w 0 (2*s) (by simp [hlen]),
    Finset.sum_range_succ, add_comm]
  have htop : applyWord x y d (delta (2*s)) w 0 = 1 := by
    simpa only [hlen, zero_add] using leading_one x y d w 0
  rw [htop, one_mul]
  congr 1
  simp only [coeff_eval, ← Fin.sum_univ_eq_sum_range, x, y, d, J, w]

private theorem args_bound (k : Fin s → ℕ) (h : 1 ≤ topLambda k) (R : ℝ) (z : ℂ)
    (hz : ‖z‖ ≤ R) : ‖odeArguments k z‖ ≤ max R 1 := by
  have hω := one_le_frequency h
  apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans (le_max_right R 1))).mpr
  refine Fin.cases ?_ (Fin.cases ?_ ?_)
  · simp only [odeArguments, Fin.cons_zero, norm_div, Complex.norm_of_nonneg (zero_le_one.trans hω)]
    exact (div_le_self (norm_nonneg _) hω).trans (hz.trans (le_max_left ..))
  · simp only [odeArguments, Fin.cons_succ, Fin.cons_zero, norm_inv,
      Complex.norm_of_nonneg (zero_le_one.trans h)]
    exact (inv_le_one_of_one_le₀ h).trans (le_max_right ..)
  · intro v
    simp only [odeArguments, Fin.cons_succ, Complex.norm_of_nonneg (show
      0 ≤ lambda (k v) / topLambda k by exact div_nonneg (by unfold lambda; positivity) (zero_le_one.trans h))]
    exact ((div_le_one (zero_lt_one.trans_le h)).mpr (lambda_le_top k v)).trans (le_max_right ..)

theorem scaled_annihilator_normal_form (s : ℕ) (hs : s ∈ Set.Icc 2 4) :
    ∃ P : Fin (2*s) → MvPolynomial (Fin (s+2)) ℂ,
      (∀ (k : Fin s → ℕ), 1 ≤ topLambda k → ∀ (p : Polynomial ℂ) (z : ℂ),
        (annihilator k p).eval z = scaledJet (frequency k) p (2*s) z +
          ∑ l, MvPolynomial.eval (odeArguments k z) (P l) * scaledJet (frequency k) p l z) ∧
      (∀ R : ℝ, 0 ≤ R → ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (k : Fin s → ℕ), 1 ≤ topLambda k →
        ∀ z : ℂ, ‖z‖ ≤ R → ∀ l, ‖MvPolynomial.eval (odeArguments k z) (P l)‖ ≤ C₀) ∧
      ∀ (k : Fin s → ℕ) (a : Fin s → ℂ), annihilator k (slotSum k a) = 0 := by
  refine ⟨fun l => coeff s l, normal_form, ?_, annihilator_slotSum⟩
  intro R _
  let D := closedBall (0 : Fin (s+2) → ℂ) (max R 1)
  have hc : IsCompact D := isCompact_closedBall .. 
  choose b hb using fun l : Fin (2*s) => hc.exists_bound_of_continuousOn
    (coeff s l).continuous_eval.continuousOn
  refine ⟨1 + ∑ l, |b l|, by positivity, ?_⟩
  intro k hk z hz l
  have hx : odeArguments k z ∈ D := by simpa [D, mem_closedBall] using args_bound k hk R z hz
  have hsum : |b l| ≤ ∑ i, |b i| := Finset.single_le_sum (fun i _ => abs_nonneg (b i)) (Finset.mem_univ l)
  linarith [hb l _ hx, le_abs_self (b l)]

end Turan.SectionTwo
