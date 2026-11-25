-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.SectionTwoOperators

noncomputable section
open Polynomial Filter Metric
open scoped Topology BigOperators Classical
namespace Turan.SectionTwo
variable {s : ℕ}

/-- A scalar times T+d, common to the annihilator and the individual slot projector. -/
def weightedShift (c d : ℂ) (p : Polynomial ℂ) : Polynomial ℂ :=
  C c * (2 * EStar p + C d*p)

private theorem EStar_sum {ι : Type*} (I : Finset ι) (f : ι → Polynomial ℂ) :
    EStar (∑ i ∈ I, f i) = ∑ i ∈ I, EStar (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [EStar]
  | insert i I hi ih => simp [hi, EStar_add, ih]

theorem weightedShift_slotSum (c d : ℂ) (k : Fin s → ℕ) (a : Fin s → ℂ) :
    weightedShift c d (slotSum k a) = slotSum k (fun v => c*(d-(lambda (k v) : ℂ))*a v) := by
  simp only [weightedShift, slotSum, EStar_sum, EStar_C_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_mul, map_sub]
  linear_combination C c * C (a i) * twice_EStar_hermite (k i)

theorem fold_shifts (l : List (Fin s)) (c d : Fin s → ℂ) (k : Fin s → ℕ) (a : Fin s → ℂ) :
    l.foldr (fun t q => weightedShift (c t) (d t) q) (slotSum k a) =
      slotSum k (fun v => ((l.map (fun t => c t*(d t-(lambda (k v) : ℂ)))).prod)*a v) := by
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [List.foldr_cons, ih, weightedShift_slotSum]
    simp [mul_assoc]

theorem annihilator_slotSum (k : Fin s → ℕ) (a : Fin s → ℂ) :
    annihilator k (slotSum k a) = 0 := by
  change (List.finRange s).foldr (fun t q => weightedShift (topLambda k : ℂ)⁻¹
    (lambda (k t) : ℂ) q) _ = _
  rw [fold_shifts]
  apply Finset.sum_eq_zero
  intro v _
  have hm : (0 : ℂ) ∈ (List.finRange s).map (fun t =>
      (topLambda k : ℂ)⁻¹ * ((lambda (k t) : ℂ) - lambda (k v))) :=
    List.mem_map.mpr ⟨v, List.mem_finRange _, by simp⟩
  simp [List.prod_eq_zero hm]

theorem projectSlot_slotSum (k : Fin s → ℕ) (hk : Function.Injective k) (a : Fin s → ℂ)
    (v : Fin s) : projectSlot k v (slotSum k a) = C (a v)*hermite (k v) := by
  let S := Finset.univ.erase v
  let c (t : Fin s) : ℂ := (((lambda (k t)-lambda (k v) : ℝ) : ℂ))⁻¹
  let d (t : Fin s) : ℂ := lambda (k t)
  change S.toList.foldr (fun t q => weightedShift (c t) (d t) q) _ = _
  rw [fold_shifts, slotSum, Finset.sum_eq_single v]
  · have h (t : Fin s) (ht : t ∈ S) : c t * (d t - (lambda (k v) : ℂ)) = 1 := by
      have ht' := hk.ne (Finset.mem_erase.mp ht).1
      have hn : (k t : ℝ) ≠ k v := by exact_mod_cast ht'
      have hl : lambda (k t) ≠ lambda (k v) := by simpa [lambda] using hn
      simp [c, d, ← Complex.ofReal_sub, sub_ne_zero.mpr hl]
    rw [Finset.prod_map_toList, Finset.prod_congr rfl h]
    simp
  · intro t _ ht
    have h0 : ∏ i ∈ S, c i * (d i - (lambda (k t) : ℂ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨ht, Finset.mem_univ _⟩) (by simp [d])
    rw [Finset.prod_map_toList, h0]
    simp
  · simp

/-- Moving l ordinary derivatives past the linear drift introduces the -2l term. -/
theorem weightedShift_jet (c d : ℂ) (p : Polynomial ℂ) (z : ℂ) (l : ℕ) :
    (derivative^[l] (weightedShift c d p)).eval z =
      c * ((derivative^[l+2] p).eval z - 2*z*(derivative^[l+1] p).eval z +
        (d-2*(l : ℂ))*(derivative^[l] p).eval z) := by
  have form : weightedShift c d p = C c*(p.derivative.derivative -
      C 2*(p.derivative*X) + C d*p) := by
    apply Polynomial.funext
    intro w
    simp only [weightedShift, EStar, eval_mul, eval_add, eval_sub, eval_C, eval_ofNat, eval_X]
    ring
  rw [form]
  simp only [iterate_map_add, iterate_derivative_sub, iterate_derivative_C_mul,
    iterate_derivative_derivative_mul_X, eval_add, eval_sub, eval_mul, eval_X, eval_C,
    nsmul_eq_mul, eval_natCast]
  change c * (((derivative^[l+2] p).eval z - 2*((derivative^[l+1] p).eval z*z +
    (l : ℂ)*(derivative^[l] p).eval z)) + d*(derivative^[l] p).eval z) = _
  ring

theorem scaledJet_shift (ω : ℝ) (hω : 0 < ω) (μ : ℝ) (p : Polynomial ℂ) (l : ℕ) (z : ℂ) :
    scaledJet ω (scaledShift (ω^2) μ p) l z =
      scaledJet ω p (l+2) z - 2*(z/(ω : ℂ))*scaledJet ω p (l+1) z +
        (((μ / ω^2 : ℝ) : ℂ) - 2*(l : ℂ)*((ω^2 : ℝ) : ℂ)⁻¹)*scaledJet ω p l z := by
  change (derivative^[l] (weightedShift _ _ p)).eval z / (ω : ℂ)^l = _
  rw [weightedShift_jet]
  simp only [scaledJet, Complex.ofReal_div, Complex.ofReal_pow, pow_add, pow_one]
  field_simp [Complex.ofReal_ne_zero.mpr hω.ne']

end Turan.SectionTwo
