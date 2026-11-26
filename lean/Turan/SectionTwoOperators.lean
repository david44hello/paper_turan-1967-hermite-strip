module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.SectionTwoFilters

@[expose] public section

noncomputable section
open Polynomial Filter Metric
open scoped Topology BigOperators Classical
namespace Turan.SectionTwo

theorem EStar_add (p q : Polynomial ℂ) : EStar (p+q) = EStar p + EStar q := by
  simp only [EStar, derivative_add]
  ring

theorem EStar_C_mul (c : ℂ) (p : Polynomial ℂ) : EStar (C c*p) = C c*EStar p := by
  simp only [EStar, derivative_C_mul]
  ring

private theorem realFilter_C_mul (μ : ℝ) (c : ℂ) (p : Polynomial ℂ) :
    realFilter μ (C c*p) = C c*realFilter μ p := by
  simp only [realFilter, EStar_C_mul]
  ring

private theorem filters_on_slot {s : ℕ} (k : Fin s → ℕ) (V : Finset (Fin s)) (v : Fin s)
    (hV : ∀ t ∈ V, 0 < lambda (k t)) :
    applyFilters k V (hermite (k v)) = C ((multiplier k V v : ℝ) : ℂ) * hermite (k v) := by
  let f (t : Fin s) := 1 - lambda (k v) / lambda (k t)
  have aux (l : List (Fin s)) (hl : ∀ t ∈ l, 0 < lambda (k t)) :
      l.foldr (fun t q => realFilter (lambda (k t)) q) (hermite (k v)) =
        C (((l.map f).prod : ℝ) : ℂ) * hermite (k v) := by
    induction l with
    | nil => simp
    | cons t l ih =>
      rw [List.foldr_cons, ih (fun i hi => hl i (by simp [hi])), realFilter_C_mul,
        (single_filter_action _ (hl t (by simp)) _).1]
      simp only [List.map_cons, List.prod_cons, Complex.ofReal_mul, map_mul, f]
      ring
  simpa only [applyFilters, multiplier, Finset.prod_map_toList, f] using
    aux V.toList (by simpa using hV)

theorem surviving_multipliers {s : ℕ} (k : ℕ → Fin s → ℕ) (γ : Fin s → ℝ)
    (hL : Tendsto (fun j => topLambda (k j)) atTop atTop)
    (hγ : ∀ v, Tendsto (fun j => lambda (k j v) / topLambda (k j)) atTop (𝓝 (γ v))) :
    let V := Finset.univ.filter (fun v => 0 < γ v)
    (∀ᶠ j in atTop, ∀ v, applyFilters (k j) V (hermite (k j v)) =
      C ((multiplier (k j) V v : ℝ) : ℂ) * hermite (k j v)) ∧
    (∀ v ∈ V, ∀ᶠ j in atTop, multiplier (k j) V v = 0) ∧
    (∀ v, γ v = 0 → Tendsto (fun j => multiplier (k j) V v) atTop (𝓝 1)) := by
  intro V
  have htop := hL.eventually_gt_atTop 0
  have hpos : ∀ᶠ j in atTop, ∀ t ∈ V, 0 < lambda (k j t) := by
    apply (Filter.eventually_all_finset V).mpr
    intro t ht
    filter_upwards [htop, (hγ t).eventually_const_lt (Finset.mem_filter.mp ht).2] with j hj hq
    exact (div_pos_iff_of_pos_right hj).mp hq
  refine ⟨hpos.mono (fun j hj v => filters_on_slot _ _ _ hj), ?_, ?_⟩
  · intro v hv
    filter_upwards [hpos] with j hj
    apply Finset.prod_eq_zero hv
    simp [(hj v hv).ne']
  · intro v hv
    have term (t) (ht : t ∈ V) : Tendsto (fun j => 1 - lambda (k j v)/lambda (k j t)) atTop (𝓝 1) := by
      have htγ := (Finset.mem_filter.mp ht).2
      have hq := (hγ v).div (hγ t) htγ.ne'
      rw [hv, zero_div] at hq
      have eq : (fun j => (lambda (k j v)/topLambda (k j)) /
          (lambda (k j t)/topLambda (k j))) =ᶠ[atTop] (fun j => lambda (k j v)/lambda (k j t)) := by
        filter_upwards [htop] with j hj
        simp [div_div_div_cancel_right₀ hj.ne']
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hq.congr' eq)
    simpa [multiplier] using tendsto_finsetProd V term

theorem scaled_commutations (ω : ℝ) (hω : 0 < ω) (μ ν : ℝ) (p : Polynomial ℂ) :
    let D := fun q : Polynomial ℂ => C (ω : ℂ)⁻¹ * q.derivative
    let b := C (-2/(ω : ℂ)) * X
    D (b*p) = b*D p + C (-2/(ω : ℂ)^2)*p ∧
    scaledShift (ω^2) μ (scaledShift (ω^2) ν p) =
      scaledShift (ω^2) ν (scaledShift (ω^2) μ p) := by
  dsimp only
  constructor
  · apply Polynomial.funext
    intro z
    simp only [derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_X, eval_C,
      eval_zero, eval_one]
    field_simp [Complex.ofReal_ne_zero.mpr hω.ne']
    ring
  · simp only [scaledShift, ← map_ofNat (C : ℂ →+* Polynomial ℂ) 2, EStar_C_mul, EStar_add]
    ring

end Turan.SectionTwo
