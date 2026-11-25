-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Challenge.SectionTwoAlgebra
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

noncomputable section
open Polynomial Filter Metric InnerProductSpace
open scoped Topology BigOperators ComplexConjugate Classical
namespace Turan.SectionTwo

variable {s : ℕ}

def scaledLog (ω : ℝ) (p : Polynomial ℂ) (z : ℂ) : ℝ :=
  Real.log ‖p.eval z‖ / ω

def complexGradient (u : ℂ → ℝ) (z : ℂ) : ℂ :=
  ((fderiv ℝ u z 1 : ℝ) : ℂ) - Complex.I * ((fderiv ℝ u z Complex.I : ℝ) : ℂ)

def jetRatio (ω : ℝ) (p : Polynomial ℂ) (l : ℕ) (z : ℂ) : ℂ :=
  scaledJet ω p l z / p.eval z

theorem normalized_log_bounds (hs : s ∈ Set.Icc 2 4) (k : ℕ → Fin s → ℕ)
    (a : ℕ → Fin s → ℂ) (hω : Tendsto (fun j => frequency (k j)) atTop atTop)
    (hjet : ∀ᶠ j in atTop, unitInitialJet (k j) (slotSum (k j) (a j)))
    (he : escapesDisks (fun j => slotSum (k j) (a j))) :
    let u := fun j => scaledLog (frequency (k j)) (slotSum (k j) (a j))
    let b := fun j => -Real.log (((2*s-1).factorial : ℕ) : ℝ) / frequency (k j)
    Tendsto b atTop (𝓝 0) ∧ ∀ R : ℝ, 0 < R → ∃ C₀ : ℝ, ∀ᶠ j in atTop,
      HarmonicOnNhd (u j) (ball 0 R) ∧ (∀ z ∈ closedBall 0 R, u j z ≤ C₀) ∧
      ∃ z ∈ closedBall (0 : ℂ) 1, b j ≤ u j z := by sorry

theorem harmonic_subsequence_from_anchor (u : ℕ → ℂ → ℝ)
    (hup : ∀ R : ℝ, 0 < R → ∃ A : ℝ, ∀ᶠ j in atTop,
      HarmonicOnNhd (u j) (ball 0 R) ∧ ∀ z ∈ ball 0 R, u j z ≤ A)
    (hanchor : ∃ b : ℝ, ∀ᶠ j in atTop, ∃ z ∈ closedBall (0 : ℂ) 1, b ≤ u j z) :
    (∀ K : Set ℂ, IsCompact K → ∃ A : ℝ, ∀ᶠ j in atTop, ∀ z ∈ K, |u j z| ≤ A) ∧
    ∃ (φ : ℕ → ℕ) (v : ℂ → ℝ), StrictMono φ ∧ HarmonicOnNhd v Set.univ ∧
      TendstoLocallyUniformly (fun j => u (φ j)) v atTop := by sorry

theorem harmonic_slot_limit_symmetry (hs : s ∈ Set.Icc 2 4)
    (k : ℕ → Fin s → ℕ) (hk : ∀ j, Function.Injective (k j)) (a : ℕ → Fin s → ℂ)
    (hω : Tendsto (fun j => frequency (k j)) atTop atTop)
    (he : escapesDisks (fun j => slotSum (k j) (a j))) (u : ℂ → ℝ)
    (hu : HarmonicOnNhd u Set.univ)
    (hlim : TendstoLocallyUniformly (fun j => scaledLog (frequency (k j))
      (slotSum (k j) (a j))) u atTop) :
    (∀ z : ℂ, ∀ ε : ℝ, 0 < ε → ∃ w ∈ closedBall z ε, u (conj z) ≤ u w) ∧
    ∀ z : ℂ, u (conj z) = u z := by sorry

theorem scaled_quotient_identities (p : Polynomial ℂ) (ω : ℝ) (hω : 0 < ω)
    (z : ℂ) (hz : p.eval z ≠ 0) (l : ℕ) :
    complexGradient (scaledLog ω p) z = jetRatio ω p 1 z ∧
    deriv (jetRatio ω p l) z / (ω : ℂ) =
      jetRatio ω p (l+1) z - jetRatio ω p l z * jetRatio ω p 1 z := by sorry

theorem harmonic_jet_limits (F : ℕ → Polynomial ℂ) (ω : ℕ → ℝ)
    (hω : Tendsto ω atTop atTop) (he : escapesDisks F) (u : ℂ → ℝ)
    (hu : HarmonicOnNhd u Set.univ)
    (hlim : TendstoLocallyUniformly (fun j => scaledLog (ω j) (F j)) u atTop) :
    Differentiable ℂ (complexGradient u) ∧ ∀ l : ℕ, 1 ≤ l →
      TendstoLocallyUniformly (fun j => jetRatio (ω j) (F j) l)
        (fun z => (complexGradient u z)^l) atTop ∧
      TendstoLocallyUniformly (fun j z => deriv (jetRatio (ω j) (F j) l) z / (ω j : ℂ))
        (fun _ => 0) atTop := by sorry

theorem slot_characteristic_equation (hs : s ∈ Set.Icc 2 4) (k : ℕ → Fin s → ℕ)
    (a : ℕ → Fin s → ℂ) (γ : Fin s → ℝ) (Φ : ℂ → ℂ)
    (hω : Tendsto (fun j => frequency (k j)) atTop atTop)
    (hγ : ∀ v, Tendsto (fun j => lambda (k j v) / topLambda (k j)) atTop (𝓝 (γ v)))
    (he : escapesDisks (fun j => slotSum (k j) (a j)))
    (hQ : ∀ l : ℕ, 1 ≤ l → l ≤ 2*s → TendstoLocallyUniformly
      (fun j => jetRatio (frequency (k j)) (slotSum (k j) (a j)) l) (fun z => (Φ z)^l) atTop) :
    ∀ z : ℂ, (∏ v, ((Φ z)^2 + (γ v : ℂ))) = 0 := by sorry

theorem symmetric_gradient_vanishes (u : ℂ → ℝ) (hu : HarmonicOnNhd u Set.univ)
    (hsymm : ∀ z : ℂ, u (conj z) = u z) (γ : Fin s → ℝ) (hγ : ∀ v, 0 ≤ γ v)
    (hchar : ∀ z : ℂ, (∏ v, ((complexGradient u z)^2 + (γ v : ℂ))) = 0) :
    (∀ x : ℝ, (complexGradient u (x : ℂ)).im = 0) ∧
    (∀ z, complexGradient u z = 0) ∧ ∀ z, u z = u 0 := by sorry

theorem scaled_operator_power_limit (F : ℕ → Polynomial ℂ) (ω : ℕ → ℝ)
    (hω : Tendsto ω atTop atTop) (he : escapesDisks F)
    (hQ : ∀ l : ℕ, 1 ≤ l →
      TendstoLocallyUniformly (fun j => jetRatio (ω j) (F j) l) (fun _ => 0) atTop)
    (d : ℕ) (hd : 1 ≤ d) :
    TendstoLocallyUniformly
      (fun j z => (((fun p : Polynomial ℂ => C (2/(ω j : ℂ)^2)*EStar p)^[d])
        (F j)).eval z / (F j).eval z) (fun _ => 0) atTop := by sorry

theorem positive_ratio_reciprocal_bound (μ L : ℕ → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (h : Tendsto (fun j => μ j / L j) atTop (𝓝 γ)) :
    Tendsto (fun j => L j / μ j) atTop (𝓝 γ⁻¹) ∧
    ∀ᶠ j in atTop, |L j / μ j| ≤ 2/γ := by sorry

def removalRound (k : ℕ → Fin s → ℕ) (active removed : Finset (Fin s)) : Prop :=
  removed ⊆ active ∧
    ((removed = ∅ ∧ ∀ v ∈ active, ∃ d, ∀ j, k j v = d) ∨
     (removed.Nonempty ∧ Tendsto (fun j => active.sup (k j)) atTop atTop ∧
       ∃ γ : Fin s → ℝ, ∀ v ∈ active,
         Tendsto (fun j => lambda (k j v) / lambda (active.sup (k j))) atTop (𝓝 (γ v)) ∧
         (v ∈ removed ↔ 0 < γ v)))

theorem reduce_to_constant_indices (hs : s ∈ Set.Icc 2 4) (k : ℕ → Fin s → ℕ)
    (hk : ∀ j, Function.Injective (k j)) (v₀ v₁ : Fin s)
    (h₀ : ∀ j, k j v₀ = 0) (h₁ : ∀ j, k j v₁ = 1) :
    ∃ (φ : ℕ → ℕ) (A B : Finset (Fin s)), StrictMono φ ∧
      let q := fun j => k (φ j)
      let keep := (Finset.univ \ A) \ B
      let μ := fun j v => multiplier (q j) A v * multiplier (q j) B v
      removalRound q Finset.univ A ∧ removalRound q (Finset.univ \ A) B ∧
      v₀ ∈ keep ∧ v₁ ∈ keep ∧ (∀ v ∈ keep, ∃ d, ∀ j, q j v = d) ∧
      (∀ v ∈ keep, Tendsto (fun j => μ j v) atTop (𝓝 1)) ∧
      ∀ a : ℕ → Fin s → ℂ, (∀ j v, a j v ≠ 0) →
        let F := fun j => slotSum (q j) (a (φ j))
        let G := fun j => applyFilters (q j) B (applyFilters (q j) A (F j))
        (∀ᶠ j in atTop, G j = ∑ v ∈ keep, C ((μ j v : ℂ)*a (φ j) v) * hermite (q j v)) ∧
        (∀ t : ℕ → ℂ, (∀ v ∈ ({v₀, v₁} : Finset (Fin s)),
          Tendsto (fun j => a (φ j) v / t j) atTop (𝓝 1)) →
          ∀ v ∈ ({v₀, v₁} : Finset (Fin s)),
            Tendsto (fun j => (μ j v : ℂ)*a (φ j) v / t j) atTop (𝓝 1)) ∧
        (escapesDisks F → escapesDisks G) := by sorry

theorem largest_coefficient_limit (hs : s ∈ Set.Icc 2 4) (k : Fin s → ℕ)
    (hk : Function.Injective k) (v₀ v₁ : Fin s) (h₀ : k v₀ = 0) (h₁ : k v₁ = 1)
    (a : ℕ → Fin s → ℂ) (hc : Tendsto (fun j => a j v₀) atTop (𝓝 1))
    (hd : Tendsto (fun j => a j v₁) atTop (𝓝 1)) :
    ∃ (φ : ℕ → ℕ) (t : Fin s) (b : Fin s → ℂ), StrictMono φ ∧
      (∀ j, a (φ j) t ≠ 0 ∧ ∀ v, ‖a (φ j) v‖ ≤ ‖a (φ j) t‖) ∧ b t = 1 ∧
      (∀ v, Tendsto (fun j => a (φ j) v / a (φ j) t) atTop (𝓝 (b v))) ∧
      TendstoLocallyUniformly (fun j z => (slotSum k (a (φ j))).eval z / a (φ j) t)
        (fun z => (slotSum k b).eval z) atTop ∧
      ((∃ C₀ : ℝ, ∃ᶠ j in atTop, ∀ v, ‖a j v‖ ≤ C₀) →
        ∃ C₀ : ℝ, ∀ j v, ‖a (φ j) v‖ ≤ C₀) ∧
      (((∃ C₀ : ℝ, ∀ j v, ‖a (φ j) v‖ ≤ C₀) ∧ b v₁ ≠ 0) ∨
        (Tendsto (fun j => ‖a (φ j) t‖) atTop atTop ∧ b v₀ = 0 ∧ b v₁ = 0 ∧
          ∃ v, 2 ≤ k v ∧ ‖b v‖ = 1)) ∧ 0 < (slotSum k b).natDegree := by sorry

end Turan.SectionTwo
