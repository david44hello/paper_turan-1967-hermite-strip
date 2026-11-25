-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.SlotDefs
open Polynomial Filter Metric
open scoped Topology
namespace Turan

theorem slot_flat_limit (n m : ℕ → ℕ) (c d a b : ℕ → ℂ)
    (hi : ∀ j, 2 ≤ n j ∧ n j < m j) (hm : Tendsto m atTop atTop)
    (hn : (∃ B : ℕ, ∀ᶠ j in atTop, n j ≤ B) ∨ Tendsto n atTop atTop)
    (F : ℕ → Polynomial ℂ) (hF : ∀ j, F j = fourSlots (n j) (m j) (c j) (d j) (a j) (b j))
    (he : escapesDisks F) :
    TendstoLocallyUniformly (fun j z => (F j).eval z / (F j).eval 0) (fun _ => 1) atTop := by sorry

theorem slot_derivative_limit (F : ℕ → Polynomial ℂ) (he : escapesDisks F)
    (hflat : TendstoLocallyUniformly (fun j z => (F j).eval z / (F j).eval 0) (fun _ => 1) atTop)
    (k : ℕ) (hk : 1 ≤ k) :
    TendstoLocallyUniformly (fun j z => ((derivative^[k]) (F j)).eval z / (F j).eval z)
      (fun _ => 0) atTop := by sorry

theorem slot_filter_limit (n m : ℕ → ℕ) (c d a b : ℕ → ℂ)
    (hi : ∀ j, 2 ≤ n j ∧ n j < m j) (hm : Tendsto m atTop atTop)
    (hn : (∃ B : ℕ, ∀ᶠ j in atTop, n j ≤ B) ∨ Tendsto n atTop atTop)
    (γ : ℝ) (hγ : Tendsto (fun j => (n j:ℝ)/(m j:ℝ)) atTop (𝓝 γ))
    (F : ℕ → Polynomial ℂ) (hF : ∀ j, F j = fourSlots (n j) (m j) (c j) (d j) (a j) (b j))
    (he : escapesDisks F) (R : ℝ) (hR : 0 < R) :
    TendstoUniformlyOn (fun j z => (slotFilter (n j) (m j) γ (F j)).eval z / (F j).eval z)
      (fun _ => 1) atTop (sphere 0 R) ∧
    ∀ᶠ j in atTop, ∀ z : ℂ, ‖z‖ ≤ R → (slotFilter (n j) (m j) γ (F j)).eval z ≠ 0 := by sorry

end Turan
