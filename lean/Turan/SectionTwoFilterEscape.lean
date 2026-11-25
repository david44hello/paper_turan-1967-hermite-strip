-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.SectionTwoAlgebraDefs
import Turan.SlotDerivatives

noncomputable section
open Polynomial Filter Metric
open scoped Topology
namespace Turan.SectionTwo

private theorem single_filter_flat (k : ℕ → ℕ) (F : ℕ → Polynomial ℂ)
    (he : escapesDisks F)
    (hf : TendstoLocallyUniformly (fun j z => (F j).eval z / (F j).eval 0)
      (fun _ => 1) atTop) :
    let G := fun j => realFilter (lambda (k j)) (F j)
    escapesDisks G ∧ TendstoLocallyUniformly (fun j z => (G j).eval z / (G j).eval 0)
      (fun _ => 1) atTop := by
  intro G
  have coeff (n : ℕ) : 2 / (lambda n : ℂ) = (n : ℂ)⁻¹ := by
    simpa [lambda] using div_mul_cancel_left₀ (by norm_num : (2 : ℂ) ≠ 0) (n : ℂ)
  have hrel : TendstoLocallyUniformly (fun j z => (G j).eval z / (F j).eval 0)
      (fun _ => 1) atTop := by
    apply (locally_to_const _ _).mpr
    intro z
    let l := (atTop : Filter ℕ) ×ˢ 𝓝 z
    have hbase := (locally_to_const _ _).mp hf z
    have hfree : ∀ᶠ p : ℕ × ℂ in l, (F p.1).eval p.2 ≠ 0 :=
      (hbase.eventually_ne one_ne_zero).mono fun p hp => (div_ne_zero_iff.mp hp).1
    let D := fun m (p : ℕ × ℂ) => (derivative^[m] (F p.1)).eval p.2 / (F p.1).eval 0
    have hD (m : ℕ) (hm : 1 ≤ m) : Tendsto (D m) l (𝓝 0) := by
      have h := ((locally_to_const _ _).mp (slot_derivative_limit F he hf m hm) z).mul hbase
      rw [zero_mul] at h
      exact h.congr' (hfree.mono fun p hp => div_mul_div_cancel₀ hp)
    have hz : Tendsto (fun p : ℕ × ℂ => p.2) l (𝓝 z) := tendsto_snd
    have hop := ((hD 2 (by decide)).const_mul (1 / 2 : ℂ)).sub (hz.mul (hD 1 (by decide)))
    simp only [mul_zero, sub_zero] at hop
    let a := fun p : ℕ × ℂ => (k p.1 : ℂ)⁻¹
    have hb : IsBoundedUnder (· ≤ ·) l (norm ∘ a) := by
      apply isBoundedUnder_of
      refine ⟨1, fun p => ?_⟩
      change ‖(k p.1 : ℂ)⁻¹‖ ≤ 1
      rw [norm_inv, Complex.norm_natCast]
      rcases Nat.eq_zero_or_pos (k p.1) with h | h
      · simp [h]
      · rw [inv_le_one₀ (by exact_mod_cast h)]
        exact_mod_cast h
    have h := hbase.add (isBoundedUnder_le_mul_tendsto_zero hb hop)
    rw [add_zero] at h
    refine h.congr (fun p => ?_)
    simp [G, realFilter, coeff, EStar, D, a, eval_add, eval_mul, eval_sub]
    ring
  constructor
  · intro R _
    have hu := tendstoLocallyUniformly_iff_forall_isCompact.mp hrel _
      (isCompact_closedBall (0 : ℂ) R)
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu 1 one_pos] with j hj
    intro z hz hzero
    have h := hj z (by simpa using hz)
    simp [hzero] at h
  · have hrel₀ : TendstoLocallyUniformly (fun j (_ : ℂ) => (G j).eval 0 / (F j).eval 0)
        (fun _ => 1) atTop := hrel.comp (fun _ => 0) continuous_const
    have he₀ := (he 1 one_pos).mono fun j hj => hj 0 (by simp)
    apply (locally_to_const _ _).mpr
    intro z
    have h := ((locally_to_const _ _).mp hrel z).div
      ((locally_to_const _ _).mp hrel₀ z) one_ne_zero
    rw [div_one] at h
    exact h.congr' ((tendsto_fst.eventually he₀).mono fun p hp => div_div_div_cancel_right₀ hp _ _)

/-- Two rounds of modal filters preserve escape on every disk for a flat normalized family. -/
theorem two_round_escape_of_flat {s : ℕ} (q : ℕ → Fin s → ℕ) (A B : Finset (Fin s))
    (F : ℕ → Polynomial ℂ) (he : escapesDisks F)
    (hf : TendstoLocallyUniformly (fun j z => (F j).eval z / (F j).eval 0)
      (fun _ => 1) atTop) :
    escapesDisks (fun j => applyFilters (q j) B (applyFilters (q j) A (F j))) := by
  have fold (l : List (Fin s)) :
      let G := fun j => l.foldr (fun v p => realFilter (lambda (q j v)) p) (F j)
      escapesDisks G ∧ TendstoLocallyUniformly (fun j z => (G j).eval z / (G j).eval 0)
        (fun _ => 1) atTop := by
    induction l with
    | nil => exact ⟨he, hf⟩
    | cons v l ih => exact single_filter_flat (fun j => q j v) _ ih.1 ih.2
  simpa only [List.foldr_append, applyFilters] using (fold (B.toList ++ A.toList)).1

end Turan.SectionTwo
