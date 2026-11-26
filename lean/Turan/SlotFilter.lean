module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.SlotDerivatives
public import Turan.SlotFlat

@[expose] public section

noncomputable section
open Polynomial Filter Metric Set
open scoped Topology
namespace Turan

private theorem square_operator (p : Polynomial ℂ) (z : ℂ) :
    (EStar (EStar p)).eval z =
      p.derivative.derivative.derivative.derivative.eval z / 4 -
      z*p.derivative.derivative.derivative.eval z +
      (z^2-1)*p.derivative.derivative.eval z + z*p.derivative.eval z := by
  simp only [EStar, derivative_sub, derivative_mul, derivative_X, derivative_C, derivative_add,
    zero_mul, one_mul, zero_add, eval_sub, eval_add, eval_mul, eval_C, eval_X]
  ring

private theorem two_removals (n m : ℕ) (p : Polynomial ℂ) :
    removeMode n (removeMode m p) =
      p + C (m:ℂ)⁻¹ * EStar p + C (n:ℂ)⁻¹ * EStar p +
      C (n:ℂ)⁻¹ * C (m:ℂ)⁻¹ * EStar (EStar p) := by
  simp only [removeMode, EStar, derivative_add, derivative_C_mul]
  ring

private theorem bounded_factor_zero {ι : Type*} {l : Filter ι} (A X : ι → ℂ)
    (hA : ∀ i, ‖A i‖ ≤ 1) (hX : Tendsto X l (𝓝 0)) :
    Tendsto (fun i => A i*X i) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun i => norm_nonneg _) _ (tendsto_zero_iff_norm_tendsto_zero.mp hX)
  intro i
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hA i)

private theorem ratio_filter_locally (F : ℕ → Polynomial ℂ) (he : escapesDisks F)
    (hflat : TendstoLocallyUniformly (fun j z => (F j).eval z / (F j).eval 0) (fun _ => 1) atTop)
    (n m : ℕ → ℕ) (hi : ∀ j, 2 ≤ n j ∧ n j < m j) (γ : ℝ) :
    TendstoLocallyUniformly (fun j z => (slotFilter (n j) (m j) γ (F j)).eval z/(F j).eval z)
      (fun _ => 1) atTop := by
  apply (locally_to_const _ _).mpr
  intro z
  let l := (atTop : Filter ℕ) ×ˢ 𝓝 z
  let D := fun k (p : ℕ × ℂ) => (derivative^[k] (F p.1)).eval p.2 / (F p.1).eval p.2
  have hd (k : ℕ) (hk : 1 ≤ k) : Tendsto (D k) l (𝓝 0) :=
    (locally_to_const _ _).mp (slot_derivative_limit F he hflat k hk) z
  have hz : Tendsto (fun p : ℕ × ℂ => p.2) l (𝓝 z) := tendsto_snd
  let e := fun p : ℕ × ℂ => (EStar (F p.1)).eval p.2/(F p.1).eval p.2
  let e₂ := fun p : ℕ × ℂ => (EStar (EStar (F p.1))).eval p.2/(F p.1).eval p.2
  have h₁ : Tendsto e l (𝓝 0) := by
    have hlim := ((hd 2 (by decide)).const_mul (1/2:ℂ)).sub (hz.mul (hd 1 (by decide)))
    simp only [mul_zero, sub_zero] at hlim
    convert hlim using 1
    funext p
    simp [e,EStar,D,eval_mul,eval_sub]
    ring
  have h₂ : Tendsto e₂ l (𝓝 0) := by
    have hlim := (((hd 4 (by decide)).div_const (4:ℂ)).sub (hz.mul (hd 3 (by decide)))).add
      ((((hz.pow 2).sub_const 1).mul (hd 2 (by decide))).add (hz.mul (hd 1 (by decide))))
    simp only [zero_div, mul_zero, sub_zero, add_zero] at hlim
    convert hlim using 1
    funext p
    rw [show e₂ p = _ from congrArg (fun t => t/(F p.1).eval p.2) (square_operator _ _)]
    simp [D]
    ring
  have invBound (k : ℕ) (hk : 1 ≤ k) : ‖(k:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_natCast, inv_le_one₀ (by exact_mod_cast (show 0<k by omega))]
    exact_mod_cast hk
  let N := fun p : ℕ × ℂ => (n p.1:ℂ)⁻¹
  let M := fun p : ℕ × ℂ => (m p.1:ℂ)⁻¹
  have hN (p) : ‖N p‖ ≤ 1 := invBound _ (by have := hi p.1; omega)
  have hM (p) : ‖M p‖ ≤ 1 := invBound _ (by have := hi p.1; omega)
  have hbase : Tendsto (fun p => 1 + M p*e p) l (𝓝 1) := by
    simpa using (bounded_factor_zero M e hM h₁).const_add (1:ℂ)
  have hfree : ∀ᶠ p : ℕ × ℂ in l, (F p.1).eval p.2 ≠ 0 := by
    have hball : ∀ᶠ w in 𝓝 z, ‖w‖ < ‖z‖+1 :=
      (continuous_norm.continuousAt.eventually_lt_const (by linarith))
    filter_upwards [tendsto_fst.eventually (he (‖z‖+1) (by positivity)), hz.eventually hball] with p hf hp
    exact hf _ hp.le
  by_cases hγ : 0 < γ
  · have hlim := (hbase.add (bounded_factor_zero N e hN h₁)).add
      (bounded_factor_zero N _ hN (bounded_factor_zero M e₂ hM h₂))
    simp only [add_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [hfree] with p hp
    simp [slotFilter,hγ,two_removals,e,e₂,N,M,eval_add,eval_mul,add_div,mul_div_assoc,hp]
    <;> ring
  · refine hbase.congr' ?_
    filter_upwards [hfree] with p hp
    simp [slotFilter,hγ,removeMode,e,M,eval_add,eval_mul,add_div,mul_div_assoc,hp]

theorem slot_filter_limit (n m : ℕ → ℕ) (c d a b : ℕ → ℂ)
    (hi : ∀ j, 2 ≤ n j ∧ n j < m j) (hm : Tendsto m atTop atTop)
    (hn : (∃ B : ℕ, ∀ᶠ j in atTop, n j ≤ B) ∨ Tendsto n atTop atTop)
    (γ : ℝ) (hγ : Tendsto (fun j => (n j:ℝ)/(m j:ℝ)) atTop (𝓝 γ))
    (F : ℕ → Polynomial ℂ) (hF : ∀ j, F j = fourSlots (n j) (m j) (c j) (d j) (a j) (b j))
    (he : escapesDisks F) (R : ℝ) (hR : 0 < R) :
    TendstoUniformlyOn (fun j z => (slotFilter (n j) (m j) γ (F j)).eval z / (F j).eval z)
      (fun _ => 1) atTop (sphere 0 R) ∧
    ∀ᶠ j in atTop, ∀ z : ℂ, ‖z‖ ≤ R → (slotFilter (n j) (m j) γ (F j)).eval z ≠ 0 := by
  have hl := ratio_filter_locally F he (slot_flat_limit n m c d a b hi hm hn F hF he) n m hi γ
  have hu := tendstoLocallyUniformly_iff_forall_isCompact.mp hl _ (isCompact_closedBall (0:ℂ) R)
  refine ⟨hu.mono sphere_subset_closedBall, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu 1 zero_lt_one] with j hj
  intro z hz hzero
  have := hj z (by simpa using hz)
  simpa [hzero] using this

end Turan
