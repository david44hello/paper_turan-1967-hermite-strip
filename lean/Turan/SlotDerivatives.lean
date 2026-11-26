module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.SlotDefs
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Filter Polynomial Set Metric
open scoped Topology
namespace Turan

theorem locally_to_const (G : ℕ → ℂ → ℂ) (v : ℂ) :
    TendstoLocallyUniformly G (fun _ => v) atTop ↔
    ∀ z : ℂ, Tendsto (fun p : ℕ × ℂ => G p.1 p.2) (atTop ×ˢ 𝓝 z) (𝓝 v) := by
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  apply forall_congr'
  intro z
  rw [nhds_eq_comap_uniformity (x := v), tendsto_comap_iff]
  rfl

private theorem normalized_derivatives (F : ℕ → Polynomial ℂ)
    (hflat : TendstoLocallyUniformly (fun j z => (F j).eval z / (F j).eval 0) (fun _ => 1) atTop)
    (k : ℕ) : TendstoLocallyUniformly
      (fun j z => (derivative^[k] (F j)).eval z / (F j).eval 0)
      (fun _ => if k=0 then 1 else 0) atTop := by
  induction k with
  | zero => simpa using hflat
  | succ k ih =>
    let p := fun j => derivative^[k] (F j)
    let g := fun j z => (p j).eval z / (F j).eval 0
    have hd (j) : Differentiable ℂ (g j) := (p j).differentiable.div_const _
    have hu := (tendstoLocallyUniformlyOn_univ.mpr ih).deriv
      (Eventually.of_forall fun j => (hd j).differentiableOn) isOpen_univ
    have hder (j) : deriv (g j) = fun z => (p j).derivative.eval z / (F j).eval 0 := by
      funext z
      exact ((p j).hasDerivAt z).div_const _ |>.deriv
    change TendstoLocallyUniformlyOn (deriv ∘ g) _ atTop univ at hu
    simp only [Function.comp_def, hder, deriv_const'] at hu
    simpa [p, Function.iterate_succ_apply'] using tendstoLocallyUniformlyOn_univ.mp hu

theorem slot_derivative_limit (F : ℕ → Polynomial ℂ) (he : escapesDisks F)
    (hflat : TendstoLocallyUniformly (fun j z => (F j).eval z / (F j).eval 0) (fun _ => 1) atTop)
    (k : ℕ) (hk : 1 ≤ k) :
    TendstoLocallyUniformly (fun j z => ((derivative^[k]) (F j)).eval z / (F j).eval z)
      (fun _ => 0) atTop := by
  have hu := normalized_derivatives F hflat k
  simp only [Nat.ne_of_gt hk, ite_false] at hu
  apply (locally_to_const _ _).mpr
  intro z
  have hz := ((locally_to_const _ _).mp hu z).div ((locally_to_const _ _).mp hflat z) one_ne_zero
  rw [zero_div] at hz
  refine hz.congr' ?_
  have hne : ∀ᶠ j in atTop, (F j).eval 0 ≠ 0 :=
    (he 1 zero_lt_one).mono fun j h => h _ (by simp)
  filter_upwards [tendsto_fst.eventually hne] with p hp
  change ((_ / (F p.1).eval 0) / (_ / (F p.1).eval 0)) = _
  rw [div_div_div_cancel_right₀ hp]

end Turan
