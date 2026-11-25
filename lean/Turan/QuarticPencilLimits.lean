-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.QuarticPencilDefs
import Turan.QuarticPencilAlgebra
import Turan.QuarticRoot
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Tactic

noncomputable section
open Polynomial Filter Set Metric
open scoped Topology
namespace Turan

theorem quartic_contact_square_alternatives (w d : ℂ) :
    (2*w+d)^2=4*w^2 ↔ d=0 ∨ d= -4*w := by
  constructor
  · intro h
    rcases mul_eq_zero.mp (show d*(d+4*w)=0 by linear_combination h) with h₀ | h₁
    · exact Or.inl h₀
    · exact Or.inr (by linear_combination h₁)
  · rintro (rfl | rfl) <;> ring

/-- The fixed-height resultant gives the contact without assuming Lemma 18. -/
theorem quartic_pencil_line_identification (w : ℂ)
    (hw : 0<w.im ∧ 12*w^4+16*w^3+12*w^2-3=0) (s d : ℝ)
    (hz : (contactPencilPoly d).eval (⟨s-1/2,w.im⟩ : ℂ)=0) :
    (⟨s-1/2,w.im⟩ : ℂ)=w ∧ d=0 := by
  let z : ℂ := ⟨s-1/2,w.im⟩
  rw [contactPencilPoly_eval] at hz
  have h₀ := QuarticPencil.height_equation 0 w hw.1.ne' (by
    push_cast
    linear_combination hw.2)
  simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero] at h₀
  have h₁ := QuarticPencil.height_equation d z hw.1.ne' hz
  have hlo := (quartic_root_height w hw).1
  have hs : 0 ≤ 3*w.im^2-2 := by
    nlinarith only [(sq_lt_sq₀ (by norm_num : (0:ℝ) ≤ 8286/10000) hw.1.le).2 hlo]
  have hd : d = 0 := by
    by_contra hn
    have hp := mul_pos (sq_pos_of_ne_zero hn) (QuarticPencil.correction_pos hs d)
    dsimp only [z] at h₁
    linarith only [h₁, h₀, hp]
  refine ⟨quartic_upper_root.unique ⟨hw.1, ?_⟩ hw, hd⟩
  rw [hd, Complex.ofReal_zero, add_zero] at hz
  linear_combination hz

/-- A jointly continuous expression at inverse parameter zero has the required
local uniform limit in its spatial variable. -/
private theorem inverse_parameter_limit (P : ℂ × ℂ → ℂ) (hP : Continuous P)
    (F : ℝ → ℂ → ℂ) (f : ℂ → ℂ) (hzero : ∀ z, P (0,z) = f z)
    (hformula : ∀ d : ℝ, d ≠ 0 → ∀ z, P ((d:ℂ)⁻¹,z) = F d z) :
    TendstoLocallyUniformly F f (comap (fun d : ℝ => |d|) atTop) := by
  let L := comap (fun d : ℝ => |d|) atTop
  have habs : Tendsto (fun d : ℝ => |d|) L atTop := tendsto_comap
  have hinv : Tendsto (fun d : ℝ => (d:ℂ)⁻¹) L (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Function.comp_def, norm_inv, Complex.norm_real, Real.norm_eq_abs] using
      tendsto_inv_atTop_zero.comp habs
  have hne : ∀ᶠ d : ℝ in L, d ≠ 0 :=
    (habs.eventually_gt_atTop 0).mono fun _ h => abs_pos.mp h
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro z
  have hfst : Tendsto (fun t : ℝ × ℂ => P (0,t.2)) (L ×ˢ 𝓝 z) (𝓝 (P (0,z))) :=
    hP.continuousAt.tendsto.comp (tendsto_const_nhds.prodMk_nhds tendsto_snd)
  have hsnd : Tendsto (fun t : ℝ × ℂ => P ((t.1:ℂ)⁻¹,t.2)) (L ×ˢ 𝓝 z) (𝓝 (P (0,z))) :=
    hP.continuousAt.tendsto.comp ((hinv.comp tendsto_fst).prodMk_nhds tendsto_snd)
  apply ((hfst.prodMk_nhds hsnd).mono_right (nhds_le_uniformity _)).congr'
  filter_upwards [tendsto_fst.eventually hne] with t ht
  simp only [hzero, hformula t.1 ht]

theorem quartic_pencil_large_parameter_limits :
    TendstoLocallyUniformly (fun (d : ℝ) (z : ℂ) => (contactPencilPoly d).eval z / (d:ℂ)^2)
      quarticDen (comap (fun d : ℝ => |d|) atTop) ∧
    TendstoLocallyUniformly (fun (d : ℝ) (t : ℂ) => (contactPencilPoly d).eval ((d:ℂ)*t)/(d:ℂ)^4)
      (fun t => 4*t^2*(3*t+1)*(t+1)) (comap (fun d : ℝ => |d|) atTop) := by
  constructor
  · apply inverse_parameter_limit (fun (v : ℂ × ℂ) =>
      (2*v.2*v.1+1)^2*(4*v.2^2+4*v.2+2) - v.1^2*(4*v.2^4-4*v.2^2+3)) (by fun_prop)
    · intro z; simp [quarticDen]
    · intro d hd z
      rw [contactPencilPoly_eval]
      field_simp [Complex.ofReal_ne_zero.mpr hd]
  · apply inverse_parameter_limit (fun (v : ℂ × ℂ) =>
      (2*v.2+1)^2*(4*v.2^2+4*v.2*v.1+2*v.1^2) -
        (4*v.2^4-4*v.2^2*v.1^2+3*v.1^4)) (by fun_prop)
    · intro t; dsimp; ring
    · intro d hd t
      rw [contactPencilPoly_eval]
      field_simp [Complex.ofReal_ne_zero.mpr hd]

#print axioms quartic_contact_square_alternatives
#print axioms quartic_pencil_line_identification
#print axioms quartic_pencil_large_parameter_limits

end Turan
