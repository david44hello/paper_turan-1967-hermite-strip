-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.SlotDefs

open Polynomial Filter Metric

namespace Turan

theorem slot_flat_lift (F G : ℕ → Polynomial ℂ) (heF : escapesDisks F) (heG : escapesDisks G)
    (hr : TendstoLocallyUniformly (fun j z => (G j).eval z / (F j).eval z) (fun _ => 1) atTop)
    (hg : TendstoLocallyUniformly (fun j z => (G j).eval z / (G j).eval 0) (fun _ => 1) atTop) :
    TendstoLocallyUniformly (fun j z => (F j).eval z / (F j).eval 0) (fun _ => 1) atTop := by
  have h₀ : TendstoLocallyUniformly (fun j (_ : ℂ) => (G j).eval 0 / (F j).eval 0)
      (fun _ => 1) atTop := hr.comp (fun _ : ℂ => 0) continuous_const
  have hi := hr.inv₀ continuous_const (fun _ => one_ne_zero)
  have hprod := (hg.mul₀ h₀ continuous_const continuous_const).mul₀ hi
    (continuous_const.mul continuous_const) continuous_const
  change TendstoLocallyUniformly (fun j z => (G j).eval z / (G j).eval 0 *
    ((G j).eval 0 / (F j).eval 0) * ((G j).eval z / (F j).eval z)⁻¹)
    (fun _ => (1 : ℂ) * 1 * 1⁻¹) atTop at hprod
  simp only [inv_one, mul_one] at hprod
  apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
  intro K hK
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  apply (tendstoLocallyUniformly_iff_forall_isCompact.mp hprod K hK).congr
  filter_upwards [heF R hR, heG R hR] with j hF hG
  intro z hz
  have hzR : ‖z‖ ≤ R := by simpa using mem_closedBall.mp (hKR hz)
  have hzero : ‖(0 : ℂ)‖ ≤ R := by simpa using hR.le
  dsimp only
  rw [inv_div]
  field_simp [hF 0 hzero, hG 0 hzero, hF z hzR, hG z hzR]

end Turan
