module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Constants

@[expose] public section

namespace Turan

/-- The endpoints certify the twelve digits printed beside the exact formula. -/
theorem height_decimal :
    (903669747226 : ℝ)/10^12 < h ∧ h < (903669747227 : ℝ)/10^12 := by
  obtain ⟨hu, hu_pos, _, _, hh, hh_pos⟩ := constants_spec
  let lo : ℝ := 1490179094958303 / 10^16
  let hi : ℝ := 1490179094958304 / 10^16
  have mono : StrictMono (fun x : ℝ => 32 * x^3 + 6*x) := by
    intro a b hab
    have := (Odd.strictMono_pow (by decide : Odd 3)) hab
    dsimp
    linarith
  have hlo : lo < u := mono.lt_iff_lt.mp (by
    change 32 * lo^3 + 6*lo < 32 * u^3 + 6*u
    rw [hu]
    norm_num [lo])
  have hhi : u < hi := mono.lt_iff_lt.mp (by
    change 32 * u^3 + 6*u < 32 * hi^3 + 6*hi
    rw [hu]
    norm_num [hi])
  have hpos : 0 ≤ h := by linarith
  constructor
  · apply (sq_lt_sq₀ (by norm_num) hpos).mp
    rw [hh]
    have := (sq_lt_sq₀ (by norm_num [lo] : 0 ≤ lo) hu_pos.le).mpr hlo
    norm_num [lo] at this ⊢
    linarith
  · apply (sq_lt_sq₀ hpos (by norm_num)).mp
    rw [hh]
    have := (sq_lt_sq₀ hu_pos.le (by norm_num [hi] : 0 ≤ hi)).mpr hhi
    norm_num [hi] at this ⊢
    linarith

end Turan
