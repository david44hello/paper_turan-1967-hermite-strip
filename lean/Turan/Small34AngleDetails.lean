-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.IntervalAngles
import Turan.Degree
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

noncomputable section
open Polynomial Real Set

namespace Turan

/-- The first variable is the squared displacement from the midpoint.
The second comparison concerns the value at the midpoint, as a function of height. -/
theorem small34_cot_monotonicity {s : ℝ} (hs : 0 < s) :
    (∀ h : ℝ, 0 < h → StrictMono (fun u : ℝ => (u + h^2 - s^2) / (2*h*s))) ∧
    StrictMonoOn (fun h : ℝ => (h^2 - s^2) / (2*h*s)) (Ioi 0) := by
  constructor
  · intro h hh u v huv
    exact (div_lt_div_iff_of_pos_right (by positivity)).mpr (by linarith)
  · intro a ha b hb hab
    have ha' : 0 < a := ha
    have hb' : 0 < b := hb
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [mul_pos (mul_pos (by linarith : 0 < 2*s) (sub_pos.mpr hab))
      (show 0 < a*b+s^2 by positivity)]

/-- The sharp envelope at minimum height, on either side of the real axis. -/
theorem small34_cot_envelope {l r h : ℝ} (hlr : l < r) (hh : 0 < h)
    (z : ℂ) (hz : h ≤ |z.im|) :
    let s := (r-l)/2
    (h^2 - s^2) / (2*h*s) ≤ Real.cot |intervalAngle l r z| ∧
    (h^2 - s^2) / (2*h*s) = Real.cot (2 * arctan (s/h)) := by
  let s := (r-l)/2
  have hs : 0<s := by dsimp [s]; linarith
  have hy : 0 < |z.im| := hh.trans_le hz
  rw [interval_angle_cot l r hlr z (abs_pos.mp hy)]
  change (h^2-s^2)/(2*h*s) ≤ _ ∧ _ = _
  constructor
  · calc
      _ ≤ (|z.im|^2 - s^2)/(2 * |z.im| * s) :=
        (small34_cot_monotonicity hs).2.monotoneOn hh hy hz
      _ ≤ _ := by rw [sq_abs]; gcongr; nlinarith [sq_nonneg (z.re-(l+r)/2)]
  · change (h^2-s^2)/(2*h*s) = cot (2*arctan (s/h))
    have hcot : ∀ x : ℝ, cot x = (tan x)⁻¹ := fun x => by
      rw [cot_eq_cos_div_sin,tan_eq_sin_div_cos,inv_div]
    rw [hcot,tan_two_mul,tan_arctan,inv_div]
    field_simp [hh.ne',hs.ne']

/-- The three displayed leading coefficients after division by 16b. -/
theorem small34_monic_expansion (a b : ℂ) (hb : b ≠ 0) :
    let p := C (16*b)⁻¹ * family 3 4 a b
    p = X^4 + C (a/(2*b)) * X^3 - C 3 * X^2
      + C ((2-12*a)/(16*b)) * X + C ((1+12*b)/(16*b)) := by
  apply Polynomial.funext
  intro z
  norm_num [family,hermite,nsmul_eq_mul,eval_add,eval_pow,eval_sub,eval_mul]
  field_simp [hb]
  ring

/-- A real lift exists with the principal initial value.
Every continuous lift has the same real increment, counting roots with multiplicity. -/
theorem small34_continuous_argument_change (a b : ℂ) (hb : b ≠ 0)
    {l r : ℝ} (hlr : l ≤ r)
    (hroots : ∀ w ∈ (family 3 4 a b).roots, w.im ≠ 0) :
    let p := family 3 4 a b
    let isLift := fun θ : ℝ → ℝ =>
      ContinuousOn θ (Icc l r) ∧
      ∀ t ∈ Icc l r, (θ t : Real.Angle) = ((p.eval (t : ℂ)).arg : Real.Angle)
    (∃ θ, isLift θ ∧ θ l = (p.eval (l : ℂ)).arg) ∧
    ∀ θ, isLift θ → θ r - θ l = (p.roots.map (intervalAngle l r)).sum := by
  let p := family 3 4 a b
  have hp : p ≠ 0 := by
    have h : p.natDegree = 4 := by simp [p,family_degree 3 4 (by decide) (by decide),hb]
    intro he; simp [he] at h
  have hf (t : ℝ) : p.eval (t:ℂ) ≠ 0 :=
    fun he => hroots _ ((mem_roots hp).mpr he) rfl
  obtain ⟨A,hA,hval,hinc⟩ := polynomial_argument_on_real_axis p hf
  have hphase (t : ℝ) : (A t : Angle) = ((p.eval (t:ℂ)).arg : Angle) := by
    symm
    apply Complex.arg_coe_angle_eq_iff_eq_toReal.mpr
    rw [Angle.toReal_coe, ← Complex.arg_exp_mul_I, hval, div_eq_mul_inv, ← Complex.ofReal_inv,
      Complex.arg_mul_real (inv_pos.mpr (norm_pos_iff.mpr (hf t)))]
  let argL := (p.eval (l:ℂ)).arg
  let B := fun t => A t - A l + argL
  have hB (t : ℝ) : (B t : Angle) = ((p.eval (t:ℂ)).arg : Angle) := by
    simp only [B,Angle.coe_add,Angle.coe_sub,argL,← hphase]
    abel
  refine ⟨⟨B, ⟨((hA.sub continuous_const).add continuous_const).continuousOn, fun t _ => hB t⟩,
      by simp [B,argL,p]⟩, ?_⟩
  rintro θ ⟨hcont,ht⟩
  have hcov : IsCoveringMap ((↑) : ℝ → Angle) := AddCircle.isCoveringMap_coe _
  have hconst := hcov.constOn_of_comp isPreconnected_Icc (hcont.sub hA.continuousOn)
    (fun t ht₁ v hv => by
      change ((θ t - A t : ℝ) : Angle) = ((θ v - A v : ℝ) : Angle)
      simp only [Angle.coe_sub,ht t ht₁,ht v hv,hphase,p,sub_self])
    (left_mem_Icc.mpr hlr) (right_mem_Icc.mpr hlr)
  change θ l - A l = θ r - A r at hconst
  rcases hlr.eq_or_lt with rfl | hlt
  · have hself : intervalAngle l l = fun _ => 0 := by funext z; simp [intervalAngle]
    simp [hself]
  · linarith only [hconst,hinc l r hlt]

#print axioms small34_cot_monotonicity
#print axioms small34_cot_envelope
#print axioms small34_monic_expansion
#print axioms small34_continuous_argument_change

end Turan
