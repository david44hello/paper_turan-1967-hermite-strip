-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.DeltaDifferential
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

noncomputable section
open Set Filter
open scoped Topology
namespace Turan

def realContactQuartic (t : ℝ) : ℝ := 12*t^4 + 16*t^3 + 12*t^2 - 3

/-- The derivative argument counts the two real roots independently of the
already verified isolation of the upper complex root. -/
theorem quartic_real_sign_intervals :
    (∀ t : ℝ, HasDerivAt realContactQuartic (24*t*(2*t^2+2*t+1)) t) ∧
    StrictAntiOn realContactQuartic (Iic 0) ∧ StrictMonoOn realContactQuartic (Ici 0) ∧
    (∃! t : ℝ, t < 0 ∧ realContactQuartic t = 0) ∧
    (∃! t : ℝ, 0 < t ∧ realContactQuartic t = 0) := by
  have hder (t : ℝ) : HasDerivAt realContactQuartic (24*t*(2*t^2+2*t+1)) t := by
    unfold realContactQuartic
    apply ((((((hasDerivAt_id t).fun_pow 4).const_mul 12).add
      (((hasDerivAt_id t).fun_pow 3).const_mul 16)).add
      (((hasDerivAt_id t).fun_pow 2).const_mul 12)).sub_const 3).congr_deriv
    dsimp
    ring
  have hcont : Continuous realContactQuartic := continuous_iff_continuousAt.mpr
    fun t => (hder t).continuousAt
  have hpos (t : ℝ) : 0 < 2*t^2+2*t+1 := by nlinarith [sq_nonneg (t+1/2)]
  have hleft : StrictAntiOn realContactQuartic (Iic 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Iic _) hcont.continuousOn
    intro t ht
    rw [interior_Iic, mem_Iio] at ht
    rw [(hder t).deriv]
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) ht) (hpos t)
  have hright : StrictMonoOn realContactQuartic (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _) hcont.continuousOn
    intro t ht
    rw [interior_Ici, mem_Ioi] at ht
    rw [(hder t).deriv]
    exact mul_pos (mul_pos (by norm_num) ht) (hpos t)
  obtain ⟨L, hL, hzeroL⟩ := intermediate_value_Icc' (by norm_num : (-27/40 : ℝ) ≤ -2/3)
    hcont.continuousOn (show (0:ℝ) ∈ Icc (realContactQuartic (-2/3)) (realContactQuartic (-27/40)) by
      norm_num [realContactQuartic])
  obtain ⟨R, hR, hzeroR⟩ := intermediate_value_Icc (by norm_num : (3/8 : ℝ) ≤ 2/5)
    hcont.continuousOn (show (0:ℝ) ∈ Icc (realContactQuartic (3/8)) (realContactQuartic (2/5)) by
      norm_num [realContactQuartic])
  have hLn : L < 0 := lt_of_le_of_lt hL.2 (by norm_num)
  have hRp : 0 < R := lt_of_lt_of_le (by norm_num) hR.1
  exact ⟨hder, hleft, hright, ⟨L, ⟨hLn,hzeroL⟩, fun s hs =>
    hleft.injOn hs.1.le hLn.le (hs.2.trans hzeroL.symm)⟩,
    ⟨R, ⟨hRp,hzeroR⟩, fun s hs => hright.injOn hs.1.le hRp.le (hs.2.trans hzeroR.symm)⟩⟩

theorem quartic_squared_height_vieta_comparison (w : ℂ)
    (hw : 0 < w.im ∧ 12*w^4+16*w^3+12*w^2-3=0) :
    25/27 - 64/225 = (433/675 : ℝ) ∧ (16/25 : ℝ) < 433/675 ∧
    (433/675 : ℝ) < w.im^2 ∧ w.im^2 < 1 - (1/4 : ℝ) := by
  obtain ⟨hlo,hhi,_⟩ := quartic_root_height w hw
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · nlinarith [mul_self_lt_mul_self (by norm_num : (0 : ℝ) ≤ 8286/10000) hlo]
  · nlinarith [mul_self_lt_mul_self hw.1.le hhi]

/-- Exact pole characterization supplements the already proved exclusion
quartic_den_ne above height one half. -/
theorem quartic_denominator_zeros (z : ℂ) :
    quarticDen z = 0 ↔
      z = -1/2+Complex.I/2 ∨ z = -1/2-Complex.I/2 := by
  have hf : quarticDen z = (2*z+1-Complex.I)*(2*z+1+Complex.I) := by
    unfold quarticDen
    linear_combination Complex.I_sq
  rw [hf, mul_eq_zero]
  constructor
  · rintro (h | h)
    · left; linear_combination h/2
    · right; linear_combination h/2
  · rintro (rfl | rfl)
    · left; ring
    · right; ring

theorem quartic_ratio_analytic_and_pencil (w z : ℂ)
    (hw : 0<w.im ∧ 12*w^4+16*w^3+12*w^2-3=0) (hz : w.im ≤ z.im) :
    AnalyticAt ℂ quarticRatio z ∧
    ∀ d : ℝ, (2*z+(d:ℂ))^2*quarticDen z-(4*z^4-4*z^2+3)=0 ↔
      quarticRatio z=(2*z+(d:ℂ))^2 := by
  have hd := quartic_den_ne z (by linarith [(quartic_root_height w hw).1])
  constructor
  · unfold quarticRatio
    apply AnalyticAt.div
    · fun_prop
    · unfold quarticDen; fun_prop
    · exact hd
  · intro d
    rw [quarticRatio, div_eq_iff hd]
    constructor <;> intro h <;> linear_combination -h

/-- The local analytic square root with the specified sign and the derivative
of its imaginary part along the paper’s horizontal parameter. -/
theorem quartic_square_root_branch_at_contact (w : ℂ)
    (hw : 0<w.im ∧ 12*w^4+16*w^3+12*w^2-3=0) :
    ∃ ρ : ℂ → ℂ, AnalyticAt ℂ ρ w ∧ (∀ᶠ z in 𝓝 w, (ρ z)^2 = quarticRatio z) ∧
      ρ w = 2*w ∧ HasDerivAt ρ (-1) w ∧
      HasDerivAt (fun s : ℝ => (ρ (⟨s-1/2,w.im⟩ : ℂ)).im) 0 (w.re+1/2) := by
  obtain ⟨hval, hratio⟩ := quartic_ratio_contact w hw
  have hw0 : w ≠ 0 := fun e => by simpa [e] using hw.1
  let c := 2*w
  have hc : c ≠ 0 := mul_ne_zero (by norm_num) hw0
  have hcw : quarticRatio w = c^2 := by rw [hval]; dsimp [c]; ring
  let u := fun z => quarticRatio z / c^2
  have hu : u w = 1 := by simp [u,hcw,hc]
  let ρ := fun z => c * Complex.sqrt (u z)
  have hs : AnalyticAt ℂ Complex.sqrt (1:ℂ) :=
    Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)
  have ha := (quartic_ratio_analytic_and_pencil w w hw le_rfl).1
  have hau : AnalyticAt ℂ u w := ha.div analyticAt_const (pow_ne_zero 2 hc)
  have has : AnalyticAt ℂ ρ w := analyticAt_const.mul (hs.comp_of_eq hau hu)
  have hρ : ρ w = c := by simp [ρ,hu]
  have hsquare (z : ℂ) : ρ z ^ 2 = quarticRatio z := by
    rw [show ρ z = c * (u z).sqrt from rfl, mul_pow,
      show (u z).sqrt ^ 2 = u z from Complex.cpow_nat_inv_pow _ (by decide : 2 ≠ 0)]
    dsimp [u]
    field_simp
  have hd := has.differentiableAt.hasDerivAt
  have hsqder := hd.fun_pow 2
  rw [show (fun z => ρ z ^ 2) = quarticRatio from funext hsquare] at hsqder
  have hderEq := hsqder.unique hratio
  simp [hρ, c] at hderEq
  have hneg : deriv ρ w = -1 := by
    apply (mul_right_inj' hw0).mp
    linear_combination hderEq / 4
  have hdneg := hd.congr_deriv hneg
  let x := w.re+1/2
  let z (s : ℝ) : ℂ := ⟨s-1/2,w.im⟩
  have hx : z x = w := by apply Complex.ext <;> simp [z,x]
  have hz : HasDerivAt z 1 x := by
    have h := (((hasDerivAt_id x).sub_const (1/2)).ofReal_comp).add_const (⟨0,w.im⟩ : ℂ)
    convert h using 1
    funext s
    apply Complex.ext <;> simp [z]
  have hpath : HasDerivAt (ρ ∘ z) (-1) x := by simpa using hdneg.comp_of_eq x hz hx.symm
  exact ⟨ρ, has, Filter.Eventually.of_forall hsquare, hρ, hdneg,
    by simpa [Function.comp_def,z,x] using Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hpath⟩

#print axioms quartic_real_sign_intervals
#print axioms quartic_squared_height_vieta_comparison
#print axioms quartic_denominator_zeros
#print axioms quartic_ratio_analytic_and_pencil
#print axioms quartic_square_root_branch_at_contact

end Turan
