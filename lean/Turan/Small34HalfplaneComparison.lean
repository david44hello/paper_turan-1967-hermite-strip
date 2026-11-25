-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Small34EnvelopeDefs
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

noncomputable section
open Real Set Filter
open scoped Topology

namespace Turan

/-- Rotate and translate the domain so that the boundary becomes the imaginary axis. -/
private def liftAngle (l r : ℝ) (w : ℂ) : ℂ :=
  (Complex.log (w + (5 / 7 : ℂ) + r * Complex.I) -
   Complex.log (w + (5 / 7 : ℂ) + l * Complex.I)) * (-Complex.I)

private theorem liftAngle_diff (l r : ℝ) {w : ℂ} (hw : 0 ≤ w.re) :
    DifferentiableAt ℂ (liftAngle l r) w := by
  have edge (t : ℝ) : DifferentiableAt ℂ
      (fun v : ℂ => Complex.log (v + (5 / 7 : ℂ) + t * Complex.I)) w := by
    apply DifferentiableAt.clog (by fun_prop)
    left
    norm_num [Complex.add_re, Complex.mul_I_re]
    linarith
  exact ((edge r).sub (edge l)).mul_const _

private theorem liftAngle_re (l r : ℝ) {w : ℂ} (hw : 0 ≤ w.re) :
    (liftAngle l r w).re = small34Angle l r ⟨-w.im, w.re + 5/7⟩ := by
  have edge (t : ℝ) : (w + (5/7 : ℂ) + t * Complex.I).arg =
      arctan ((t - -w.im) / (w.re + 5/7)) := by
    symm
    apply arctan_eq_of_tan_eq
    · rw [Complex.tan_arg]
      norm_num [Complex.add_im, Complex.add_re, Complex.mul_I_re, Complex.mul_I_im, add_comm]
    · apply abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (.inl ?_))
      norm_num [Complex.add_re, Complex.mul_I_re]
      linarith
  simp [liftAngle, small34Angle, mul_neg, Complex.sub_im, Complex.log_im, edge]

/-- A bounded real part on a right half-plane is controlled by its boundary values. -/
private theorem re_le_boundary (F : ℂ → ℂ) (K M : ℝ)
    (hd : ∀ w : ℂ, 0 ≤ w.re → DifferentiableAt ℂ F w)
    (hK : ∀ w : ℂ, 0 ≤ w.re → (F w).re ≤ K)
    (hM : ∀ x : ℝ, (F (x * Complex.I)).re ≤ M) {w : ℂ} (hw : 0 ≤ w.re) :
    (F w).re ≤ M := by
  let f (v : ℂ) := Complex.exp (F v)
  have hnorm (v : ℂ) : ‖f v‖ = Real.exp (F v).re := Complex.norm_exp _
  have hdiff : DiffContOnCl ℂ f {v : ℂ | 0 < v.re} := by
    apply DifferentiableOn.diffContOnCl
    rw [Complex.closure_setOfPred_lt_re]
    intro v hv
    exact ((hd v hv).cexp).differentiableWithinAt
  apply Real.exp_le_exp.mp
  rw [← hnorm]
  apply PhragmenLindelof.right_half_plane_of_bounded_on_real hdiff _ _ _ hw
  · refine ⟨0, by norm_num, 0, Asymptotics.IsBigO.of_bound (Real.exp K) ?_⟩
    apply eventually_inf_principal.2 (Eventually.of_forall fun v hv => ?_)
    simpa [hnorm] using Real.exp_le_exp.mpr (hK v (le_of_lt hv))
  · apply isBoundedUnder_of_eventually_le (a := Real.exp K)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [hnorm]
    exact Real.exp_le_exp.mpr (hK _ (by simpa using hx))
  · intro x
    rw [hnorm]
    exact Real.exp_le_exp.mpr (hM x)

private theorem envelope_bounds (a b c d e f : ℝ) (z : ℂ) (hz : 5/7 ≤ z.im) :
    let g := fun v => 5 * small34Angle a b v - 4 * small34Angle c d v + 2 * small34Angle e f v
    (∀ k : ℝ, g z - k ≤ sSup (range fun x : ℝ => g ⟨x, 5/7⟩ - k)) ∧
      sInf (range fun x : ℝ => g ⟨x, 5/7⟩) ≤ g z := by
  intro g
  let F (v : ℂ) := 5 * liftAngle a b v - 4 * liftAngle c d v + 2 * liftAngle e f v
  have hd (v : ℂ) (hv : 0 ≤ v.re) : DifferentiableAt ℂ F v :=
    (((liftAngle_diff a b hv).const_mul 5).sub ((liftAngle_diff c d hv).const_mul 4)).add
      ((liftAngle_diff e f hv).const_mul 2)
  have hre (v : ℂ) (hv : 0 ≤ v.re) : (F v).re = g ⟨-v.im, v.re + 5/7⟩ := by
    norm_num [F, g, Complex.add_re, Complex.sub_re, Complex.mul_re, liftAngle_re _ _ hv]
  have line (x : ℝ) : (F (x * Complex.I)).re = g ⟨-x, 5/7⟩ := by
    simpa using hre (x * Complex.I) (by simp)
  have ang (l r : ℝ) (v : ℂ) : -π ≤ small34Angle l r v ∧ small34Angle l r v ≤ π := by
    unfold small34Angle
    have hr := arctan_mem_Ioo ((r-v.re)/v.im)
    have hl := arctan_mem_Ioo ((l-v.re)/v.im)
    constructor <;> linarith only [hr.1, hr.2, hl.1, hl.2]
  have hg (v : ℂ) : -(11*π) ≤ g v ∧ g v ≤ 11*π := by
    dsimp [g]
    constructor <;> linarith [ang a b v, ang c d v, ang e f v]
  let w : ℂ := ⟨z.im - 5/7, -z.re⟩
  have hw : 0 ≤ w.re := sub_nonneg.mpr hz
  have hval : (F w).re = g z := by simpa [w] using hre w hw
  constructor
  · intro k
    let S := range fun x : ℝ => g ⟨x, 5/7⟩ - k
    have hS : BddAbove S := ⟨11*π-k, by rintro _ ⟨x, rfl⟩; exact sub_le_sub_right (hg _).2 _⟩
    have h := re_le_boundary F (11*π) (sSup S + k) hd
      (fun v hv => (hre v hv).trans_le (hg _).2) (fun x => by
        rw [line]
        have hx : g ⟨-x, 5/7⟩ - k ≤ sSup S := le_csSup hS (mem_range_self (-x))
        linarith only [hx]) hw
    linarith [hval]
  · let S := range fun x : ℝ => g ⟨x, 5/7⟩
    have hS : BddBelow S := ⟨-(11*π), by rintro _ ⟨x, rfl⟩; exact (hg _).1⟩
    have h := re_le_boundary (fun v => -F v) (11*π) (-sInf S) (fun v hv => (hd v hv).neg)
      (fun v hv => by rw [Complex.neg_re, hre v hv]; linarith [(hg ⟨-v.im, v.re + 5/7⟩).1])
      (fun x => by rw [Complex.neg_re, line]; exact neg_le_neg (csInf_le hS (mem_range_self (-x)))) hw
    simpa [hval] using h

/-- The same boundary extrema control the entire closed half-plane. -/
theorem small34_halfplane_boundary_bounds (z : ℂ) (hz : 5/7 ≤ z.im) :
    small34GUpper z - arctan (1/44) ≤
      sSup (range fun x : ℝ => small34GUpper ⟨x, 5/7⟩ - arctan (1/44)) ∧
    sInf (range fun x : ℝ => small34GLower ⟨x, 5/7⟩) ≤ small34GLower z := by
  exact ⟨(envelope_bounds _ _ _ _ _ _ z hz).1 _, (envelope_bounds _ _ _ _ _ _ z hz).2⟩

#print axioms small34_halfplane_boundary_bounds

end Turan
