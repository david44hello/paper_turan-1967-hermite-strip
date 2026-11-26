module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Tactic

@[expose] public section
open Filter Metric Set
open scoped Topology
noncomputable section
namespace Turan

private theorem half_disk_side (f : ℂ → ℂ) (y B : ℝ) (c : ℂ) (T : ℝ)
    (ha : ∀ z : ℂ, y ≤ z.im → AnalyticAt ℂ f z)
    (hline : ∀ z : ℂ, z.im=y → (f z).im ≤ B)
    (hfar : ∀ z : ℂ, T ≤ ‖z-c‖ → (f z).im < B) :
    (∀ R ≥ T, ∀ z : ℂ, y ≤ z.im → ‖z-c‖ ≤ R → (f z).im ≤ B) ∧
    (∀ z : ℂ, y ≤ z.im → (f z).im ≤ B) ∧
    (∀ z : ℂ, y < z.im → (f z).im < B) := by
  let G := fun z => Complex.exp (-(f z)*Complex.I)
  have hnorm (z : ℂ) : ‖G z‖ = Real.exp (f z).im := by simp [G, Complex.norm_exp, Complex.mul_I_re]
  have hG (z : ℂ) (hz : y ≤ z.im) : DifferentiableAt ℂ G z :=
    ((ha z hz).differentiableAt.neg.mul_const Complex.I).cexp
  let H := {z : ℂ | y ≤ z.im}
  have hH : IsClosed H := isClosed_le continuous_const Complex.continuous_im
  have hbound (R : ℝ) (hR : T ≤ R) (z : ℂ) (hz : y ≤ z.im) (hd : ‖z-c‖ ≤ R) : (f z).im ≤ B := by
    let D := closedBall c R ∩ H
    have hcl : IsClosed D := isClosed_closedBall.inter hH
    have hmem : z ∈ D := ⟨by simpa [mem_closedBall, dist_eq_norm] using hd, hz⟩
    apply Real.exp_le_exp.mp
    rw [← hnorm]
    apply Complex.norm_le_of_forall_mem_frontier_norm_le
      (U := D) (Metric.isBounded_closedBall.subset inter_subset_left)
    · apply DifferentiableOn.diffContOnCl
      rw [hcl.closure_eq]
      exact fun w hw => (hG w hw.2).differentiableWithinAt
    · intro w hw
      rw [hnorm, Real.exp_le_exp]
      rcases frontier_inter_subset (closedBall c R) H hw with h | h
      · have hw' := mem_sphere.mp (frontier_closedBall_subset_sphere h.1)
        exact (hfar _ (hR.trans_eq (by simpa [dist_eq_norm] using hw'.symm))).le
      · exact hline _ ((frontier_le_subset_eq continuous_const Complex.continuous_im h.2).symm)
    · exact subset_closure hmem
  have hup (z : ℂ) (hz : y ≤ z.im) := hbound (max T ‖z-c‖) (le_max_left ..) z hz (le_max_right ..)
  refine ⟨hbound, hup, ?_⟩
  intro z hz
  apply lt_of_le_of_ne (hup z hz.le)
  intro he
  let U := {w : ℂ | y < w.im}
  have hmax : IsMaxOn (norm ∘ G) U z := by
    intro w hw
    change ‖G w‖ ≤ ‖G z‖
    rw [hnorm, hnorm, he, Real.exp_le_exp]
    exact hup w (le_of_lt hw)
  have hconst := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn
    (convex_halfSpace_im_gt y).isPreconnected (isOpen_lt continuous_const Complex.continuous_im)
    (fun w hw => (hG w (le_of_lt hw)).differentiableWithinAt) hz hmax
  let w : ℂ := ⟨c.re+T, y+1⟩
  have hw : y < w.im := by dsimp [w]; linarith
  have hdist : T ≤ ‖w-c‖ := by
    have ha := Complex.re_le_norm (w-c)
    simpa [w,Complex.sub_re] using ha
  have hc : ‖G w‖ = ‖G z‖ := hconst hw
  rw [hnorm, hnorm, he] at hc
  exact (hfar w hdist).ne (Real.exp_injective hc)

theorem imaginary_half_disk_maximum (f : ℂ → ℂ) (y B : ℝ) (hB : 0 < B)
    (ha : ∀ z : ℂ, y ≤ z.im → AnalyticAt ℂ f z)
    (hline : ∀ z : ℂ, z.im=y → |(f z).im| ≤ B)
    (hinf : Tendsto (fun z => (f z).im) (cocompact ℂ) (𝓝 0)) :
    let c := (y:ℂ)*Complex.I
    (∃ R₀ > (0:ℝ), ∀ R ≥ R₀,
      (∀ z : ℂ, y ≤ z.im → ‖z-c‖=R → |(f z).im| < B) ∧
      (∀ z : ℂ, y ≤ z.im → ‖z-c‖≤R → |(f z).im| ≤ B)) ∧
    (∀ z : ℂ, y ≤ z.im → |(f z).im| ≤ B) ∧
    (∀ z : ℂ, y < z.im → |(f z).im| < B) := by
  dsimp only
  let c := (y:ℂ)*Complex.I
  have hsmall := (Metric.tendsto_nhds.mp hinf) B hB
  rw [← Metric.cobounded_eq_cocompact] at hsmall
  obtain ⟨T, _, ht⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp hsmall
  let R₀ := max 1 (T+‖c‖)
  have hfar (z : ℂ) (hz : R₀ ≤ ‖z-c‖) : |(f z).im| < B := by
    have h : T ≤ ‖z‖ := by linarith only [le_max_right (1:ℝ) (T+‖c‖), hz, norm_sub_le z c]
    simpa [Real.dist_eq] using ht h
  obtain ⟨hfill,hup,hstrict⟩ := half_disk_side f y B c R₀ ha
    (fun z hz => (abs_le.mp (hline z hz)).2) (fun z hz => (abs_lt.mp (hfar z hz)).2)
  obtain ⟨hfill',hlo,hstrict'⟩ := half_disk_side (fun z => -f z) y B c R₀
    (fun z hz => (ha z hz).neg)
    (fun z hz => by simpa using (neg_le.mpr (abs_le.mp (hline z hz)).1))
    (fun z hz => by simpa using (neg_lt.mpr (abs_lt.mp (hfar z hz)).1))
  refine ⟨⟨R₀, (by exact lt_of_lt_of_le zero_lt_one (le_max_left ..)), fun R hR =>
    ⟨fun z _ hz => hfar z (hR.trans_eq hz.symm), fun z hy hd => ?_⟩⟩, ?_, ?_⟩
  · exact abs_le.mpr ⟨by simpa using neg_le_neg (hfill' R hR z hy hd), hfill R hR z hy hd⟩
  · intro z hz
    exact abs_le.mpr ⟨by simpa using neg_le_neg (hlo z hz), hup z hz⟩
  · intro z hz
    exact abs_lt.mpr ⟨by simpa using neg_lt_neg (hstrict' z hz), hstrict z hz⟩

end Turan
