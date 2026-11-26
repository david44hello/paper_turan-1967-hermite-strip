module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Defs
public import Turan.RouteDefs
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Convex.Function

@[expose] public section

noncomputable section
namespace Turan

/-- The explicit shifted nodes and their Vieta data. -/
theorem quintic_shifted_node_identities (S : ℝ) :
    let X := (S - 1) / 2
    let s := Real.sqrt (1 + S ^ 2) / 2
    let Zplus := (S + Real.sqrt (S ^ 2 + 1)) / 2
    let Zminus := (S - Real.sqrt (S ^ 2 + 1)) / 2
    X + s = Zplus - 1 / 2 ∧ X - s = Zminus - 1 / 2 ∧
      Zplus + Zminus = S ∧ Zplus * Zminus = -(1 / 4) ∧ Zminus < Zplus := by
  dsimp only
  rw [add_comm 1 (S ^ 2)]
  have hp : 0 < S ^ 2 + 1 := by positivity
  have hs := Real.sq_sqrt hp.le
  refine ⟨by ring, by ring, by ring, by nlinarith only [hs], ?_⟩
  linarith [Real.sqrt_pos.2 hp]

/-- Convexity and endpoint values of the derivative of the node cubic. -/
theorem quintic_node_derivative_test :
    let f := fun S : ℝ => 2 * S ^ 3 - 5 * S ^ 2 - 4 * S + 1
    let d := fun S : ℝ => 6 * S ^ 2 - 10 * S - 4
    (∀ S, HasDerivAt f (d S) S) ∧ ConvexOn ℝ Set.univ d ∧
      d 0 = -4 ∧ d (1 / 4) = -(49 / 8) ∧
      ∀ S ∈ Set.Icc 0 (1 / 4), d S < 0 := by
  dsimp only
  refine ⟨?_, ⟨convex_univ, ?_⟩, by norm_num, by norm_num, ?_⟩
  · intro S
    convert (((((hasDerivAt_id S).pow 3).const_mul 2).sub
      (((hasDerivAt_id S).pow 2).const_mul 5)).sub ((hasDerivAt_id S).const_mul 4)).add_const 1
      using 1 <;> simp
    ring
  · intro x _ y _ a b ha hb hab
    obtain rfl : b = 1 - a := by linarith
    simp only [smul_eq_mul]
    nlinarith only [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))]
  · intro S ⟨h₀, h₁⟩
    nlinarith [mul_nonneg h₀ (sub_nonneg.mpr h₁)]

/-- Both strict comparisons for the centered cotangent quotient. -/
theorem quintic_cot_quotient_monotonicity :
    let q := fun y s : ℝ => (y ^ 2 - s ^ 2) / (2 * y * s)
    (∀ s : ℝ, 0 < s → StrictMonoOn (fun y => q y s) (Set.Ioi 0)) ∧
      ∀ y : ℝ, 0 < y → StrictAntiOn (q y) (Set.Ioi 0) := by
  let q (y s : ℝ) := (y ^ 2 - s ^ 2) / (2 * y * s)
  change (∀ s, 0 < s → StrictMonoOn (fun y => q y s) (Set.Ioi 0)) ∧ _
  have form (y s : ℝ) (hy : 0 < y) (hs : 0 < s) : q y s = (y / s - s / y) / 2 := by
    dsimp [q]
    field_simp
  have inc (s : ℝ) (hs : 0 < s) : StrictMonoOn (fun y => q y s) (Set.Ioi 0) := by
    intro a ha b hb hab
    change q a s < q b s
    rw [form a s ha hs, form b s hb hs]
    linarith [div_lt_div_of_pos_right hab hs, div_lt_div_of_pos_left hs ha hab]
  refine ⟨inc, ?_⟩
  intro y hy a ha b hb hab
  change q y b < q y a
  have h := inc y hy ha hb hab
  change q a y < q b y at h
  rw [form a y ha hy, form b y hb hy] at h
  rw [form y a hy ha, form y b hy hb]
  linarith

/-- Count indexed roots, with multiplicity, before selecting a triple. -/
theorem quintic_initial_upper_count (X s : ℝ) (z : Fin 5 → ℂ)
    (hs₀ : 1 / 2 < s) (hs₁ : s < 511 / 1000)
    (hh : ∀ i, 87 / 100 ≤ |(z i).im|) (hz : ∑ i, z i = 0)
    (hsum : Real.pi ≤ ∑ i, intervalAngle (X - s) (X + s) (z i)) :
    let n := (Finset.univ.filter (fun i : Fin 5 => 0 < (z i).im)).card
    n = 3 ∨ n = 4 := by
  classical
  let upper := Finset.univ.filter (fun i : Fin 5 => 0 < (z i).im)
  change upper.card = 3 ∨ upper.card = 4
  have hab : X - s ≤ X + s := by linarith
  have bound (i : Fin 5) : intervalAngle (X - s) (X + s) (z i) ≤
      if 0 < (z i).im then 3 / 2 else 0 := by
    let y := (z i).im
    have hy : y ≠ 0 := by
      intro h
      have hi := hh i
      change 87 / 100 ≤ |y| at hi
      norm_num [h] at hi
    have hd (t : ℝ) : 0 < (t - (z i).re)^2 + y^2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hy)
    have hc : Continuous (fun t : ℝ => y / ((t - (z i).re)^2 + y^2)) :=
      continuous_const.div (by fun_prop) (fun t => (hd t).ne')
    have cmp (c : ℝ) (h : ∀ t : ℝ, y / ((t - (z i).re)^2 + y^2) ≤ c) :
        intervalAngle (X - s) (X + s) (z i) ≤ (X + s - (X - s)) * c := by
      simpa only [intervalAngle, intervalIntegral.integral_const, smul_eq_mul, y] using
        (intervalIntegral.integral_mono (μ := MeasureTheory.volume) hab (hc.intervalIntegrable _ _) intervalIntegrable_const h)
    split_ifs with h
    · have hb : 87 / 100 ≤ y := by simpa [y, abs_of_pos h] using hh i
      have he := cmp (4 / 3) (fun t => (div_le_iff₀ (hd t)).mpr (by
        nlinarith [mul_nonneg (show 0 ≤ y by exact h.le) (sub_nonneg.mpr hb),
          sq_nonneg (t - (z i).re)]))
      linarith
    · simpa using cmp 0 (fun t => div_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) (hd t).le)
  have htotal : Real.pi ≤ (upper.card : ℝ) * (3 / 2) := by
    simpa [Finset.sum_ite, upper] using hsum.trans (Finset.sum_le_sum (fun i _ => bound i))
  have hmin : 2 < upper.card := by
    by_contra! hc
    have hc' : (upper.card : ℝ) ≤ 2 := by exact_mod_cast hc
    linarith [Real.pi_gt_three]
  have hmax : upper.card < 5 := by
    by_contra! hc
    have hall : upper = Finset.univ := Finset.eq_of_subset_of_card_le
      (Finset.subset_univ _) (by simpa using hc)
    have hp := Finset.filter_eq_self.mp hall
    have him := congrArg Complex.im hz
    rw [Complex.im_sum, Complex.zero_im] at him
    exact (Finset.sum_pos hp Finset.univ_nonempty).ne' him
  omega

#print axioms quintic_shifted_node_identities
#print axioms quintic_node_derivative_test
#print axioms quintic_cot_quotient_monotonicity
#print axioms quintic_initial_upper_count

end Turan
