module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.SectionTwoShifts
public import Mathlib.Analysis.Complex.Liouville

@[expose] public section

noncomputable section
open Polynomial Metric
open scoped BigOperators Classical
namespace Turan.SectionTwo

theorem polynomial_iteratedDeriv (p : Polynomial ℂ) (l : ℕ) :
    iteratedDeriv l (fun z => p.eval z) = fun z => (derivative^[l] p).eval z := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    exact funext fun z => ((derivative^[l] p).hasDerivAt z).deriv

private theorem spectral_gap {i j : ℕ} (hne : i ≠ j) : 2 ≤ |lambda i - lambda j| := by
  rcases lt_or_gt_of_ne hne with h | h
  · have h' : (i : ℝ)+1 ≤ j := by exact_mod_cast h
    unfold lambda
    exact le_trans (by linarith : 2 ≤ -(2*(i : ℝ)-2*j)) (neg_le_abs _)
  · have h' : (j : ℝ)+1 ≤ i := by exact_mod_cast h
    unfold lambda
    exact le_trans (by linarith : 2 ≤ 2*(i : ℝ)-2*j) (le_abs_self _)

private theorem step_bound (p : Polynomial ℂ) (c d z : ℂ) (l : ℕ) (L M : ℝ)
    (hc : ‖c‖ ≤ 1) (hd : ‖d‖ ≤ L) (hM : 0 ≤ M)
    (hb : ∀ t ≤ l+2, ‖(derivative^[t] p).eval z‖ ≤ M) :
    ‖(derivative^[l] (weightedShift c d p)).eval z‖ ≤ (1+2*‖z‖+L+2*l)*M := by
  rw [weightedShift_jet, norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) hc).trans
  grw [norm_add_le, norm_sub_le]
  simp only [norm_mul, Complex.norm_ofNat]
  have hd' : ‖d-2*(l:ℂ)‖ ≤ L+2*l := by
    apply (norm_sub_le _ _).trans
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_natCast]
    linarith
  have hL := (norm_nonneg d).trans hd
  calc
    _ ≤ M + 2*‖z‖*M + (L+2*l)*M := by gcongr <;> apply hb <;> omega
    _ = _ := by ring

theorem project_slot_estimate (s : ℕ) (hs : s ∈ Set.Icc 2 4) (z : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (k : Fin s → ℕ), Function.Injective k →
      ∀ (a : Fin s → ℂ) (v : Fin s),
      projectSlot k v (slotSum k a) = C (a v) * hermite (k v) ∧
      (∀ t, t ≠ v → 2 ≤ |lambda (k t) - lambda (k v)|) ∧
      ∀ M : ℝ, 0 ≤ M → (∀ w ∈ closedBall z ε, ‖(slotSum k a).eval w‖ ≤ M) →
        ‖(projectSlot k v (slotSum k a)).eval z‖ ≤ C₀ * (1 + topLambda k)^(s-1) * M := by
  let weight (i : ℕ) : ℝ := i.factorial / ε^i
  have hw (i : ℕ) : 0 ≤ weight i := by dsimp [weight]; positivity
  let W := 1 + ∑ i ∈ Finset.range 9, weight i
  let K := 17 + 2*‖z‖
  have hW : 0 < W := by dsimp [W]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K^(s-1)*W, by positivity, ?_⟩
  intro k hk a v
  refine ⟨projectSlot_slotSum k hk a v, fun t ht => spectral_gap (hk.ne ht), ?_⟩
  intro M hM hball
  let p := slotSum k a
  let L := topLambda k
  have hL : 0 ≤ L := by unfold L topLambda lambda; positivity
  let c (t : Fin s) : ℂ := (((lambda (k t)-lambda (k v) : ℝ) : ℂ))⁻¹
  let d (t : Fin s) : ℂ := lambda (k t)
  let stage (l : List (Fin s)) := l.foldr (fun t q => weightedShift (c t) (d t) q) p
  have hc (t : Fin s) (ht : t ≠ v) : ‖c t‖ ≤ 1 := by
    rw [show ‖c t‖ = _ from norm_inv _, Complex.norm_real, Real.norm_eq_abs]
    exact inv_le_one_of_one_le₀ (by linarith [spectral_gap (hk.ne ht)])
  have hd (t : Fin s) : ‖d t‖ ≤ L := by
    rw [show ‖d t‖ = _ from Complex.norm_of_nonneg (show 0 ≤ lambda (k t) by unfold lambda; positivity)]
    unfold L topLambda lambda
    gcongr
    exact Finset.le_sup (Finset.mem_univ _)
  have bound (l : List (Fin s)) (hl : ∀ t ∈ l, t ≠ v) (j : ℕ) (hj : j+2*l.length ≤ 8) :
      ‖(derivative^[j] (stage l)).eval z‖ ≤ (K*(1+L))^l.length * (W*M) := by
    induction l generalizing j with
    | nil =>
      have hj' : j ∈ Finset.range 9 := Finset.mem_range.mpr (by simp at hj; omega)
      have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hε
        p.differentiable.diffContOnCl (fun t ht => hball t (sphere_subset_closedBall ht))
      rw [polynomial_iteratedDeriv] at hC
      simp only [stage, List.foldr_nil, List.length_nil, pow_zero, one_mul]
      apply hC.trans
      rw [show (j.factorial : ℝ)*M/ε^j = weight j*M by dsimp [weight]; ring]
      apply mul_le_mul_of_nonneg_right _ hM
      have := Finset.single_le_sum (f := weight) (fun i _ => hw i) hj'
      dsimp [W]
      linarith
    | cons t l ih =>
      simp only [List.length_cons] at hj ⊢
      have he := step_bound (stage l) (c t) (d t) z j L
        ((K*(1+L))^l.length*(W*M)) (hc t (hl t (by simp))) (hd t) (by positivity)
        (fun i hi => ih (fun t ht => hl t (by simp [ht])) i (by omega))
      apply he.trans
      rw [pow_succ, mul_right_comm ((K*(1+L))^l.length), mul_comm _ (K*(1+L))]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hj' : (j : ℝ) ≤ 8 := by exact_mod_cast (show j ≤ 8 by omega)
      dsimp only [K]
      nlinarith [mul_nonneg (norm_nonneg z) hL]
  let l := (Finset.univ.erase v).toList
  have hlen : l.length = s-1 := by simp [l, Finset.card_erase_of_mem]
  have hb := bound l (by simp [l]) 0 (by rw [hlen]; have := hs.2; omega)
  change ‖(stage l).eval z‖ ≤ _
  rw [hlen, mul_pow] at hb
  simpa only [Function.iterate_zero_apply, mul_assoc, mul_left_comm, mul_comm, L] using hb

end Turan.SectionTwo
