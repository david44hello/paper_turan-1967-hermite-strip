-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.LowerTailCenter
import Turan.Vertical
import Turan.Recover

noncomputable section
open Filter Metric Set Polynomial
open scoped ComplexConjugate Topology
namespace Turan.LowerTailSteps

def realEnergy (m : ℕ) (t : ℝ) : ℝ :=
  ‖psi m (t : ℂ)‖ ^ 2 + ‖deriv (psi m) (t : ℂ)‖ ^ 2 / (2 * (m : ℝ))

theorem psi_real (j : ℕ) (t : ℝ) : (((psi j t).re : ℝ) : ℂ) = psi j t := by
  apply Complex.conj_eq_iff_re.mp
  have hH := (hermite_symmetry j (t:ℂ)).1.symm
  simp [psi, hH]

theorem real_mode_sq (j : ℕ) (t : ℝ) : ‖psi j t‖^2 = (psi j t).re^2 := by
  conv_lhs => rw [← psi_real j t, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem adjacent_energy (j : ℕ) (z : ℂ) :
    ‖deriv (psi (j+1)) z‖^2 / (2*((j:ℝ)+1)) = ‖psi j z‖^2 := by
  have h := (psi_adjacent_derivatives j z).1.deriv
  rw [h, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity)]
  field_simp

theorem realEnergy_succ (j : ℕ) (t : ℝ) :
    realEnergy (j+1) t = ‖psi (j+1) t‖^2 + ‖psi j t‖^2 := by
  simp only [realEnergy, Nat.cast_succ, adjacent_energy]

private theorem odd_zero (k : ℕ) : psi (2*k+1) 0 = 0 := by
  have he := (hermite_symmetry (2*k+1) 0).2
  simp [pow_add, pow_mul] at he
  simp [psi, show (hermite (2*k+1)).eval 0 = 0 by linear_combination he/2]

private theorem center_norm (k : ℕ) : ‖psi (2*k) 0‖^2 = (((2*k).choose k : ℕ) : ℝ)/4^k := by
  have h := congrArg norm (even_center k).1
  simpa [norm_pow, norm_div] using h

private theorem center_upper (k : ℕ) : ‖psi (2*k) 0‖^2 ≤ 1 := by
  rw [center_norm, div_le_one (by positivity)]
  exact_mod_cast Nat.centralBinom_le_four_pow k

theorem realEnergy_origin_odd (k : ℕ) :
    realEnergy (2*k+1) 0 = ‖psi (2*k) 0‖^2 ∧ realEnergy (2*k+1) 0 ≤ 1 := by
  simp only [realEnergy_succ, Complex.ofReal_zero, odd_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
  exact ⟨trivial, center_upper _⟩

theorem realEnergy_origin_even (k : ℕ) (hk : 1 ≤ k) :
    realEnergy (2*k) 0 = (((2*k).choose k : ℕ) : ℝ) / 4^k ∧ realEnergy (2*k) 0 ≤ 1 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have he : realEnergy (2*(j+1)) 0 = ‖psi (2*(j+1)) 0‖^2 := by
    rw [show 2*(j+1) = (2*j+1)+1 by omega, realEnergy_succ]
    simp [odd_zero]
  exact ⟨he.trans (center_norm _), he.trans_le (center_upper _)⟩

theorem energy_origin_bounds (m : ℕ) (hm : 1 ≤ m) :
    1 / ((m:ℝ)+1) ≤ realEnergy m 0 ∧ realEnergy m 0 ≤ 1 := by
  rcases Nat.even_or_odd m with ⟨k,h⟩ | ⟨k,h⟩
  · have he : m=2*k := by omega
    rw [he]
    have hh := realEnergy_origin_even k (by omega)
    rw [← center_norm] at hh
    exact ⟨by simpa [hh.1] using (even_center k).2, hh.2⟩
  · have he : m=2*k+1 := by omega
    subst m
    obtain ⟨hE,hub⟩ := realEnergy_origin_odd k
    refine ⟨?_, hub⟩
    rw [hE]
    apply le_trans _ (even_center k).2
    push_cast
    gcongr <;> linarith

theorem energy_hasDeriv (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    HasDerivAt (realEnergy m) (2*t*‖deriv (psi m) (t:ℂ)‖^2 / (m:ℝ)) t := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  let f := Real.sqrt (2*((j:ℝ)+1))
  obtain ⟨hp,hq⟩ := psi_adjacent_derivatives j (t:ℂ)
  have hident : realEnergy (j+1) = fun s : ℝ => (psi (j+1) s).re^2 + (psi j s).re^2 := by
    funext s
    rw [realEnergy_succ, real_mode_sq, real_mode_sq]
  rw [hident]
  convert (hp.real_of_complex.pow 2).add (hq.real_of_complex.pow 2) using 1
  rw [hp.deriv, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by positivity)]
  simp only [Complex.sub_re, Complex.re_ofReal_mul, Complex.mul_re, Complex.mul_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
    Nat.cast_succ, Nat.cast_ofNat, pow_one, mul_zero, zero_mul, sub_zero, add_zero, zero_add]
  rw [real_mode_sq]
  field_simp
  ring

theorem realEnergy_derivative_min (m : ℕ) (hm : 1 ≤ m) :
    (∀ t : ℝ, HasDerivAt (realEnergy m)
      (2*t*‖deriv (psi m) (t : ℂ)‖^2 / (m : ℝ)) t) ∧
    1 / ((m : ℝ) + 1) ≤ realEnergy m 0 ∧
    (∀ t : ℝ, realEnergy m 0 ≤ realEnergy m t) := by
  refine ⟨energy_hasDeriv m hm, (energy_origin_bounds m hm).1, fun t => ?_⟩
  have hd := energy_hasDeriv m hm
  have hc : Continuous (realEnergy m) := continuous_iff_continuousAt.mpr fun s => (hd s).continuousAt
  rcases le_total 0 t with ht | ht
  · apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t) hc.continuousOn
      (fun s _ => (hd s).hasDerivWithinAt) _ (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht) ht
    intro s hs
    have := (show s ∈ Icc 0 t from interior_subset hs).1
    positivity
  · apply antitoneOn_of_deriv_nonpos (convex_Icc t 0) hc.continuousOn
      (fun s _ => (hd s).differentiableAt.differentiableWithinAt) _ (left_mem_Icc.mpr ht)
      (right_mem_Icc.mpr ht) ht
    intro s hs
    have h := (show s ∈ Icc t 0 from interior_subset hs).2
    rw [(hd s).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
      (Nat.cast_nonneg _)

theorem realEnergy_comparison (m : ℕ) (hm : 1 ≤ m) :
    (∀ t : ℝ, 0 ≤ t → deriv (realEnergy m) t ≤ 4*t*realEnergy m t) ∧
    Function.Even (realEnergy m) ∧
    (∀ t : ℝ, realEnergy m t ≤ realEnergy m 0 * Real.exp (2*t^2)) := by
  have hrate (t : ℝ) (ht : 0 ≤ t) : deriv (realEnergy m) t ≤ 4*t*realEnergy m t := by
    rw [(energy_hasDeriv m hm t).deriv, realEnergy]
    have hp : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    field_simp
    nlinarith only [mul_nonneg (mul_nonneg ht hp.le) (sq_nonneg ‖psi m (t:ℂ)‖)]
  have parity (j : ℕ) (t : ℝ) : ‖psi j ((-t:ℝ):ℂ)‖ = ‖psi j (t:ℂ)‖ := by
    simp [psi, (hermite_symmetry j (t:ℂ)).2, norm_div, norm_mul, norm_pow]
  have heven : Function.Even (realEnergy m) := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    intro t
    simp only [realEnergy_succ, parity]
  have hpos (t : ℝ) (ht : 0 ≤ t) : realEnergy m t ≤ realEnergy m 0 * Real.exp (2*t^2) := by
    let E (s : ℝ) := realEnergy m s * Real.exp (-(2*s^2))
    have hE (s : ℝ) : HasDerivAt E ((deriv (realEnergy m) s - 4*s*realEnergy m s) *
        Real.exp (-(2*s^2))) s := by
      have hd := energy_hasDeriv m hm s
      convert hd.mul (((((hasDerivAt_id s).pow 2).const_mul 2).neg).exp) using 1
      · rfl
      · rw [hd.deriv]
        simp
        ring
    have hanti := antitoneOn_of_deriv_nonpos (convex_Icc 0 t)
      (fun s _ => (hE s).continuousAt.continuousWithinAt)
      (fun s _ => (hE s).differentiableAt.differentiableWithinAt) (fun s hs => by
        rw [(hE s).deriv]
        exact mul_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr (hrate s (show s ∈ Icc 0 t from interior_subset hs).1)) (Real.exp_nonneg _))
    have H := hanti (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht) ht
    simpa [E, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)] using H
  refine ⟨hrate, heven, fun t => ?_⟩
  rcases le_total 0 t with ht | ht
  · exact hpos t ht
  · simpa only [heven t, neg_sq] using hpos (-t) (neg_nonneg.mpr ht)

theorem complex_mode_floor (n m : ℕ) (hn : 1 ≤ n) (hh : 2*n ≤ m) (c : ℂ) :
    1 / Real.sqrt ((m:ℝ)+2) ≤ 1 / Real.sqrt (2*(n:ℝ)+2) ∧
    1 / Real.sqrt (2*(n:ℝ)+2) ≤
      max ‖psi n c‖ (‖deriv (psi n) c‖ / Real.sqrt (2*(n:ℝ))) := by
  have hproj (j : ℕ) : ‖psi j (c.re : ℂ)‖ ≤ ‖psi j c‖ := by
    simp only [psi, norm_div]
    gcongr
    apply norm_eval_re_le
    intro w hw
    exact (hermite_real_simple j w (Polynomial.isRoot_of_mem_roots hw)).1
  refine ⟨one_div_le_one_div_of_le (by positivity) (Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 2*n+2 ≤ m+2))), ?_⟩
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let M := max ‖psi (j+1) c‖ (‖deriv (psi (j+1)) c‖ / Real.sqrt (2*((j:ℝ)+1)))
  have hM : 0 ≤ M := (norm_nonneg _).trans (le_max_left ..)
  have h1 : ‖psi (j+1) (c.re : ℂ)‖ ≤ M := (hproj _).trans (le_max_left ..)
  have hd : ‖deriv (psi (j+1)) c‖ / Real.sqrt (2*((j:ℝ)+1)) = ‖psi j c‖ := by
    rw [((psi_adjacent_derivatives j c).1).deriv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    field_simp
  have h2 : ‖psi j (c.re : ℂ)‖ ≤ M := (hproj _).trans (hd ▸ le_max_right ..)
  obtain ⟨_,h0,he⟩ := realEnergy_derivative_min (j+1) (by omega)
  have H := h0.trans (he c.re)
  rw [realEnergy_succ, Nat.cast_succ, div_le_iff₀ (by positivity)] at H
  simp only [Nat.cast_succ]
  change 1 / Real.sqrt (2*((j:ℝ)+1)+2) ≤ M
  rw [div_le_iff₀ (by positivity)]
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hsum := add_le_add ((sq_le_sq₀ (norm_nonneg _) hM).mpr h1) ((sq_le_sq₀ (norm_nonneg _) hM).mpr h2)
  nlinarith only [H, mul_le_mul_of_nonneg_right hsum (show 0 ≤ (j:ℝ)+1+1 by positivity)]

end Turan.LowerTailSteps
