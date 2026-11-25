-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Recover
import Turan.TailGapCore
import Turan.TailLinesHermite

noncomputable section
open Polynomial
namespace Turan

/-- The affine polynomial left by the two Hermite operators vanishes at this point. -/
private theorem disk_test_point (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) :
    ∃ z : ℂ, ‖z‖ ≤ 2 ∧ (n : ℂ)*m + 2*((n : ℂ)-1)*(m-1)*z = 0 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hn1 : 0 < (n : ℝ)-1 := by linarith
  have hm1 : 0 < (m : ℝ)-1 := by linarith
  have hden : 0 < 2*((n : ℝ)-1)*(m-1) := by positivity
  let x := -((n : ℝ)*m) / (2*((n : ℝ)-1)*(m-1))
  refine ⟨(x : ℂ), ?_, ?_⟩
  · simp only [Complex.norm_real, Real.norm_eq_abs, x, abs_div, abs_neg,
      abs_of_nonneg (show 0 ≤ (n : ℝ)*m by positivity),
      abs_of_pos hden, div_le_iff₀ hden]
    calc
      _ ≤ (2*((n : ℝ)-1)) * (2*((m : ℝ)-1)) := by gcongr <;> linarith
      _ = _ := by ring
  · have hx : (n : ℝ)*m + 2*((n : ℝ)-1)*(m-1)*x = 0 := by
      dsimp only [x]
      field_simp [hn1.ne', hm1.ne']
      ring
    exact_mod_cast hx

/-- Small first through fourth derivatives make both oscillator terms small. -/
private theorem disk_jet_bounds (z : ℂ) (hz : ‖z‖ ≤ 2) (d : ℕ → ℂ)
    (T : ℝ) (hT : 0 ≤ T) (hd : ∀ k, ‖d k‖ ≤ (1/10 : ℝ)^k * T) :
    ‖d 2/2 - z*d 1‖ ≤ T/3 ∧
    ‖d 4/4 - z*d 3 + (z^2-1)*d 2 + z*d 1‖ ≤ T/3 := by
  have hz2 : ‖z^2-1‖ ≤ 5 := by
    apply (norm_sub_le ..).trans
    rw [norm_pow, norm_one]
    nlinarith only [(sq_le_sq₀ (norm_nonneg z) (by norm_num : (0 : ℝ) ≤ 2)).mpr hz]
  constructor
  · grw [norm_sub_le]
    simp only [norm_div, norm_mul, Complex.norm_ofNat]
    calc
      _ ≤ ((1/10 : ℝ)^2*T)/2 + 2*((1/10)^1*T) := by gcongr <;> apply hd
      _ ≤ _ := by linarith only [hT]
  · grw [norm_add_le, norm_add_le, norm_sub_le]
    simp only [norm_div, norm_mul, Complex.norm_ofNat]
    calc
      _ ≤ ((1/10 : ℝ)^4*T)/4 + 2*((1/10)^3*T) + 5*((1/10)^2*T) + 2*((1/10)^1*T) := by
        gcongr <;> apply hd
      _ ≤ _ := by linarith only [hT]

theorem bounded_degree_disk (M : ℕ) :
    ∃ R : ℝ, 0 < R ∧ ∀ n m : ℕ, 2 ≤ n → n < m → m ≤ M → ∀ a b : ℂ,
      ∃ z : ℂ, (family n m a b).eval z = 0 ∧ ‖z‖ < R := by
  refine ⟨10*(M : ℝ)+3, by positivity, ?_⟩
  intro n m hn hnm hmM a b
  by_contra! outside
  obtain ⟨z, hz, hcancel⟩ := disk_test_point n m hn (by omega)
  let p := family n m a b
  let A := scaleCoeff n a
  let B := scaleCoeff m b
  let F := normalizedFamily n m A B
  have hF : F = fun w => p.eval w := funext (rescale_family n m a b)
  have hm : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hdist (w : ℂ) (hw : w ∈ p.roots) : 1 ≤ (1/(10*(m : ℝ))) * ‖z-w‖ := by
    have hout := outside w (isRoot_of_mem_roots hw)
    have htri := norm_sub_norm_le w z
    rw [norm_sub_rev] at htri
    rw [one_div_mul_eq_div, le_div_iff₀ (by positivity)]
    linarith only [hz, hout, htri, (by exact_mod_cast hmM : (m : ℝ) ≤ M)]
  have hdeg : p.natDegree ≤ m := by
    change (family n m a b).natDegree ≤ m
    rw [family_degree n m hn hnm]
    split_ifs <;> omega
  let T := ‖F z‖
  have hT : 0 < T := by
    apply norm_pos_iff.mpr
    rw [hF]
    intro he
    have hout := outside z he
    linarith [Nat.cast_nonneg (α := ℝ) M]
  let d (k : ℕ) := iteratedDeriv k F z
  have hjet (k : ℕ) : iteratedDeriv k F = fun w => (derivative^[k] p).eval w := by
    induction k with
    | zero => simpa using hF
    | succ k ih =>
      rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
      exact funext fun w => ((derivative^[k] p).hasDerivAt w).deriv
  have hd (k : ℕ) : ‖d k‖ ≤ (1/10 : ℝ)^k * T := by
    have hb := polynomial_derivatives_of_root_distance p z m k _ (by positivity) hdeg hdist
    change ‖iteratedDeriv k F z‖ ≤ (1/10 : ℝ)^k * ‖F z‖
    rw [hjet, hF]
    simpa only [show (m : ℝ)*(1/(10*m)) = 1/10 by field_simp] using hb
  let E := d 2/2 - z*d 1
  let EE := d 4/4 - z*d 3 + (z^2-1)*d 2 + z*d 1
  obtain ⟨hE, hEE⟩ := disk_jet_bounds z hz d T hT.le hd
  change ‖E‖ ≤ T/3 at hE
  change ‖EE‖ ≤ T/3 at hEE
  obtain ⟨h₁, h₂⟩ := TailLines.family_jets n m A B z
  change E = -2*z - n*(A*psi n z) - m*(B*psi m z) at h₁
  change EE = 2*z + (n : ℂ)^2*(A*psi n z) + (m : ℂ)^2*(B*psi m z) at h₂
  -- At z the affine term vanishes, and the two Hermite modes cancel identically.
  have hid : -((n : ℂ)*m*F z) = ((n : ℂ)+m)*E + EE := by
    rw [h₁, h₂]
    dsimp only [F, normalizedFamily]
    linear_combination -hcancel
  have hsum : (n : ℝ)*m*T ≤ ((n : ℝ)+m)*(T/3) + T/3 := by
    calc
      _ = ‖-((n : ℂ)*m*F z)‖ := by simp [T]
      _ = _ := congrArg norm hid
      _ ≤ ‖((n : ℂ)+m)*E‖ + ‖EE‖ := norm_add_le ..
      _ ≤ _ := by
        rw [norm_mul, ← Nat.cast_add, Complex.norm_natCast, Nat.cast_add]
        gcongr
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
  have hcoef : (n : ℝ)+m+1 < 3*((n : ℝ)*m) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hn') (sub_nonneg.mpr hm'), hn', hm']
  nlinarith only [hsum, mul_lt_mul_of_pos_right hcoef hT]

end Turan
