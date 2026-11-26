module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Recover
public import Turan.SlotDefs

@[expose] public section

noncomputable section
open Polynomial
namespace Turan

namespace DiskProjection

/-- The shifted Hermite oscillator E+c. -/
private def shift (c : ℕ) (p : Polynomial ℂ) : Polynomial ℂ :=
  C (1/2) * p.derivative.derivative - p.derivative * X + C (c : ℂ) * p

private theorem shift_add (c : ℕ) (p q : Polynomial ℂ) :
    shift c (p+q) = shift c p + shift c q := by
  simp only [shift, derivative_add]
  ring

private theorem shift_C_mul (c : ℕ) (a : ℂ) (p : Polynomial ℂ) :
    shift c (C a * p) = C a * shift c p := by
  simp only [shift, derivative_C_mul]
  ring

private theorem shift_hermite (c j : ℕ) :
    shift c (hermite j) = C ((c : ℂ) - j) * hermite j := by
  apply Polynomial.funext
  intro w
  have h := congrArg (eval w) (hermite_equation j)
  simp only [shift, eval_add, eval_sub, eval_mul, eval_X, eval_C, eval_neg, eval_ofNat,
    nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, eval_natCast] at h ⊢
  linear_combination h / 2

/-- The three shifts isolate the top Hermite slot, including its integer multiplier. -/
private theorem project (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m) (c d a b : ℂ) :
    shift n (shift 1 (shift 0 (fourSlots n m c d a b))) =
      C (-(((m-n)*(m-1)*m : ℕ) : ℂ) * b) * hermite m := by
  simp only [fourSlots, shift_add, shift_C_mul, shift_hermite]
  simp only [Nat.cast_mul, Nat.cast_sub hnm.le,
    Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_zero, Nat.cast_one,
    map_neg, map_mul, map_sub, map_zero, map_one]
  ring

/-- A shifted oscillator uses two derivative orders. Differentiating p'X contributes
one additional term with coefficient k in derivative order k. -/
private theorem shift_bound (p : Polynomial ℂ) (w : ℂ) (c r : ℕ) (S B L : ℝ)
    (hw : ‖w‖ ≤ S) (hB : 0 ≤ B) (hL : 1/2 + S + r + c ≤ L)
    (hp : ∀ k ≤ r+2, ‖(derivative^[k] p).eval w‖ ≤ B) :
    ∀ k ≤ r, ‖(derivative^[k] (shift c p)).eval w‖ ≤ L * B := by
  intro k hk
  let d (i : ℕ) := (derivative^[i] p).eval w
  have hform : (derivative^[k] (shift c p)).eval w =
      (1/2)*d (k+2) - (d (k+1)*w + (k:ℂ)*d k) + (c:ℂ)*d k := by
    simp only [shift, iterate_map_add, iterate_derivative_sub, iterate_derivative_C_mul,
      iterate_derivative_derivative_mul_X, eval_add, eval_sub, eval_mul, eval_X,
      eval_C, nsmul_eq_mul, eval_natCast, d]
    rfl
  rw [hform]
  grw [norm_add_le, norm_sub_le, norm_add_le]
  simp only [norm_mul, norm_div, norm_one, Complex.norm_ofNat, Complex.norm_natCast]
  have hd (i : ℕ) (hi : i ≤ r+2) : ‖d i‖ ≤ B := hp i hi
  calc
    _ ≤ 1/2*B + (B*S + (k:ℝ)*B) + (c:ℝ)*B := by
      gcongr <;> apply hd <;> omega
    _ = (1/2 + S + k + c)*B := by ring
    _ ≤ L*B := mul_le_mul_of_nonneg_right (by
      have : (k : ℝ) ≤ r := by exact_mod_cast hk
      linarith) hB

end DiskProjection

open DiskProjection in
theorem fourSlots_projection_bound (S : ℝ) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ n m : ℕ, 2 ≤ n → n < m → ∀ c d a b w : ℂ,
      (∀ z : ℂ, ‖z‖ ≤ S+2 → (fourSlots n m c d a b).eval z ≠ 0) → ‖w‖ ≤ S →
      ‖b*(hermite m).eval w / (fourSlots n m c d a b).eval w‖ ≤ C*((m:ℝ)+1)^7 := by
  let L := S+6
  have hL : 0 < L := by dsimp [L]; linarith
  refine ⟨L^3, by positivity, ?_⟩
  intro n m hn hnm c d a b w hfree hw
  let p := fourSlots n m c d a b
  have hwpos : 0 < ‖p.eval w‖ := norm_pos_iff.mpr (hfree w (by linarith))
  have hdeg : p.natDegree ≤ m := by
    have hmode (j : ℕ) (u : ℂ) (hj : j ≤ m) : (C u * hermite j).natDegree ≤ m :=
      (natDegree_C_mul_le ..).trans ((hermite_degree j).1.le.trans hj)
    exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le (hmode 0 c (Nat.zero_le _)) (hmode 1 d (by omega)))
      (hmode n a hnm.le)) (hmode m b le_rfl)
  have hdist (z : ℂ) (hz : z ∈ p.roots) : 1 ≤ 1 * ‖w-z‖ := by
    have hout : S+2 < ‖z‖ := lt_of_not_ge fun hin =>
      hfree z hin (isRoot_of_mem_roots hz)
    have htri := norm_sub_norm_le z w
    rw [norm_sub_rev] at htri
    linarith
  let M := (m:ℝ)+1
  have hM : 1 ≤ M := by dsimp [M]; linarith [Nat.cast_nonneg (α := ℝ) m]
  let B := M^6 * ‖p.eval w‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have h₀ (k : ℕ) (hk : k ≤ 6) : ‖(derivative^[k] p).eval w‖ ≤ B := by
    have h := polynomial_derivatives_of_root_distance p w m k 1 zero_le_one hdeg hdist
    simp only [mul_one] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (pow_le_pow_left₀ (Nat.cast_nonneg m) (by dsimp [M]; linarith : (m:ℝ) ≤ M) k).trans
      (pow_le_pow_right₀ hM hk)
  have h₁ := shift_bound p w 0 4 S B L hw hB (by dsimp [L]; norm_num; linarith) h₀
  have h₂ := shift_bound (shift 0 p) w 1 2 S (L*B) L hw (by positivity)
    (by dsimp [L]; norm_num; linarith) h₁
  have hnm' : (n:ℝ) ≤ m := by exact_mod_cast hnm.le
  have h₃ := shift_bound (shift 1 (shift 0 p)) w n 0 S (L*(L*B)) (L*M) hw (by positivity)
    (by dsimp [L, M]; push_cast; nlinarith [mul_nonneg hS (Nat.cast_nonneg (α := ℝ) m)]) h₂ 0 le_rfl
  change ‖(shift n (shift 1 (shift 0 (fourSlots n m c d a b)))).eval w‖ ≤ _ at h₃
  rw [project n m hn hnm, eval_mul, eval_C] at h₃
  let D := (m-n)*(m-1)*m
  have hD : 0 < D := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hD' : 1 ≤ (D:ℝ) := by exact_mod_cast hD
  change ‖(-(D:ℂ)*b)*(hermite m).eval w‖ ≤ _ at h₃
  rw [mul_assoc, norm_mul, norm_neg, Complex.norm_natCast] at h₃
  rw [norm_div]
  apply (div_le_iff₀ hwpos).mpr
  calc
    _ ≤ (D:ℝ)*‖b*(hermite m).eval w‖ := le_mul_of_one_le_left (norm_nonneg _) hD'
    _ ≤ _ := h₃
    _ = _ := by dsimp only [B, M, p]; ring

theorem disk_projection_bound (S : ℝ) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ n m : ℕ, 2 ≤ n → n < m → ∀ a b w : ℂ,
      (∀ z : ℂ, ‖z‖ ≤ S+2 → (family n m a b).eval z ≠ 0) → ‖w‖ ≤ S →
      ‖b*(hermite m).eval w / (family n m a b).eval w‖ ≤ C*((m:ℝ)+1)^7 := by
  obtain ⟨C, hC, h⟩ := fourSlots_projection_bound S hS
  refine ⟨C, hC, fun n m hn hnm a b w => ?_⟩
  simpa only [fourSlots, hermite, map_one, one_mul, family] using h n m hn hnm 1 1 a b w

end Turan
