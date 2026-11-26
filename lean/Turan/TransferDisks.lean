module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TransferDefs
public import Turan.Circles
public import Turan.CircleMinimum
public import Turan.RealZeros

@[expose] public section

noncomputable section
open Polynomial Metric
namespace Turan

private theorem sum_on_unit_circle (p : Polynomial ℂ) (s : Finset ℕ) (v : ℂ) (hv : ‖v‖ = 1) :
    ‖∑ j ∈ s, p.coeff j * v^j‖ ≤ ∑ j ∈ s, ‖p.coeff j‖ := by
  simpa [norm_mul, norm_pow, hv] using norm_sum_le s (fun j => p.coeff j * v^j)

theorem coefficientMass_nonneg (p : Polynomial ℂ) : 0 ≤ coefficientMass p :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_eval_le_coefficientMass (p : Polynomial ℂ) (v : ℂ) (hv : ‖v‖ = 1) :
    ‖p.eval v‖ ≤ coefficientMass p := by
  rw [eval_eq_sum]
  exact sum_on_unit_circle p _ v hv

theorem eval_diskExpansion (p : Polynomial ℂ) (w : ℂ) (r : ℝ) (v : ℂ) :
    (diskExpansion p w r).eval v = p.eval (w + (r : ℂ)*v) := by
  simp [diskExpansion, eval_comp, eval_mul]

theorem norm_eval_le_disk_mass (p : Polynomial ℂ) (w : ℂ) (r : ℝ) (hr : 0 < r)
    (z : ℂ) (hz : ‖z-w‖ = r) : ‖p.eval z‖ ≤ coefficientMass (diskExpansion p w r) := by
  let v := (z-w)/(r : ℂ)
  have hv : ‖v‖ = 1 := by
    rw [show ‖v‖ = _ from norm_div _ _, hz, Complex.norm_of_nonneg hr.le, div_self hr.ne']
  have h := norm_eval_le_coefficientMass (diskExpansion p w r) v hv
  rwa [eval_diskExpansion, show w+(r : ℂ)*v = z by
    dsimp only [v]; field_simp [Complex.ofReal_ne_zero.mpr hr.ne']; ring] at h

/-- The positive-degree pivot has a zero at the center. Its margin absorbs
both the other coefficients of the low polynomial and the entire perturbation. -/
private theorem root_of_pivot_margin (p q : Polynomial ℂ) (b : ℂ) (k : ℕ) (hk : 1 ≤ k)
    (hgap : ‖b‖ * coefficientMass q < coefficientMargin p k) :
    ∃ v ∈ ball (0 : ℂ) 1, p.eval v + b*q.eval v = 0 := by
  classical
  unfold coefficientMargin at hgap
  have htail := Finset.sum_nonneg (s := p.support.erase k) (fun j _ => norm_nonneg (p.coeff j))
  have hc : p.coeff k ≠ 0 := norm_pos_iff.mp (by
    linarith [mul_nonneg (norm_nonneg b) (coefficientMass_nonneg q)])
  apply circle_comparison (P := fun v => p.coeff k * v^k) zero_lt_one
    (p.differentiable.add (q.differentiable.const_mul b)).differentiableOn (by fun_prop)
  · exact ⟨0, mem_ball_self zero_lt_one, by simp [zero_pow (by omega : k ≠ 0)]⟩
  · intro v hv
    have hv' : ‖v‖ = 1 := by simpa using mem_sphere.mp hv
    have he : p.eval v - p.coeff k*v^k = ∑ j ∈ p.support.erase k, p.coeff j*v^j := by
      apply sub_eq_iff_eq_add.mpr
      rw [eval_eq_sum, Polynomial.sum]
      exact (Finset.sum_erase_add _ _ (mem_support_iff.mpr hc)).symm
    calc
      _ = ‖(p.eval v - p.coeff k*v^k) + b*q.eval v‖ := by
        change ‖p.eval v + b*q.eval v - p.coeff k*v^k‖ = _
        congr 1
        ring
      _ ≤ ‖p.eval v - p.coeff k*v^k‖ + ‖b*q.eval v‖ := norm_add_le ..
      _ ≤ (∑ j ∈ p.support.erase k, ‖p.coeff j‖) + ‖b‖*coefficientMass q := by
        rw [he, norm_mul]
        exact add_le_add (sum_on_unit_circle _ _ v hv')
          (mul_le_mul_of_nonneg_left (norm_eval_le_coefficientMass q v hv') (norm_nonneg _))
      _ < ‖p.coeff k*v^k‖ := by simp only [norm_mul, norm_pow, hv', one_pow, mul_one]; linarith

/-- For a pencil in the checked upper half disk, the outer and inner
comparisons cover every complex coefficient of the high mode. -/
theorem transfer_pencil_upper (n m : ℕ) (check : TransferCertificate n m)
    (swap : Bool) (θ : ℂ) (hθ : ‖θ‖ ≤ 1) (him : 0 ≤ θ.im) (b : ℂ) :
    ∃ z : ℂ, (transferPencil n swap θ).eval z + b*(hermite m).eval z = 0 ∧ |z.im| < 87/100 := by
  obtain ⟨w, ri, x, ro, k, hi, ho, hk, hwi, hxo, hsign, hgap⟩ := check swap θ hθ him
  let S := transferPencil n swap θ
  let H := hermite m
  let L := min ‖H.eval ((x-ro : ℝ) : ℂ)‖ ‖H.eval ((x+ro : ℝ) : ℂ)‖
  let outer := coefficientMass (diskExpansion S (x : ℂ) ro)
  let p := diskExpansion S w ri
  let q := diskExpansion H w ri
  change outer * coefficientMass q < coefficientMargin p k * L at hgap
  by_cases hbig : outer < ‖b‖*L
  · obtain ⟨y, hy, hzero⟩ := hermite_zero_of_sign_change m (x-ro) (x+ro) (by linarith) hsign
    have hyball : (y : ℂ) ∈ ball (x : ℂ) ro := by
      rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith [hy.1, hy.2]
    have dom (z : ℂ) (hz : z ∈ sphere (x : ℂ) ro) :
        ‖(S.eval z + b*H.eval z) - b*H.eval z‖ < ‖b*H.eval z‖ := by
      have hr : ‖z-(x : ℂ)‖ = ro := by simpa [dist_eq_norm] using mem_sphere.mp hz
      have hmin : L ≤ ‖H.eval z‖ := real_rooted_circle H
        (fun t ht => (hermite_real_simple m t ht).1) x ro ho z hr
      rw [add_sub_cancel_right, norm_mul]
      exact (norm_eval_le_disk_mass S _ ro ho z hr).trans_lt
        (hbig.trans_le (mul_le_mul_of_nonneg_left hmin (norm_nonneg b)))
    obtain ⟨z, hz, he⟩ := circle_comparison ho
      (S.differentiable.add (H.differentiable.const_mul b)).differentiableOn
      (H.differentiable.const_mul b).differentiableOn
      ⟨(y : ℂ), hyball, by change b*(hermite m).eval _ = 0; rw [hzero, mul_zero]⟩ dom
    exact ⟨z, he, disk_in_strip _ _ _ _ (by simpa using hxo) (ball_subset_closedBall hz)⟩
  · have hsmall : ‖b‖*coefficientMass q < coefficientMargin p k := by
      apply lt_of_mul_lt_mul_right (a := L) _ (le_min (norm_nonneg _) (norm_nonneg _))
      calc
        _ = (‖b‖*L)*coefficientMass q := by ring
        _ ≤ outer*coefficientMass q :=
          mul_le_mul_of_nonneg_right (le_of_not_gt hbig) (coefficientMass_nonneg q)
        _ < _ := hgap
    obtain ⟨v, hv, he⟩ := root_of_pivot_margin p q b k hk hsmall
    have hv' : ‖v‖ ≤ 1 := by simpa using (mem_ball.mp hv).le
    have hball : w+(ri : ℂ)*v ∈ closedBall w ri := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_of_nonneg hi.le]
      exact mul_le_of_le_one_right hi.le hv'
    exact ⟨_, by simpa only [p, q, eval_diskExpansion] using he,
      disk_in_strip _ _ _ _ hwi hball⟩

end Turan
