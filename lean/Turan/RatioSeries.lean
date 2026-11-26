module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.RatioDefs
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Tactic

@[expose] public section

noncomputable section
namespace Turan.Ratio
open Polynomial Metric Filter
open scoped Topology

def point (x r : ℝ) (v : ℂ) : ℂ := x + r*v

def weight (x r : ℝ) (v : ℂ) : ℂ :=
  Complex.exp (((-x*r : ℝ) : ℂ)*v + ((-r^2/2 : ℝ) : ℂ)*v^2)

def mode (j : ℕ) (x r : ℝ) (v : ℂ) : ℂ :=
  weight x r v * (ratioMode j).eval (point x r v)

private theorem convolution {a b : ℕ → ℂ} {v A B : ℂ}
    (ha : HasSum (fun n => a n*v^n) A) (hb : HasSum (fun n => b n*v^n) B) :
    HasSum (fun n => (∑ i ∈ Finset.range (n+1), a i*b (n-i))*v^n) (A*B) := by
  have h := hasSum_sum_range_mul_of_summable_norm ha.summable.norm hb.summable.norm
  rw [ha.tsum_eq, hb.tsum_eq] at h
  apply h.congr_fun
  intro n
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have he : i + (n-i) = n := by have := Finset.mem_range.mp hi; omega
  rw [show v^n = v^i * v^(n-i) by rw [← pow_add, he]]
  ring

private theorem exp_series (A v : ℂ) :
    HasSum (fun n : ℕ => (A^n / n.factorial)*v^n) (Complex.exp (A*v)) := by
  simpa [Complex.exp_eq_exp_ℂ, mul_pow, div_mul_eq_mul_div] using
    NormedSpace.expSeries_div_hasSum_exp (A*v)

private theorem weight_series (x r : ℝ) (v : ℂ) :
    HasSum (fun n => (gaugeCoeff x r n : ℂ)*v^n) (weight x r v) := by
  let A : ℂ := ((-x*r : ℝ) : ℂ)
  let B : ℂ := ((-r^2/2 : ℝ) : ℂ)
  let b (n : ℕ) : ℂ := if n%2 = 0 then B^(n/2)/(n/2).factorial else 0
  have hb : HasSum (fun n => b n * v^n) (Complex.exp (B*v^2)) := by
    rw [← add_zero (Complex.exp _)]
    apply HasSum.even_add_odd
    · simpa [b, pow_mul] using exp_series B (v^2)
    · simp [b]
  have h := convolution hb (exp_series A v)
  rw [← Complex.exp_add] at h
  change HasSum _ (Complex.exp (A*v+B*v^2))
  rw [add_comm]
  apply h.congr_fun
  intro n
  congr 1
  let s := Finset.range (n/2+1)
  have hsub : s.image (fun l => 2*l) ⊆ Finset.range (n+1) := by
    intro i hi
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hi
    have := Finset.mem_range.mp hl
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_subset hsub (fun i hi hnot => by
    have hodd : i%2 ≠ 0 := by
      intro he
      exact hnot (Finset.mem_image.mpr ⟨i/2, Finset.mem_range.mpr
        (by have := Finset.mem_range.mp hi; omega), by omega⟩)
    simp [b, hodd])]
  rw [Finset.sum_image (by intro i _ j _ he; change 2*i = 2*j at he; omega)]
  simp only [gaugeCoeff, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro l _
  simp [b, A, B]
  ring

theorem mode_series (j : ℕ) (x r : ℝ) (v : ℂ) :
    HasSum (fun n => gaugedJet j x r n * v^n) (mode j x r v) := by
  let p := diskExpansion (ratioMode j) x r
  have hp : HasSum (fun n => p.coeff n*v^n) (p.eval v) := by
    rw [eval_eq_sum]
    exact hasSum_sum_of_ne_finset_zero (fun n hn => by simp [notMem_support_iff.mp hn])
  have h := convolution hp (weight_series x r v)
  simpa only [mode, gaugedJet, point, p, diskExpansion, eval_comp, eval_add, eval_mul, eval_C, eval_X,
    mul_comm (weight x r v)] using h

/-- Cauchy's coefficient estimate on the radius-two circle gives the full
order-eleven remainder on the unit circle by summing a geometric series. -/
theorem cauchy_tail {f : ℂ → ℂ} {c : ℕ → ℂ} (hd : Differentiable ℂ f)
    (hs : ∀ v : ℂ, HasSum (fun n => c n*v^n) (f v)) {M : ℝ}
    (hb : ∀ w : ℂ, ‖w‖ = 2 → ‖f w‖ ≤ M) (v : ℂ) (hv : ‖v‖ = 1) :
    ‖f v - ∑ n ∈ Finset.range 11, c n*v^n‖ ≤ M/1024 := by
  have hp : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ c) 0 := by
    apply hasFPowerSeriesAt_iff.mpr (Eventually.of_forall (fun z => ?_))
    simpa [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm] using hs z
  have he := hp.eq_formalMultilinearSeries (hd.analyticAt 0).hasFPowerSeriesAt
  have hc (n : ℕ) : ‖c n‖ ≤ M / 2^n := by
    have h := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) he
    simp only [FormalMultilinearSeries.coeff_ofScalars] at h
    rw [h, norm_div, Complex.norm_natCast, div_le_iff₀ (by positivity)]
    have hder := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
      (by norm_num : (0:ℝ)<2) (hd.diffContOnCl (s := ball (0:ℂ) 2)) (fun w hw => hb w (by simpa using mem_sphere.mp hw))
    convert hder using 1
    ring
  let t (n : ℕ) := c n*v^n
  have ht : HasSum t (f v) := hs v
  have htail := (summable_nat_add_iff 11).mpr ht.summable
  have heq := ht.summable.sum_add_tsum_nat_add 11
  rw [ht.tsum_eq] at heq
  change ‖f v - ∑ n ∈ Finset.range 11, t n‖ ≤ _
  rw [← eq_sub_of_add_eq' heq]
  have hg := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_left (M/2048)
  apply (norm_tsum_le_tsum_norm htail.norm).trans
  calc
    _ ≤ _ := htail.norm.tsum_le_tsum (fun n => ?_) hg.summable
    _ = M/1024 := by rw [hg.tsum_eq]; ring
  simp only [t, norm_mul, norm_pow, hv, one_pow, mul_one]
  convert hc (n+11) using 1
  rw [pow_add, div_pow]
  ring

end Turan.Ratio
