module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TailLogDisk
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section

noncomputable section
namespace Turan
open Complex Metric Filter
open scoped Topology

private def dnorm (f : ℂ → ℂ) (k : ℕ) : ℝ := ‖iteratedDeriv k f 0‖

private lemma product_bound (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (k : ℕ) :
    dnorm (fun t ↦ f t * g t) k ≤
      ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) * dnorm f i * dnorm g (k-i) := by
  unfold dnorm
  rw [iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt]
  simpa only [norm_mul, Complex.norm_natCast] using
    norm_sum_le (Finset.range (k+1))
      (fun i ↦ (k.choose i : ℂ) * iteratedDeriv i f 0 * iteratedDeriv (k-i) g 0)

/-- Cauchy's estimate on concentric subdisks, followed by the radial limit. -/
private lemma cauchy_unit {S : ℂ → ℂ} (hd : DifferentiableOn ℂ S (ball 0 1))
    (hb : ∀ t ∈ ball (0 : ℂ) 1, ‖S t‖ ≤ ‖t‖) (k : ℕ) :
    dnorm S k ≤ k.factorial := by
  suffices h : ∀ᶠ r in 𝓝[<] (1 : ℝ), dnorm S k ≤ (k.factorial : ℝ) / r^k by
    have ht : ContinuousAt (fun r : ℝ ↦ (k.factorial : ℝ) / r^k) 1 := by fun_prop (disch := simp)
    simpa using ge_of_tendsto ht.continuousWithinAt h
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
  have hsub := closedBall_subset_ball (x := (0 : ℂ)) hr.2
  have he := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (f := S)
    (C := 1) k hr.1 (hd.diffContOnCl_ball hsub) (fun t ht ↦
      (hb t (hsub (sphere_subset_closedBall ht))).trans
        (mem_ball_zero_iff.mp (hsub (sphere_subset_closedBall ht))).le)
  simpa [dnorm] using he

private def schwarzMajorant (k : ℕ) : ℝ := if k = 0 then 0 else k.factorial

/-- Bounds for the four logarithmic derivatives from H = 2LS - HS and Cauchy's
estimate for S. The scale is the unit disk. -/
private lemma log_jet_bounds {H : ℂ → ℂ} (h0 : H 0 = 0)
    (hd : DifferentiableOn ℂ H (ball 0 1))
    (hb : ∀ t ∈ ball (0 : ℂ) 1, (H t).re ≤ 71/2) :
    dnorm H 1 ≤ 71 ∧ dnorm H 2 ≤ 284 ∧ dnorm H 3 ≤ 1704 ∧ dnorm H 4 ≤ 13632 := by
  obtain ⟨S, hS0, hSd, hSb, heq, _⟩ := tailLog_schwarz (by norm_num : (0:ℝ) < 71/2)
    h0 hd hb
  have hHa := hd.analyticAt (ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ) < 1))
  have hSa := hSd.analyticAt (ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ) < 1))
  have hSD (k) : dnorm S k ≤ schwarzMajorant k := by
    by_cases hk : k = 0
    · simp [hk, dnorm, schwarzMajorant, hS0]
    · simpa [schwarzMajorant, hk] using cauchy_unit hSd hSb k
  have he : H =ᶠ[𝓝 0] fun t ↦ 71 * S t - H t * S t := by
    filter_upwards [ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ) < 1)] with t ht
    convert heq t ht using 1
    push_cast
    ring
  have hrec (k : ℕ) : dnorm H k ≤ 71 * schwarzMajorant k +
      ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) * dnorm H i * schwarzMajorant (k-i) := by
    calc
      dnorm H k ≤ 71 * dnorm S k + dnorm (fun t ↦ H t * S t) k := by
        unfold dnorm
        rw [he.iteratedDeriv_eq k, iteratedDeriv_fun_sub
          (f := fun t ↦ 71 * S t) (g := fun t ↦ H t * S t)
          (analyticAt_const.mul hSa).contDiffAt (hHa.mul hSa).contDiffAt,
          iteratedDeriv_const_mul_field]
        simpa [norm_mul] using norm_sub_le ((71:ℂ) * iteratedDeriv k S 0)
          (iteratedDeriv k (fun t ↦ H t * S t) 0)
      _ ≤ _ := by
        apply add_le_add (by gcongr; apply hSD)
        apply (product_bound H S hHa hSa k).trans
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hSD _) (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
  have hzero : dnorm H 0 = 0 := by simp [dnorm, h0]
  have h1 := hrec 1
  have h2 := hrec 2
  have h3 := hrec 3
  have h4 := hrec 4
  norm_num [Finset.sum_range_succ, schwarzMajorant, hzero, Nat.choose, Nat.factorial]
    at h1 h2 h3 h4
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The normalized function satisfies G' = G H'. Leibniz's formula gives its
first four derivatives using only the four logarithmic derivative bounds. -/
theorem tailLog_unit_deriv {G H : ℂ → ℂ} (hg : Differentiable ℂ G) (hg0 : G 0 = 1)
    (hd : DifferentiableOn ℂ H (ball 0 1)) (h0 : H 0 = 0)
    (hb : ∀ t ∈ ball (0 : ℂ) 1, (H t).re ≤ 71/2)
    (he : deriv G =ᶠ[𝓝 0] (fun t ↦ G t * deriv H t))
    (l : ℕ) (hl : 1 ≤ l) (hl' : l ≤ 4) : ‖iteratedDeriv l G 0‖ ≤ 77^l := by
  obtain ⟨h1,h2,h3,h4⟩ := log_jet_bounds h0 hd hb
  let B : ℕ → ℝ := fun k ↦ if k = 1 then 71 else if k = 2 then 284 else
    if k = 3 then 1704 else 13632
  have hB (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 4) : dnorm H k ≤ B k := by
    interval_cases k <;> simp_all [B]
  have hDa := (hd.deriv isOpen_ball).analyticAt
    (ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ) < 1))
  have hrec (k : ℕ) (hk : k ≤ 3) : dnorm G (k+1) ≤
      ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) * dnorm G i * B (k-i+1) := by
    calc
      dnorm G (k+1) = dnorm (fun t ↦ G t * deriv H t) k := by
        simp only [dnorm, iteratedDeriv_succ', he.iteratedDeriv_eq k]
      _ ≤ _ := by
        apply (product_bound G (deriv H) (hg.analyticAt _) hDa k).trans
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
        simpa only [dnorm, iteratedDeriv_succ'] using hB (k-i+1) (by omega) (by omega)
  have hzero : dnorm G 0 = 1 := by simp [dnorm, hg0]
  have g1 := hrec 0 (by decide)
  have g2 := hrec 1 (by decide)
  have g3 := hrec 2 (by decide)
  have g4 := hrec 3 (by decide)
  norm_num [Finset.sum_range_succ, B, Nat.choose, hzero] at g1 g2 g3 g4
  change dnorm G l ≤ _
  interval_cases l <;> norm_num <;> linarith

end Turan
