module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Sturm
public import Turan.DiskProjection
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Sqrt

@[expose] public section

noncomputable section
open Filter Metric Polynomial
namespace Turan

/-- Each open cell of the partition of [0,1] contains a distinct Hermite zero. -/
private theorem disk_nodes (m k : ℕ) (hk : 0 < k) (hm : (4*k)^2 ≤ m) :
    ∃ r : Fin k → ℂ, Function.Injective r ∧
      ∀ i, ‖r i‖ ≤ 1 ∧ (hermite m).eval (r i) = 0 := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  let freq := Real.pi * (k : ℝ)
  have hf : 0 < freq := mul_pos Real.pi_pos hk'
  have hlen : Real.pi / freq = 1 / (k : ℝ) := by
    dsimp [freq]
    field_simp [Real.pi_pos.ne', hk'.ne']
  have hfreq : freq ^ 2 ≤ (m : ℝ) := by
    have hlt : freq ≤ 4 * (k : ℝ) :=
      mul_le_mul_of_nonneg_right Real.pi_lt_four.le hk'.le
    exact (pow_le_pow_left₀ hf.le hlt 2).trans (by exact_mod_cast hm)
  let left (i : Fin k) := (i.val : ℝ) / k
  have cell (i : Fin k) : ∃ t : ℝ, left i < t ∧ t < left i + 1/k ∧
      (hermite m).eval (t : ℂ) = 0 := by
    have ha : 0 ≤ left i := by dsimp [left]; positivity
    have hb : left i + 1/k ≤ 1 := by
      dsimp [left]
      rw [← add_div, div_le_iff₀ hk', one_mul]
      exact_mod_cast i.isLt
    obtain ⟨t, ht, hz⟩ := hermite_sturm_interval m (left i) freq hf (by
      rw [hlen]
      intro x hx
      have hx₀ := ha.trans_lt hx.1
      have hx₁ := hx.2.trans_le hb
      nlinarith only [hfreq, mul_pos (sub_pos.mpr hx₁) (by linarith : 0 < 1+x),
        Nat.cast_nonneg (α := ℝ) m])
    rw [hlen] at ht
    have hden : (Real.sqrt (2^m * (m.factorial : ℝ)) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < 2^m * (m.factorial : ℝ))).ne'
    exact ⟨t, ht.1, ht.2, (div_eq_zero_iff.mp hz).resolve_right hden⟩
  choose t hlo hhi hroot using cell
  have jump {i j : Fin k} (hij : i < j) : left i + 1/k ≤ left j := by
    dsimp [left]
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) hk'.le
  have hmono : StrictMono t := fun i j hij =>
    ((hhi i).trans_le (jump hij)).trans (hlo j)
  refine ⟨fun i => (t i : ℂ), Complex.ofReal_injective.comp hmono.injective, fun i => ⟨?_, hroot i⟩⟩
  have ht₀ : 0 ≤ t i := (show 0 ≤ left i by dsimp [left]; positivity).trans (hlo i).le
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht₀]
  apply (hhi i).le.trans
  dsimp [left]
  rw [← add_div, div_le_iff₀ hk', one_mul]
  exact_mod_cast i.isLt

/-- For k = floor(sqrt(m)/4), once k ≥ 1 we have m+1 ≤ (8k)².
The exponential in k eventually dominates the seventh power of this bound. -/
private theorem disk_node_threshold (C : ℝ) (hC : 0 < C) :
    ∃ M : ℕ, ∀ m ≥ M, ∃ k : ℕ, 0 < k ∧ (4*k)^2 ≤ m ∧
      C * ((m : ℝ)+1)^7 < (2 : ℝ)^k := by
  let D : ℝ := C * 8^14
  have hD : 0 < D := by dsimp [D]; positivity
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt 14 (by norm_num : (1:ℝ) < 2)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const (one_div_pos.mpr hD))
  refine ⟨(4*(N+1))^2, fun m hm => ?_⟩
  let k := m.sqrt / 4
  have hlarge := Nat.le_sqrt'.mpr hm
  have hk : N+1 ≤ k := by dsimp [k]; omega
  have hkpos : 0 < k := by omega
  have hlow : 4*k ≤ m.sqrt := by dsimp [k]; omega
  have hupp : m.sqrt + 1 ≤ 8*k := by dsimp [k] at *; omega
  have hm' : m+1 ≤ (8*k)^2 :=
    (Nat.lt_succ_sqrt' m).trans_le (Nat.pow_le_pow_left hupp 2)
  have hexp := hN k (by omega)
  change (k:ℝ)^14 / 2^k < 1/D at hexp
  have he : D * (k:ℝ)^14 < 2^k := by
    have he' := (div_lt_div_iff₀ (by positivity) hD).mp hexp
    linarith
  refine ⟨k, hkpos, (Nat.pow_le_pow_left hlow 2).trans (Nat.sqrt_le' m), ?_⟩
  calc
    C * ((m:ℝ)+1)^7 ≤ C * ((8*(k:ℝ))^2)^7 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hm') 7) hC.le
    _ = D * (k:ℝ)^14 := by dsimp [D]; ring
    _ < 2^k := he

/-- Dividing out k distinct zeros in the unit disk gains a factor of two
per zero between the outer circle and the inner disk. -/
private theorem disk_suppression_of_nodes (P F : Polynomial ℂ) (b : ℂ)
    (K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B) {k : ℕ} (r : Fin k → ℂ)
    (hr : Function.Injective r) (hroot : ∀ i, ‖r i‖ ≤ 1 ∧ P.eval (r i) = 0)
    (hF : ∀ w : ℂ, ‖w‖ ≤ 2*(K+1)+1 → F.eval w ≠ 0)
    (hbound : ∀ w : ℂ, ‖w‖ = 2*(K+1)+1 → ‖b * P.eval w / F.eval w‖ ≤ B)
    (z : ℂ) (hz : ‖z‖ ≤ K) : ‖b * P.eval z / F.eval z‖ ≤ B / 2^k := by
  classical
  let S := 2*(K+1)+1
  let T : Polynomial ℂ := ∏ i, (X - Polynomial.C (r i))
  obtain ⟨Q, hQ⟩ : T ∣ P := Fintype.prod_dvd_of_coprime
    (pairwise_coprime_X_sub_C hr) (fun i => dvd_iff_isRoot.mpr (hroot i).2)
  let g (w : ℂ) := b * Q.eval w / F.eval w
  have hd : DifferentiableOn ℂ g (closedBall 0 S) :=
    (Q.differentiable.differentiableOn.const_mul b).div
      F.differentiable.differentiableOn (fun w hw => hF w (by simpa [mem_closedBall] using hw))
  have factor (w : ℂ) : ‖b * P.eval w / F.eval w‖ = ‖g w‖ * ‖T.eval w‖ := by
    rw [← norm_mul, hQ, eval_mul]
    apply congrArg norm
    dsimp [g]
    ring
  have factors (w : ℂ) : ‖T.eval w‖ = ∏ i, ‖w - r i‖ := by
    simp [T, eval_prod]
  have hK₁ : 0 < K+1 := by linarith
  have houter : 0 < (2*(K+1))^k := by positivity
  have boundary (w : ℂ) (hw : w ∈ frontier (ball 0 S)) :
      ‖g w‖ ≤ B / (2*(K+1))^k := by
    have hwS : ‖w‖ = S := by
      simpa [mem_sphere] using frontier_ball_subset_sphere hw
    have hfac (i : Fin k) : 2*(K+1) ≤ ‖w - r i‖ := by
      have hn := norm_sub_norm_le w (r i)
      rw [hwS] at hn
      dsimp [S] at hn
      linarith only [hn, (hroot i).1]
    have hT : (2*(K+1))^k ≤ ‖T.eval w‖ := by
      rw [factors]
      simpa using (Finset.prod_le_prod₀ (s := Finset.univ)
        (f := fun _ : Fin k => 2*(K+1)) (g := fun i => ‖w-r i‖)
        (fun _ _ => by positivity) (fun i _ => hfac i))
    apply (le_div_iff₀ houter).mpr
    exact (mul_le_mul_of_nonneg_left hT (norm_nonneg _)).trans
      ((factor w) ▸ hbound w hwS)
  have hinside : z ∈ ball (0 : ℂ) S := by
    simp only [mem_ball, dist_zero_right]
    dsimp [S]
    linarith
  have hg := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    (hd.diffContOnCl_ball subset_rfl) boundary (subset_closure hinside)
  have hTz : ‖T.eval z‖ ≤ (K+1)^k := by
    rw [factors]
    simpa using (Finset.prod_le_prod₀ (s := Finset.univ)
      (f := fun i => ‖z-r i‖) (g := fun _ : Fin k => K+1)
      (fun _ _ => norm_nonneg _) (fun i _ => (norm_sub_le ..).trans (add_le_add hz (hroot i).1)))
  rw [factor]
  calc
    _ ≤ B / (2*(K+1))^k * (K+1)^k :=
      mul_le_mul hg hTz (norm_nonneg _) (div_nonneg hB houter.le)
    _ = B / 2^k := by rw [mul_pow]; field_simp [hK₁.ne']

/-- A polynomial seventh-power bound on the boundary yields any prescribed
inner bound for the top Hermite mode, uniformly in its coefficient and denominator. -/
theorem disk_suppression_threshold (K ε C : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) (hC : 0 < C) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ (F : Polynomial ℂ) (b : ℂ),
      (∀ w : ℂ, ‖w‖ ≤ 2*(K+1)+1 → F.eval w ≠ 0) →
      (∀ w : ℂ, ‖w‖ = 2*(K+1)+1 → ‖b*(hermite m).eval w / F.eval w‖ ≤ C*((m:ℝ)+1)^7) →
      ∀ z : ℂ, ‖z‖ ≤ K → ‖b*(hermite m).eval z / F.eval z‖ < ε := by
  obtain ⟨M, hM⟩ := disk_node_threshold (C/ε) (div_pos hC hε)
  refine ⟨M, fun m hm F b hfree hbound z hz => ?_⟩
  obtain ⟨k, hk, hkm, hsmall⟩ := hM m hm
  obtain ⟨r, hr, hroot⟩ := disk_nodes m k hk hkm
  apply (disk_suppression_of_nodes (hermite m) F b K (C*((m:ℝ)+1)^7) hK
    (by positivity) r hr hroot hfree hbound z hz).trans_lt
  apply (div_lt_iff₀ (by positivity)).mpr
  rw [mul_comm ε]
  apply (div_lt_iff₀ hε).mp
  simpa only [div_mul_eq_mul_div] using hsmall

/-- A zero-free family on a large disk has uniformly small high mode on the
inner disk, once the upper index exceeds a threshold independent of the lower one. -/
theorem high_mode_small_on_disk (K : ℝ) (hK : 0 ≤ K) :
    ∃ R : ℝ, K < R ∧ ∃ M : ℕ, ∀ n m : ℕ, 2 ≤ n → n < m → M ≤ m → ∀ a b : ℂ,
      (∀ w : ℂ, ‖w‖ ≤ R → (family n m a b).eval w ≠ 0) →
      ∀ z : ℂ, ‖z‖ ≤ K → ‖b*(hermite m).eval z / (family n m a b).eval z‖ < 1 := by
  let S := 2*(K+1)+1
  obtain ⟨C, hC, hproj⟩ := disk_projection_bound S (by dsimp [S]; linarith)
  obtain ⟨M, hM⟩ := disk_suppression_threshold K 1 C hK zero_lt_one hC
  refine ⟨S+2, by dsimp [S]; linarith, M, ?_⟩
  intro n m hn hnm hm a b hfree
  exact hM m hm (family n m a b) b
    (fun w hw => hfree w (hw.trans (by dsimp [S]; linarith)))
    (fun w hw => hproj n m hn hnm a b w hfree hw.le)

end Turan
