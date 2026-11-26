module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.SectionTwoHarmonicEstimates
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Analysis.Complex.LocallyUniformLimit

@[expose] public section

noncomputable section
open Filter Metric InnerProductSpace BoundedContinuousFunction
open scoped Topology Classical
namespace Turan.SectionTwo

private abbrev disk (R : ℝ) := closedBall (0 : ℂ) R

/-- Fix the imaginary part at the center, so the holomorphic lifts share both
a Lipschitz constant and a bound at the center. -/
private theorem disk_lift {u : ℂ → ℝ} {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hu : HarmonicOnNhd u (disk (R+1))) (hb : ∀ w ∈ disk (R+1), |u w| ≤ M) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 0 R) ∧
      LipschitzOnWith (Real.toNNReal (8*M)) g (disk R) ∧
      (∀ w ∈ disk R, ‖g w‖ ≤ M+8*M*R) ∧ ∀ w ∈ disk R, (g w).re = u w := by
  let U := ball (0 : ℂ) (R+1)
  obtain ⟨G,hG,hRe⟩ := (hu.mono ball_subset_closedBall).exists_analyticOnNhd_ball_re_eq
  let g (w : ℂ) := G w - ((G 0).im : ℂ)*Complex.I
  have hin : disk R ⊆ U := closedBall_subset_ball (by linarith)
  have hre {w : ℂ} (hw : w ∈ U) : (g w).re = u w := by
    simpa [g, Complex.sub_re, Complex.mul_re] using hRe hw
  have hd {w : ℂ} (hw : w ∈ U) : DifferentiableAt ℂ g w :=
    (hG w hw).differentiableAt.sub_const _
  have hl : LipschitzOnWith (Real.toNNReal (8*M)) g (disk R) := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le (fun w hw => hd (hin hw)) _ (convex_closedBall ..)
    intro w hw
    change ‖deriv g w‖₊ ≤ _
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ (by positivity), coe_nnnorm]
    have hball : ball w 1 ⊆ disk (R+1) := by
      intro y hy
      have hw' : ‖w‖ ≤ R := by simpa using mem_closedBall.mp hw
      apply mem_closedBall_zero_iff.mpr
      linarith [norm_sub_norm_le y w, mem_ball_iff_norm.mp hy]
    have he := Filter.eventually_of_mem (isOpen_ball.mem_nhds (hin hw)) fun y hy => hre hy
    rw [← gradient_of_re (hd (hin hw)).hasDerivAt, gradient_congr he]
    exact harmonic_gradient_bound w M hM (hu.mono hball) (fun y hy => hb _ (hball hy))
  refine ⟨g, fun w hw => (hd (hin (ball_subset_closedBall hw))).differentiableWithinAt, hl, ?_,
    fun w hw => hre (hin hw)⟩
  intro w hw
  have h0 : (0 : ℂ) ∈ disk R := mem_closedBall_self hR.le
  have he : g 0 = (u 0 : ℂ) := by
    apply Complex.ext
    · simpa using hre (hin h0)
    · simp [g, Complex.sub_im, Complex.mul_im]
  have hdist := hl.dist_le_mul _ hw 0 h0
  rw [Real.coe_toNNReal _ (by positivity), dist_zero_right, dist_eq_norm] at hdist
  have ht := norm_sub_norm_le (g w) (g 0)
  rw [he, Complex.norm_real, Real.norm_eq_abs] at ht
  rw [he] at hdist
  have hw' : ‖w‖ ≤ R := by simpa using mem_closedBall.mp hw
  linarith [mul_le_mul_of_nonneg_left hw' (show 0 ≤ 8*M by positivity), hb 0 (h0 |> closedBall_subset_closedBall (by linarith))]

private theorem compact_lifts (u : ℕ → ℂ → ℝ) (R : ℝ) (hR : 0 < R)
    (hb : ∃ M : ℝ, 0 < M ∧ ∀ᶠ j in atTop, HarmonicOnNhd (u j) (disk (R+1)) ∧
      ∀ w ∈ disk (R+1), |u j w| ≤ M) :
    ∃ (G : ℕ → ℂ → ℂ) (X : ℕ → (disk R →ᵇ ℂ)),
      IsCompact (closure (Set.range X)) ∧
      (∀ j, DifferentiableOn ℂ (G j) (ball 0 R)) ∧
      (∀ j (w : disk R), X j w = G j w) ∧
      ∀ᶠ j in atTop, ∀ w ∈ disk R, (G j w).re = u j w := by
  obtain ⟨M,hM,hev⟩ := hb
  let good j := HarmonicOnNhd (u j) (disk (R+1)) ∧ ∀ w ∈ disk (R+1), |u j w| ≤ M
  choose G hd hL hbnd hRe using fun j => (show ∃ g : ℂ → ℂ,
    DifferentiableOn ℂ g (ball 0 R) ∧ LipschitzOnWith (Real.toNNReal (8*M)) g (disk R) ∧
    (∀ w ∈ disk R, ‖g w‖ ≤ M+8*M*R) ∧ (good j → ∀ w ∈ disk R, (g w).re = u j w) by
      by_cases h : good j
      · obtain ⟨g,hd,hL,hB,he⟩ := disk_lift hR hM h.1 h.2
        exact ⟨g,hd,hL,hB,fun _ => he⟩
      · exact ⟨fun _ => 0, differentiableOn_const _, (LipschitzWith.const' (K := Real.toNNReal (8*M)) (0 : ℂ)).lipschitzOnWith,
          fun _ _ => by simp; positivity, fun hj => (h hj).elim⟩)
  let X (j : ℕ) : disk R →ᵇ ℂ :=
    mkOfCompact ⟨fun w => G j w, continuousOn_iff_continuous_domRestrict.mp (hL j).continuousOn⟩
  refine ⟨G,X,?_,hd,fun _ _ => rfl,hev.mono fun j hj => hRe j hj⟩
  apply BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) (M+8*M*R)) (isCompact_closedBall ..)
  · intro f w hf
    obtain ⟨j,rfl⟩ := hf
    exact mem_closedBall_zero_iff.mpr (hbnd j w w.property)
  · apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ (Real.toNNReal (8*M))
    rintro ⟨f,j,rfl⟩
    exact lipschitzOnWith_iff_restrict.mp (hL j)

theorem harmonic_subsequence_from_anchor (u : ℕ → ℂ → ℝ)
    (hup : ∀ R : ℝ, 0 < R → ∃ A : ℝ, ∀ᶠ j in atTop,
      HarmonicOnNhd (u j) (ball 0 R) ∧ ∀ z ∈ ball 0 R, u j z ≤ A)
    (hanchor : ∃ b : ℝ, ∀ᶠ j in atTop, ∃ z ∈ closedBall (0 : ℂ) 1, b ≤ u j z) :
    (∀ K : Set ℂ, IsCompact K → ∃ A : ℝ, ∀ᶠ j in atTop, ∀ z ∈ K, |u j z| ≤ A) ∧
    ∃ (φ : ℕ → ℕ) (v : ℂ → ℝ), StrictMono φ ∧ HarmonicOnNhd v Set.univ ∧
      TendstoLocallyUniformly (fun j => u (φ j)) v atTop := by
  have bounds := harmonic_anchor_bounds u hup hanchor
  constructor
  · intro K hK
    obtain ⟨R,hR,hKR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
    obtain ⟨A,_,hh⟩ := bounds R hR.le
    exact ⟨A,hh.mono fun j hj w hw => hj.2 w (hKR hw)⟩
  let r (n : ℕ) := (n : ℝ)+1
  have hr (n) : 0 < r n := by dsimp [r]; positivity
  choose G X hcompact hd hX hRe using fun n : ℕ =>
    compact_lifts u (r n) (hr n) (bounds (r n+1) (by positivity [hr n]))
  let path (j : ℕ) (n : ℕ) := X n j
  have hmem (j) : path j ∈ Set.pi Set.univ (fun n => closure (Set.range (X n))) :=
    fun n _ => subset_closure ⟨j,rfl⟩
  obtain ⟨Y,_,φ,hφ,hY⟩ := (isCompact_univ_pi hcompact).tendsto_subseq hmem
  let v (z : ℂ) := limUnder atTop (fun j => u (φ j) z)
  -- Each coordinate of the product limit is a uniform limit on one closed disk.
  let g (n : ℕ) (w : ℂ) := if h : w ∈ disk (r n) then Y n ⟨w,h⟩ else 0
  have hgu (n) : TendstoUniformlyOn (fun j => G n (φ j)) (g n) atTop (disk (r n)) := by
    have h := tendsto_pi_nhds.mp hY n
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp h ε hε] with j hj w hw
    change dist (g n w) (G n (φ j) w) < ε
    dsimp only [g]
    rw [dif_pos hw, ← hX n (φ j) ⟨w,hw⟩, dist_comm]
    exact (BoundedContinuousFunction.dist_coe_le_dist ⟨w,hw⟩).trans_lt hj
  have hv (n) : TendstoUniformlyOn (fun j => u (φ j)) (fun w => (g n w).re) atTop (disk (r n)) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hgu n) ε hε,
      hφ.tendsto_atTop.eventually (hRe n)] with j hj he w hw
    rw [← he w hw]
    exact (Complex.abs_re_le_norm ((g n w)-(G n (φ j) w))).trans_lt (by
      simpa [dist_eq_norm] using hj w hw)
  have hvEq (n) {w : ℂ} (hw : w ∈ disk (r n)) : v w = (g n w).re :=
    ((hv n).tendsto_at hw).limUnder_eq
  refine ⟨φ,v,hφ,?_,?_⟩
  · intro w _
    obtain ⟨n,hn⟩ := exists_nat_gt ‖w‖
    have hw : w ∈ ball 0 (r n) := mem_ball_zero_iff.mpr (by dsimp [r]; linarith)
    have hgl := ((hgu n).mono ball_subset_closedBall).tendstoLocallyUniformlyOn
    have hag := (hgl.differentiableOn (Eventually.of_forall fun j => hd n (φ j)) isOpen_ball).analyticAt
      (isOpen_ball.mem_nhds hw)
    apply (harmonicAt_congr_nhds (f₂ := fun w => (g n w).re) ?_).mpr hag.harmonicAt_re
    exact Filter.eventually_of_mem (isOpen_ball.mem_nhds hw) (fun y hy => hvEq n (ball_subset_closedBall hy))
  · apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
    intro K hK
    obtain ⟨R,hR,hRK⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
    obtain ⟨n,hn⟩ := exists_nat_ge R
    have hinc : K ⊆ disk (r n) := hRK.trans (closedBall_subset_closedBall (by dsimp [r]; linarith))
    exact ((hv n).mono hinc).congr_right (fun w hw => (hvEq n (hinc hw)).symm)

end Turan.SectionTwo
