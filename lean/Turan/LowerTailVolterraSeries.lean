-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.LowerTailVolterraBounds
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

noncomputable section
open Filter Metric Set Polynomial
open scoped ComplexConjugate Topology
namespace Turan.LowerTailSteps

private def evenTerm (Q : ℝ) (k : ℕ) := Q^k / ((2*k).factorial : ℝ)
private def oddTerm (Q : ℝ) (k : ℕ) := Q^k / ((2*k+1).factorial : ℝ)

private theorem even_sum (Q : ℝ) (hQ : 0 ≤ Q) : HasSum (evenTerm Q) (Real.cosh (Real.sqrt Q)) := by
  unfold evenTerm
  simpa only [pow_mul, Real.sq_sqrt hQ] using Real.hasSum_cosh (Real.sqrt Q)

private theorem odd_sum (Q : ℝ) (hQ : 0 < Q) : HasSum (oddTerm Q) (Real.sinh (Real.sqrt Q)/Real.sqrt Q) := by
  convert (Real.hasSum_sinh (Real.sqrt Q)).div_const (Real.sqrt Q) using 1
  funext k
  rw [pow_succ,pow_mul,Real.sq_sqrt hQ.le]
  unfold oddTerm
  field_simp [(Real.sqrt_pos.mpr hQ).ne']

private theorem uniform_majorant (j : ℕ) (ξ ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) (v : ℂ) (hv : ‖v‖ ≤ 1) :
    ‖volterraTerm j ξ ρ k v‖ ≤ ‖radialMode j ξ ρ 0‖*evenTerm (circleQ j ξ ρ) k +
      ‖radialSlope j ξ ρ‖*oddTerm (circleQ j ξ ρ) k := by
  apply (volterra_factorial_bounds j ξ ρ hρ k v hv).2.2.trans
  dsimp only [evenTerm, oddTerm]
  have Q : 0 ≤ circleQ j ξ ρ := by unfold circleQ; positivity
  calc
    _ ≤ (circleQ j ξ ρ)^k * ‖radialMode j ξ ρ 0‖ * 1^ (2*k) / _ +
        (circleQ j ξ ρ)^k * ‖radialSlope j ξ ρ‖ * 1^ (2*k+1) / _ := by gcongr
    _ = _ := by simp only [one_pow,mul_one]; ring

private theorem majorant_summable (j : ℕ) (ξ ρ : ℝ) (hρ : 0 < ρ) :
    Summable (fun k => ‖radialMode j ξ ρ 0‖*evenTerm (circleQ j ξ ρ) k +
      ‖radialSlope j ξ ρ‖*oddTerm (circleQ j ξ ρ) k) := by
  have hQ : 0 < circleQ j ξ ρ := by unfold circleQ; positivity
  exact ((even_sum _ hQ.le).summable.mul_left _).add ((odd_sum _ hQ).summable.mul_left _)

private theorem iter_congr_disk (j : ℕ) (ξ ρ : ℝ) {f g : ℂ → ℂ}
    (h : ∀ w : ℂ, ‖w‖ ≤ 1 → f w = g w) (k : ℕ) :
    ∀ v : ℂ, ‖v‖ ≤ 1 → ((volterraOp j ξ ρ)^[k] f) v = ((volterraOp j ξ ρ)^[k] g) v := by
  induction k with
  | zero => exact h
  | succ k ih => simpa only [Function.iterate_succ_apply'] using op_congr_disk j ξ ρ ih

private theorem bounded_iterates (j : ℕ) (ξ ρ : ℝ) (hρ : 0 < ρ) (f : ℂ → ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hf : ∀ w : ℂ, ‖w‖ ≤ 1 → ‖f w‖ ≤ B) (k : ℕ) (v : ℂ) (hv : ‖v‖ ≤ 1) :
    ‖((volterraOp j ξ ρ)^[k] f) v‖ ≤ B*evenTerm (circleQ j ξ ρ) k := by
  have h := iter_bound j ξ ρ hρ f B 0 (by simpa using hf) k v hv
  simp only [add_zero] at h
  apply h.trans
  have hQ : 0 ≤ circleQ j ξ ρ := by unfold circleQ; positivity
  calc
    _ ≤ (circleQ j ξ ρ)^k * B / ((2*k).factorial:ℝ) := div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg _) hv)) (by positivity)
    _ = _ := by unfold evenTerm; ring

private theorem tel (j : ℕ) (ξ ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) (v : ℂ) (hv : ‖v‖ ≤ 1) :
    (∑ i ∈ Finset.range k, volterraTerm j ξ ρ i v) +
      ((volterraOp j ξ ρ)^[k] (radialMode j ξ ρ)) v = radialMode j ξ ρ v := by
  let T := volterraOp j ξ ρ
  let u := radialMode j ξ ρ
  let a := radialAffine j ξ ρ
  have hstep (n : ℕ) : (T^[n] u) v = volterraTerm j ξ ρ n v + (T^[n+1] u) v := by
    have hu : ∀ w : ℂ, ‖w‖ ≤ 1 → u w = (a+T u) w := fun w hw => (radial_integral_equation j ξ ρ hρ w hw).2
    have ha : Continuous a := by unfold a radialAffine; fun_prop
    have he := iter_congr_disk j ξ ρ hu n v hv
    rw [iter_add j ξ ρ ha (op_continuous j ξ ρ (mode_continuous j ξ ρ))] at he
    exact he
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, add_assoc]
    exact (congrArg ((∑ i ∈ Finset.range k, volterraTerm j ξ ρ i v) + ·) (hstep k).symm).trans ih

private theorem radialPartial_limit (j : ℕ) (ξ ρ : ℝ) (hρ : 0 < ρ) (v : ℂ) (hv : ‖v‖ ≤ 1) :
    Tendsto (fun k => ∑ i ∈ Finset.range k, volterraTerm j ξ ρ i v) atTop (𝓝 (radialMode j ξ ρ v)) := by
  let u := radialMode j ξ ρ
  obtain ⟨w,hw,hmax⟩ := (isCompact_closedBall (0:ℂ) 1).exists_isMaxOn (nonempty_closedBall.mpr zero_le_one)
    (mode_continuous j ξ ρ).norm.continuousOn
  have hbound := bounded_iterates j ξ ρ hρ u ‖u w‖ (norm_nonneg _)
    (fun z hz => hmax (by simpa using hz))
  have hQ : 0 ≤ circleQ j ξ ρ := by unfold circleQ; positivity
  have hzero : Tendsto (fun k => ((volterraOp j ξ ρ)^[k] u) v) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k => hbound k v hv)
    simpa using (even_sum _ hQ).summable.tendsto_atTop_zero.const_mul ‖u w‖
  have he (k : ℕ) := eq_sub_of_add_eq (tel j ξ ρ hρ k v hv)
  simpa only [he, sub_zero] using tendsto_const_nhds.sub hzero


theorem radialMode_hasSum (j : ℕ) (ξ ρ : ℝ) (hρ : 0 < ρ) (v : ℂ) (hv : ‖v‖ ≤ 1) :
    HasSum (fun k => volterraTerm j ξ ρ k v) (radialMode j ξ ρ v) := by
  have hs := (majorant_summable j ξ ρ hρ).of_norm_bounded (fun k => uniform_majorant j ξ ρ hρ k v hv)
  exact hs.hasSum_iff_tendsto_nat.mpr (radialPartial_limit j ξ ρ hρ v hv)

theorem volterra_series_solves (j : ℕ) (ξ ρ : ℝ) (hρ : 0 < ρ) :
    let term := volterraTerm j ξ ρ
    let F := fun v => ∑' k, term k v
    TendstoUniformlyOn (fun N v => ∑ k ∈ Finset.range N, term k v) F atTop (closedBall 0 1) ∧
    ContinuousOn F (closedBall 0 1) ∧
    ∀ v ∈ closedBall (0:ℂ) 1, F v = radialAffine j ξ ρ v + volterraOp j ξ ρ F v := by
  let F := fun v => ∑' k, volterraTerm j ξ ρ k v
  have he : ∀ v : ℂ, ‖v‖ ≤ 1 → F v = radialMode j ξ ρ v := fun v hv => (radialMode_hasSum j ξ ρ hρ v hv).tsum_eq
  refine ⟨tendstoUniformlyOn_tsum_nat (majorant_summable j ξ ρ hρ) (fun k v hv =>
    uniform_majorant j ξ ρ hρ k v (by simpa using hv)), ?_, ?_⟩
  · exact (mode_continuous j ξ ρ).continuousOn.congr (fun v hv => he v (by simpa using hv))
  · intro v hv
    have hv' : ‖v‖ ≤ 1 := by simpa using hv
    change F v = _ + volterraOp j ξ ρ F v
    rw [he v hv', op_congr_disk j ξ ρ he v hv']
    exact (radial_integral_equation j ξ ρ hρ v hv').2

theorem volterra_unique (j : ℕ) (ξ ρ : ℝ) (hρ : 0 < ρ) (f g : ℂ → ℂ)
    (hf : ContinuousOn f (closedBall 0 1)) (hg : ContinuousOn g (closedBall 0 1))
    (hef : ∀ v ∈ closedBall (0:ℂ) 1, f v = radialAffine j ξ ρ v + volterraOp j ξ ρ f v)
    (heg : ∀ v ∈ closedBall (0:ℂ) 1, g v = radialAffine j ξ ρ v + volterraOp j ξ ρ g v) :
    let M := sSup ((fun w => ‖f w-g w‖) '' closedBall (0:ℂ) 1)
    (∀ k : ℕ, ∀ v ∈ closedBall (0:ℂ) 1,
      ‖f v-g v‖ ≤ M * (circleQ j ξ ρ)^k / ((2*k).factorial : ℝ)) ∧
    EqOn f g (closedBall (0:ℂ) 1) := by
  let D (w : ℂ) := f w-g w
  let S := closedBall (0:ℂ) 1
  let M := sSup ((fun w => ‖D w‖) '' S)
  have hD : ContinuousOn D S := hf.sub hg
  have hbdd := ((isCompact_closedBall (0:ℂ) 1).image_of_continuousOn hD.norm).bddAbove
  have hM (w : ℂ) (hw : ‖w‖ ≤ 1) : ‖D w‖ ≤ M :=
    le_csSup hbdd ⟨w, by simpa [S] using hw, rfl⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  have hfix (v : ℂ) (hv : ‖v‖ ≤ 1) : D v = volterraOp j ξ ρ D v := by
    have hi (g : ℂ → ℂ) (hg : ContinuousOn g S) :
        IntervalIntegrable (fun s : ℝ => ((1-s:ℝ):ℂ)*radialPotential j ξ ρ ((s:ℂ)*v)*g ((s:ℂ)*v))
          MeasureTheory.volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul (by unfold radialPotential; fun_prop)
      apply hg.comp (by fun_prop)
      intro s hs
      simpa [S] using radial_shrink (s := s) (by simpa only [uIcc_of_le zero_le_one] using hs) hv
    have hv' : v ∈ closedBall (0:ℂ) 1 := by simpa using hv
    change f v-g v = _
    rw [hef _ hv', heg _ hv']
    dsimp [volterraOp,D]
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub (hi f hf) (hi g hg)]
    ring
  have hbound (k : ℕ) (v : ℂ) (hv : v ∈ S) : ‖D v‖ ≤ M * evenTerm (circleQ j ξ ρ) k := by
    have hv' : ‖v‖ ≤ 1 := by simpa [S] using hv
    have he (i : ℕ) : ((volterraOp j ξ ρ)^[i] D) v = D v := by
      induction i with
      | zero => rfl
      | succ i ih =>
        rw [Function.iterate_succ_apply, ← iter_congr_disk j ξ ρ hfix i v hv', ih]
    rw [← he k]
    exact bounded_iterates j ξ ρ hρ D M hM0 hM k v hv'
  refine ⟨fun k v hv => ?_, ?_⟩
  · simpa [M,D,S,evenTerm,mul_div_assoc] using hbound k v hv
  · intro v hv
    have hlim := (even_sum (circleQ j ξ ρ) (by unfold circleQ; positivity)).summable.tendsto_atTop_zero.const_mul M
    have hn := le_of_tendsto_of_tendsto' (tendsto_const_nhds (x := ‖D v‖)) hlim (fun k => hbound k v hv)
    exact sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa using hn : ‖D v‖ ≤ 0))

theorem volterra_remainder_series (j : ℕ) (ξ ρ : ℝ) (hρ : 0 < ρ) (v : ℂ) (hv : ‖v‖ ≤ 1) :
    let u := radialMode j ξ ρ
    let δ := radialSlope j ξ ρ
    let Q := circleQ j ξ ρ
    let term := volterraTerm j ξ ρ
    let E := ∑' k : ℕ, Q^k / ((2*k).factorial : ℝ)
    let O := ∑' k : ℕ, Q^(k+1) / ((2*(k+1)+1).factorial : ℝ)
    u v - δ*v = u 0 + ∑' k : ℕ, term (k+1) v ∧
    ‖u v - δ*v‖ ≤ ‖u 0‖*E + ‖δ‖*O ∧
    E = Real.cosh (Real.sqrt Q) ∧ O = Real.sinh (Real.sqrt Q)/Real.sqrt Q - 1 := by
  let Q := circleQ j ξ ρ
  let A := radialMode j ξ ρ 0
  let d := radialSlope j ξ ρ
  let u := radialMode j ξ ρ
  let t := fun k => volterraTerm j ξ ρ k v
  have hQ : 0 < Q := by dsimp [Q,circleQ]; positivity
  have hs : HasSum t (u v) := radialMode_hasSum j ξ ρ hρ v hv
  have h0 : t 0 = A+d*v := rfl
  have hid : u v-d*v = A + ∑' k : ℕ, t (k+1) := by
    have he := hs.summable.tsum_eq_zero_add
    rw [hs.tsum_eq,h0] at he
    linear_combination he
  have hmajor := majorant_summable j ξ ρ hρ
  have hnorm : Summable (fun k => ‖t k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => uniform_majorant j ξ ρ hρ k v hv) hmajor
  have he := even_sum Q hQ.le
  have ho := odd_sum Q hQ
  have hEs := (summable_nat_add_iff 1).2 he.summable
  have hOs := (summable_nat_add_iff 1).2 ho.summable
  have hsplit := he.summable.tsum_eq_zero_add
  have hsplit' := ho.summable.tsum_eq_zero_add
  change _ ∧ ‖u v-d*v‖ ≤ ‖A‖*(∑' k, evenTerm Q k) + ‖d‖*(∑' k, oddTerm Q (k+1)) ∧
    _ ∧ (∑' k, oddTerm Q (k+1)) = _
  refine ⟨hid, ?_, he.tsum_eq, ?_⟩
  · rw [hid]
    calc
      _ ≤ ‖A‖ + ‖∑' k : ℕ, t (k+1)‖ := norm_add_le .. 
      _ ≤ ‖A‖ + ∑' k : ℕ, ‖t (k+1)‖ :=
        add_le_add le_rfl (norm_tsum_le_tsum_norm (f := fun k : ℕ => t (k+1)) ((summable_nat_add_iff 1).2 hnorm))
      _ ≤ ‖A‖ + ∑' k : ℕ, (‖A‖*evenTerm Q (k+1) + ‖d‖*oddTerm Q (k+1)) := by
        apply add_le_add le_rfl
        exact ((summable_nat_add_iff 1).2 hnorm).tsum_le_tsum
          (fun k => uniform_majorant j ξ ρ hρ (k+1) v hv) ((summable_nat_add_iff 1).2 hmajor)
      _ = _ := by
        rw [Summable.tsum_add (hEs.mul_left _) (hOs.mul_left _),tsum_mul_left,tsum_mul_left, hsplit]
        simp [evenTerm]
        ring
  · rw [ho.tsum_eq, show oddTerm Q 0 = 1 by simp [oddTerm]] at hsplit'
    change (∑' k : ℕ, oddTerm Q (k+1)) = Real.sinh (Real.sqrt Q)/Real.sqrt Q - 1
    linarith only [hsplit']

end Turan.LowerTailSteps
