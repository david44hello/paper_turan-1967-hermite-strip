-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.QuarticContactRows
import Turan.QuarticVerticalDefs
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic

noncomputable section
open Filter Polynomial Set
open scoped Topology
namespace Turan
namespace VerticalInterpolation

private def w (z : ℂ) (e : ℝ) := quarticVerticalMove e z + 1/2
private def val (j : ℕ) (z : ℂ) (e : ℝ) := nodeMode j (w z e)
private def tan (j : ℕ) (z : ℂ) (e : ℝ) := deriv (nodeMode j) (w z e)
private abbrev Regular (f : ℝ → ℂ) := ∀ᶠ e in 𝓝 (0 : ℝ), ContinuousAt f e

@[simp] private theorem w_zero (z : ℂ) : w z 0 = z + 1/2 := by simp [w, quarticVerticalMove]

private theorem regular_rows (j : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    Regular (val j z) ∧ Regular (tan j z) := by
  have hw : Continuous (w z) := by unfold w quarticVerticalMove; fun_prop
  have hne : w z 0 ≠ 0 := by
    intro he
    apply hz
    simpa using congrArg Complex.im he
  have H : ∀ᶠ e in 𝓝 (0 : ℝ), ContinuousAt (val j z) e ∧ ContinuousAt (tan j z) e := by
    filter_upwards [hw.continuousAt.eventually_ne hne] with e he
    have han : AnalyticAt ℂ (nodeMode j) (w z e) := by
      apply AnalyticAt.div _ analyticAt_id he
      exact ((AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (hermite j)) _ trivial).comp
        (analyticAt_id.sub analyticAt_const)
    exact ⟨han.continuousAt.comp hw.continuousAt, han.deriv.continuousAt.comp hw.continuousAt⟩
  exact ⟨H.mono fun _ => And.left, H.mono fun _ => And.right⟩

private def Solution (a b : ℂ) (P : ℝ → ℂ → ℂ → Prop) : Prop :=
  ∃ (A B : ℝ → ℂ) (η : ℝ), 0 < η ∧ A 0 = a ∧ B 0 = b ∧
    ContinuousOn A (Ico 0 η) ∧ ContinuousOn B (Ico 0 η) ∧
    ∀ e ∈ Ico 0 η, P e (A e) (B e)

private theorem solve_rows (a b p q : ℂ) (U V S T : ℝ → ℂ)
    (hU : Regular U) (hV : Regular V) (hS : Regular S) (hT : Regular T)
    (hp : a*U 0 + b*V 0 = p) (hq : a*S 0 + b*T 0 = q)
    (hdet : U 0*T 0 - V 0*S 0 ≠ 0)
    (P : ℝ → ℂ → ℂ → Prop)
    (hP : ∀ e c d, c*U e + d*V e = p → c*S e + d*T e = q → P e c d) :
    Solution a b P := by
  let D (e : ℝ) := U e*T e - V e*S e
  let A (e : ℝ) := (p*T e - V e*q)/D e
  let B (e : ℝ) := (U e*q - p*S e)/D e
  have hD : Regular D := by
    filter_upwards [hU,hV,hS,hT] with e hu hv hs ht using (hu.mul ht).sub (hv.mul hs)
  have hgood : ∀ᶠ e in 𝓝 (0 : ℝ), ContinuousAt A e ∧ ContinuousAt B e ∧ D e ≠ 0 := by
    filter_upwards [hU,hV,hS,hT,hD,hD.self_of_nhds.eventually_ne hdet] with e hu hv hs ht hd hn
    exact ⟨((continuousAt_const.mul ht).sub (hv.mul continuousAt_const)).div hd hn,
      ((hu.mul continuousAt_const).sub (continuousAt_const.mul hs)).div hd hn, hn⟩
  obtain ⟨η,hη,hball⟩ := Metric.eventually_nhds_iff.mp hgood
  have hloc (e : ℝ) (he : e ∈ Ico 0 η) := hball (y := e) (by
    simpa [Real.dist_eq,abs_of_nonneg he.1] using he.2)
  refine ⟨A,B,η,hη,?_,?_,fun e he => (hloc e he).1.continuousWithinAt,
    fun e he => (hloc e he).2.1.continuousWithinAt, ?_⟩
  · apply (div_eq_iff hdet).2
    linear_combination -(T 0)*hp + (V 0)*hq
  · apply (div_eq_iff hdet).2
    linear_combination (S 0)*hp - (U 0)*hq
  · intro e he
    apply hP
    · dsimp [A,B]
      field_simp [(hloc e he).2.2]
      dsimp [D]
      ring
    · dsimp [A,B]
      field_simp [(hloc e he).2.2]
      dsimp [D]
      ring

private def Prescribes (a b : ℂ) (M : Multiset ℂ) (e : ℝ) (c d : ℂ) : Prop :=
  quarticMovedRows M e c d ∧ ∀ z : ℂ, M = {z} →
    if nodeMode 2 (z + 1/2) ≠ 0 then d = b else c = a

private theorem interpolate (a b : ℂ) (M : Multiset ℂ) (hfew : M.card ≤ 2)
    (hn : ∀ z ∈ M, z.im ≠ 0)
    (eqs : ∀ z ∈ M, a*val 2 z 0 + b*val 4 z 0 = -2 ∧
      (2 ≤ M.count z → a*tan 2 z 0 + b*tan 4 z 0 = 0))
    (rank₂ : ∀ z ∈ M, ∀ t ∈ M, z ≠ t →
      val 2 z 0 * val 4 t 0 - val 4 z 0 * val 2 t 0 ≠ 0)
    (rankD : ∀ z ∈ M, 2 ≤ M.count z →
      val 2 z 0 * tan 4 z 0 - val 4 z 0 * tan 2 z 0 ≠ 0) :
    Solution a b (Prescribes a b M) := by
  classical
  have hcard : M.card = 0 ∨ M.card = 1 ∨ M.card = 2 := by omega
  rcases hcard with h | h | h
  · obtain rfl := Multiset.card_eq_zero.mp h
    exact ⟨fun _ => a, fun _ => b, 1, zero_lt_one, rfl, rfl, continuousOn_const,
      continuousOn_const, fun e _ => by simp [Prescribes, quarticMovedRows]⟩
  · obtain ⟨z,rfl⟩ := Multiset.card_eq_one.mp h
    have he := (eqs z (by simp)).1
    have hnz := hn z (by simp)
    have hrow (e : ℝ) (c d : ℂ) (hval : c*val 2 z e + d*val 4 z e = -2) :
        quarticMovedRows {z} e c d := by
      intro t ht
      obtain rfl : t = z := by simpa using ht
      exact ⟨hval, by simp⟩
    by_cases h2 : nodeMode 2 (z + 1/2) ≠ 0
    · apply solve_rows a b (-2) b (val 2 z) (val 4 z) (fun _ => 0) (fun _ => 1)
        (regular_rows 2 z hnz).1 (regular_rows 4 z hnz).1
        (Eventually.of_forall fun _ => continuousAt_const) (Eventually.of_forall fun _ => continuousAt_const)
        he (by simp) (by simpa [val] using h2)
      intro e c d hv hfix
      refine ⟨hrow e c d hv, ?_⟩
      intro t ht
      obtain rfl : z = t := by simpa using ht
      rw [ite_eq_left h2]
      simpa using hfix
    · have h4 : val 4 z 0 ≠ 0 := by
        intro hz
        have h0 : val 2 z 0 = 0 := by simpa [val] using not_ne_iff.mp h2
        simp [h0,hz] at he
      apply solve_rows a b (-2) a (val 2 z) (val 4 z) (fun _ => 1) (fun _ => 0)
        (regular_rows 2 z hnz).1 (regular_rows 4 z hnz).1
        (Eventually.of_forall fun _ => continuousAt_const) (Eventually.of_forall fun _ => continuousAt_const)
        he (by simp) (by simpa using h4)
      intro e c d hv hfix
      refine ⟨hrow e c d hv, ?_⟩
      intro t ht
      obtain rfl : z = t := by simpa using ht
      rw [ite_eq_right h2]
      simpa using hfix
  · obtain ⟨z,t,rfl⟩ := Multiset.card_eq_two.mp h
    have hz := hn z (by simp)
    have ht := hn t (by simp)
    have hsecondary (e : ℝ) (c d : ℂ) (hr : quarticMovedRows {z,t} e c d) :
        Prescribes a b {z,t} e c d := by
      refine ⟨hr, fun q he => ?_⟩
      have := congrArg Multiset.card he
      simp at this
    by_cases hzt : z = t
    · subst t
      have hv := eqs z (by simp)
      have hm : 2 ≤ ({z,z} : Multiset ℂ).count z := by simp
      apply solve_rows a b (-2) 0 (val 2 z) (val 4 z) (tan 2 z) (tan 4 z)
        (regular_rows 2 z hz).1 (regular_rows 4 z hz).1 (regular_rows 2 z hz).2
        (regular_rows 4 z hz).2 hv.1 (hv.2 hm) (rankD z (by simp) hm)
      intro e c d he hd
      apply hsecondary
      intro q hq
      obtain rfl : q = z := by simpa using hq
      exact ⟨he,fun _ => hd⟩
    · apply solve_rows a b (-2) (-2) (val 2 z) (val 4 z) (val 2 t) (val 4 t)
        (regular_rows 2 z hz).1 (regular_rows 4 z hz).1 (regular_rows 2 t ht).1
        (regular_rows 4 t ht).1 (eqs z (by simp)).1 (eqs t (by simp)).1
        (rank₂ z (by simp) t (by simp) hzt)
      intro e c d he hf
      apply hsecondary
      intro q hq
      rcases (show q = z ∨ q = t by simpa using hq) with rfl | rfl
      · exact ⟨he, by simp [hzt]⟩
      · exact ⟨hf, by simp [hzt,Ne.symm hzt]⟩

end VerticalInterpolation

open VerticalInterpolation in
theorem quartic_vertical_interpolation (a b : ℂ) (y : ℝ) (hy : 0 < y)
    (hfew : (quarticBoundaryRoots a b y).card ≤ 2) :
    let M := quarticBoundaryRoots a b y
    ∃ (A B : ℝ → ℂ) (η : ℝ), 0 < η ∧ A 0 = a ∧ B 0 = b ∧
      ContinuousOn A (Set.Ico 0 η) ∧ ContinuousOn B (Set.Ico 0 η) ∧
      (∀ ε ∈ Set.Ico 0 η, quarticMovedRows M ε (A ε) (B ε)) ∧
      (∀ z : ℂ, M = {z} →
        if nodeMode 2 (z + 1/2) ≠ 0 then ∀ ε ∈ Set.Ico 0 η, B ε = b
        else ∀ ε ∈ Set.Ico 0 η, A ε = a) := by
  classical
  let M := quarticBoundaryRoots a b y
  have hr {z : ℂ} (hz : z ∈ M) := isRoot_of_mem_roots (Multiset.mem_filter.mp hz).1
  have hn (z : ℂ) (hz : z ∈ M) : z.im ≠ 0 := by
    have hc := (Multiset.mem_filter.mp hz).2
    intro he
    simp [he] at hc
    linarith
  have hm (z : ℂ) (hz : z ∈ M) : M.count z = (family 2 4 a b).rootMultiplicity z := by
    rw [← count_roots]
    exact Multiset.count_filter_of_pos (Multiset.mem_filter.mp hz).2
  obtain ⟨A,B,η,hη,hA,hB,hAc,hBc,H⟩ := interpolate a b M hfew hn (by
    intro z hz
    have H := quartic_contact_equations (hn z hz) (hr hz)
    simpa only [val,tan,w_zero,hm z hz] using H) (by
    intro z hz t ht hzt
    simpa only [val,w_zero] using quartic_distinct_contact_rows hzt (hn z hz) (hn t ht) (hr hz) (hr ht)) (by
    intro z hz hh
    rw [hm z hz] at hh
    simpa only [val,tan,w_zero] using quartic_double_contact_rows (hn z hz) hh)
  refine ⟨A,B,η,hη,hA,hB,hAc,hBc,fun e he => (H e he).1, ?_⟩
  intro z hz
  split_ifs with h
  · exact fun e he => by simpa only [ite_eq_left h] using (H e he).2 z hz
  · exact fun e he => by simpa only [ite_eq_right h] using (H e he).2 z hz

#print axioms quartic_vertical_interpolation
end Turan
