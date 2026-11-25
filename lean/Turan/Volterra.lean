-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Oscillator
import Turan.Hermite
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace Turan

private theorem primitive_derivative (f : ℝ → ℝ) (hf : Continuous f) (t : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ s in (0:ℝ)..r, f s) (f t) t :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

/-- A bound for the derivative norm can be integrated on the unit interval. -/
private theorem compare_derivative (F F' : ℝ → ℂ) (B B' : ℝ → ℝ)
    (hf : ∀ t, HasDerivAt F (F' t) t) (hb : ∀ t, HasDerivAt B (B' t) t)
    (hstart : ‖F 0‖ ≤ B 0) (hbound : ∀ t ∈ Set.Icc 0 1, ‖F' t‖ ≤ B' t) :
    ∀ t ∈ Set.Icc 0 1, ‖F t‖ ≤ B t := by
  intro t ht
  exact image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun s _ => (hf s).continuousAt.continuousWithinAt) (fun s _ => (hf s).hasDerivWithinAt)
    hstart hb (fun s hs => hbound s ⟨hs.1,hs.2.le⟩) ht

/-- Majorize a solution of a second-order equation along a radius. Here the
linear term is removed before the norm is taken. -/
private theorem oscillator_majorant (U V A : ℝ → ℂ) (q : ℝ) (hq : 0 < q)
    (hU : ∀ t, HasDerivAt U (V t) t) (hV : ∀ t, HasDerivAt V (A t) t)
    (ha : ∀ t ∈ Set.Icc 0 1, ‖A t‖ ≤ q^2 * ‖U t‖) :
    ‖U 1 - V 0‖ ≤ Real.cosh q * ‖U 0‖ + (Real.sinh q / q - 1) * ‖V 0‖ := by
  let d := V 0
  let S (t : ℝ) := q^2 * ‖U t‖
  have hS : Continuous S := continuous_const.mul (continuous_iff_continuousAt.mpr
    (fun t => (hU t).continuousAt.norm))
  let D (t : ℝ) := ∫ s in (0:ℝ)..t, S s
  have hD (t : ℝ) : HasDerivAt D (S t) t := primitive_derivative S hS t
  have hDc : Continuous D := continuous_iff_continuousAt.mpr fun t => (hD t).continuousAt
  let R (t : ℝ) := ‖U 0‖ + ∫ s in (0:ℝ)..t, D s
  have hR (t : ℝ) : HasDerivAt R (D t) t := (primitive_derivative D hDc t).const_add _
  have hd : ∀ t ∈ Set.Icc 0 1, ‖V t-d‖ ≤ D t := compare_derivative (fun t => V t-d) A D S
    (fun t => (hV t).sub_const d) hD (by simp [d,D]) ha
  have hr : ∀ t ∈ Set.Icc 0 1, ‖U t-(t:ℂ)*d‖ ≤ R t := by
    apply compare_derivative _ (fun t => V t-d) _ D _ hR (by simp [R]) hd
    intro t
    simpa [Pi.sub_def] using! (hU t).sub (((hasDerivAt_id t).ofReal_comp).mul_const d)
  let M (t : ℝ) := R t+t*‖d‖
  let N (t : ℝ) := D t+‖d‖
  have hm (t : ℝ) : HasDerivAt M (N t) t := by
    simpa [M,N,Pi.add_def] using! (hR t).add ((hasDerivAt_id t).mul_const ‖d‖)
  have hn (t : ℝ) : HasDerivAt N (S t) t := (hD t).add_const _
  have hub (t : ℝ) (ht : t ∈ Set.Icc 0 1) : ‖U t‖ ≤ M t := by
    have hadd := norm_add_le (U t-(t:ℂ)*d) ((t:ℂ)*d)
    rw [sub_add_cancel, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1] at hadd
    exact hadd.trans (add_le_add_left (hr t ht) _)
  let f (t : ℝ) := q*(1-t)
  let C (t : ℝ) := Real.cosh (f t)*M t + Real.sinh (f t)/q*N t
  have hc (t : ℝ) : HasDerivAt C (Real.sinh (f t)/q*(S t-q^2*M t)) t := by
    have hf : HasDerivAt f (-q) t := by simpa [f] using ((hasDerivAt_id t).const_sub 1).const_mul q
    convert (hf.cosh.mul (hm t)).add ((hf.sinh.div_const q).mul (hn t)) using 1
    field_simp
    ring
  have hcanti : AntitoneOn C (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (fun t _ => (hc t).continuousAt.continuousWithinAt)
      (fun t _ => (hc t).differentiableAt.differentiableWithinAt)
    intro t ht
    have hmem : t ∈ Set.Icc 0 1 := interior_subset ht
    rw [(hc t).deriv]
    apply mul_nonpos_of_nonneg_of_nonpos
    · exact div_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg hq.le (sub_nonneg.mpr hmem.2))) hq.le
    · exact sub_nonpos.mpr (mul_le_mul_of_nonneg_left (hub t hmem) (sq_nonneg q))
  have hend := hcanti (show (0:ℝ) ∈ Set.Icc 0 1 by simp) (show (1:ℝ) ∈ Set.Icc 0 1 by simp) zero_le_one
  simp [C,f,M,N,R,D] at hend
  have hrem := hr 1 (by simp)
  simp [R] at hrem
  dsimp [d,D] at hrem hend
  linarith

theorem phi_equation (j : ℕ) :
    (∀ z : ℂ, HasDerivAt (phi j) (deriv (phi j) z) z) ∧
    ∀ z : ℂ, HasDerivAt (deriv (phi j)) ((z^2-(2*(j:ℂ)+1))*phi j z) z := by
  let p := hermite j
  let a : ℂ := (Real.sqrt (2^j * (j.factorial : ℝ)) : ℂ)⁻¹
  let G (z : ℂ) := Complex.exp (-z^2/2)
  have hG (z : ℂ) : HasDerivAt G (-z*G z) z := by
    convert ((((hasDerivAt_id z).pow 2).neg.div_const 2).cexp) using 1 <;> dsimp [G] <;> ring
  let V (z : ℂ) := G z*(p.derivative.eval z-z*p.eval z)*a
  have hfirst (z : ℂ) : HasDerivAt (phi j) (V z) z := by
    convert (((hG z).mul (p.hasDerivAt z)).mul_const a) using 1
    · funext w; dsimp [phi,psi,G,p,a]; ring
    · dsimp [V]; ring
  have hder : deriv (phi j) = V := funext fun z => (hfirst z).deriv
  rw [hder]
  refine ⟨hfirst, ?_⟩
  intro z
  have hode := congrArg (fun P : Polynomial ℂ => P.eval z) (hermite_equation j)
  simp only [eval_neg, eval_smul] at hode
  simp only [eval_sub, eval_mul, eval_X, eval_ofNat, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_ofNat] at hode
  change p.derivative.derivative.eval z - 2*z*p.derivative.eval z = -(2*(j:ℂ)*p.eval z) at hode
  convert (((hG z).mul ((p.derivative.hasDerivAt z).sub ((hasDerivAt_id z).mul (p.hasDerivAt z)))).mul_const a) using 1
  · rfl
  change (z^2-(2*(j:ℂ)+1))*(G z*(p.eval z*a)) = _
  simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
  linear_combination -(G z*a)*hode

theorem oscillator_coeff (j : ℕ) (ξ ρ : ℝ) (w : ℂ) (hw : ‖w‖ ≤ ρ) :
    ‖((ξ:ℂ)+w)^2-(2*(j:ℂ)+1)‖ ≤ |2*(j:ℝ)+1-ξ^2|+2*|ξ| *ρ+ρ^2 := by
  have hid : ((ξ:ℂ)+w)^2-(2*(j:ℂ)+1) =
      -((2*(j:ℝ)+1-ξ^2:ℝ):ℂ) + (2:ℂ)*(ξ:ℂ)*w + w^2 := by push_cast; ring
  rw [hid]
  calc
    _ ≤ ‖-((2*(j:ℝ)+1-ξ^2:ℝ):ℂ) + (2:ℂ)*(ξ:ℂ)*w‖ + ‖w^2‖ := norm_add_le _ _
    _ ≤ ‖-((2*(j:ℝ)+1-ξ^2:ℝ):ℂ)‖ + ‖(2:ℂ)*(ξ:ℂ)*w‖ + ‖w^2‖ :=
      add_le_add_left (norm_add_le _ _) _
    _ ≤ _ := by
      simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_pow,
        Complex.norm_ofNat]
      gcongr

theorem lemma_thirteen (j : ℕ) (ξ ρ : ℝ) (hρ : 0 < ρ) (v : ℂ) (hv : ‖v‖ ≤ 1) :
    let δ := (ρ : ℂ) * deriv (phi j) (ξ : ℂ)
    let q := Real.sqrt (circleQ j ξ ρ)
    ‖phi j ((ξ : ℂ) + ρ*v) - δ*v‖ ≤ Real.cosh q * ‖phi j (ξ : ℂ)‖ +
      (Real.sinh q / q - 1) * ‖δ‖ := by
  dsimp only
  let b := (ρ:ℂ)*v
  let q := Real.sqrt (circleQ j ξ ρ)
  let z (s : ℂ) := (ξ:ℂ)+s*b
  let U (s : ℝ) := phi j (z s)
  let V (s : ℝ) := deriv (phi j) (z s)*b
  let A (s : ℝ) := ((z s)^2-(2*(j:ℂ)+1))*phi j (z s)*b^2
  have hz (s : ℂ) : HasDerivAt z b s := by simpa [z] using ((hasDerivAt_id s).mul_const b).const_add (ξ:ℂ)
  obtain ⟨h₁,h₂⟩ := phi_equation j
  have hU (s : ℝ) : HasDerivAt U (V s) s := ((h₁ (z s)).comp (s:ℂ) (hz s)).comp_ofReal
  have hV (s : ℝ) : HasDerivAt V (A s) s := by
    convert ((((h₂ (z s)).comp (s:ℂ) (hz s)).mul_const b).comp_ofReal) using 1
    dsimp [A]; ring
  have hQ : 0 < circleQ j ξ ρ := by unfold circleQ; positivity
  have hq : 0 < q := Real.sqrt_pos.mpr hQ
  have hq2 : q^2 = circleQ j ξ ρ := Real.sq_sqrt hQ.le
  have hb : ‖b‖ ≤ ρ := by
    rw [show b=(ρ:ℂ)*v by rfl,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hρ]
    simpa using mul_le_mul_of_nonneg_left hv hρ.le
  have hA (t : ℝ) (ht : t ∈ Set.Icc 0 1) : ‖A t‖ ≤ q^2 * ‖U t‖ := by
    have ht' : ‖(t:ℂ)*b‖ ≤ ρ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hb
    have hcoef := oscillator_coeff j ξ ρ ((t:ℂ)*b) ht'
    dsimp [A,U]
    rw [norm_mul,norm_mul,norm_pow,hq2,circleQ]
    rw [mul_right_comm, mul_comm (ρ^2)]
    gcongr
  have hm := oscillator_majorant U V A q hq hU hV hA
  simp only [U,V,z, Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul,
    add_zero] at hm
  let δ := (ρ:ℂ)*deriv (phi j) (ξ:ℂ)
  have hδ : deriv (phi j) (ξ:ℂ)*b = δ*v := by dsimp [b,δ]; ring
  rw [hδ] at hm
  refine hm.trans (add_le_add_right (mul_le_mul_of_nonneg_left ?_ ?_) _)
  · change ‖δ*v‖ ≤ ‖δ‖
    rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) hv
  · apply sub_nonneg.mpr
    apply (one_le_div₀ hq).2
    exact Real.self_le_sinh_iff.mpr hq.le

end Turan
