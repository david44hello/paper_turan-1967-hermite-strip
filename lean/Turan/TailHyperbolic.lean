-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

noncomputable section
open Real
namespace Turan

private theorem positive_from_derivative (f g : ℝ → ℝ) (h : ∀ x, HasDerivAt f (g x) x)
    (hzero : 0 ≤ f 0) (hg : ∀ x, 0 ≤ x → 0 ≤ g x) (t : ℝ) (ht : 0 ≤ t) : 0 ≤ f t := by
  have hm : MonotoneOn f (Set.Ici 0) := monotoneOn_of_hasDerivWithinAt_nonneg
    (convex_Ici _) (fun x _ => (h x).continuousAt.continuousWithinAt)
    (fun x _ => (h x).hasDerivWithinAt) (fun x hx => hg x (interior_subset hx))
  exact hzero.trans (hm (show (0:ℝ) ∈ Set.Ici 0 by simp) ht ht)

/-- A cubic lower estimate for the reciprocal of sinh, proved by differentiating
the cleared inequality three times. -/
private theorem inv_sinh_lower (x : ℝ) (hx : 0 < x) :
    1/x-x/6 ≤ 1/Real.sinh x := by
  let f (t : ℝ) := 6*t-(6-t^2)*sinh t
  let g (t : ℝ) := 6-(6-t^2)*cosh t+2*t*sinh t
  let r (t : ℝ) := 4*t*cosh t+(t^2-4)*sinh t
  have hf (t : ℝ) : HasDerivAt f (g t) t := by
    dsimp [f,g]; convert ((hasDerivAt_id t).const_mul 6).sub
      ((((hasDerivAt_id t).pow 2).const_sub 6).mul (hasDerivAt_sinh t)) using 1 <;> simp [Pi.sub_def,Pi.add_def,Pi.mul_def] <;> ring
  have hg (t : ℝ) : HasDerivAt g (r t) t := by
    dsimp [g,r]
    convert (((((hasDerivAt_id t).pow 2).const_sub 6).mul (hasDerivAt_cosh t)).const_sub 6).add
      (((hasDerivAt_id t).const_mul 2).mul (hasDerivAt_sinh t)) using 1 <;> simp [Pi.sub_def,Pi.add_def,Pi.mul_def] <;> ring
  have hr (t : ℝ) : HasDerivAt r (t^2*cosh t+6*t*sinh t) t := by
    dsimp [r]
    convert (((hasDerivAt_id t).const_mul 4).mul (hasDerivAt_cosh t)).add
      ((((hasDerivAt_id t).pow 2).sub_const 4).mul (hasDerivAt_sinh t)) using 1 <;> simp [Pi.sub_def,Pi.add_def,Pi.mul_def] <;> ring
  have hr₀ := positive_from_derivative r _ hr (by simp [r]) (fun t ht => by
    have := sinh_nonneg_iff.mpr ht; positivity)
  have hg₀ := positive_from_derivative g r hg (by norm_num [g]) hr₀
  have hf₀ := positive_from_derivative f g hf (by simp [f]) hg₀ x hx.le
  dsimp [f] at hf₀
  have hs := sinh_pos_iff.mpr hx
  apply (mul_le_mul_iff_of_pos_right (mul_pos hx hs)).mp
  field_simp
  nlinarith

private def oddIndex (k : ℕ) : ℝ := 2*(k:ℝ)+1

private theorem log_tanh_five (x : ℝ) (hx : 0 < x) :
    (∑ k ∈ Finset.range 5, 2/oddIndex k * exp (-2*x*oddIndex k)) ≤ -log (tanh x) := by
  let u := exp (-2*x)
  have hu : 0 < u := exp_pos _
  have hu' : u < 1 := exp_lt_one_iff.mpr (by linarith)
  have hseries := hasSum_log_sub_log_of_abs_lt_one (show |u| < 1 by rwa [abs_of_pos hu])
  have he : tanh x = (1-u)/(1+u) := by
    rw [tanh_eq]
    dsimp [u]
    rw [show -2*x = -x + -x by ring, exp_add, exp_neg]
    field_simp
  rw [he, log_div (sub_pos.mpr hu').ne' (by positivity)]
  rw [neg_sub, ← hseries.tsum_eq]
  apply le_trans _ (hseries.summable.sum_le_tsum (Finset.range 5) (fun i _ => by positivity))
  apply Finset.sum_le_sum
  intro k _
  dsimp [oddIndex,u]
  rw [← Real.exp_nat_mul]
  push_cast
  ring_nf
  rfl

private theorem paired_term (c d e B : ℝ) (hc : 0 < c) (h : d+e ≤ B) :
    2*exp (-c*B) ≤ exp (-2*c*d)+exp (-2*c*e) := by
  have hle := exp_le_exp.mpr (show -c*B ≤ -c*d-c*e by nlinarith [mul_nonneg hc.le (sub_nonneg.mpr h)])
  rw [show -c*d-c*e = -c*d+(-c*e) by ring,exp_add] at hle
  rw [show -2*c*d = -c*d+(-c*d) by ring,show -2*c*e = -c*e+(-c*e) by ring,exp_add,exp_add]
  nlinarith [sq_nonneg (exp (-c*d)-exp (-c*e))]

/-- A geometric sum on the odd lattice, including the factor sinh(c). -/
theorem tail_odd_lattice_sum (N : ℕ) (c : ℝ) :
    2*sinh c * (∑ i : Fin N, exp (-((2:ℝ)*(i:ℕ)+1)*c)) = 1-exp (-2*(N:ℝ)*c) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Fin.sum_univ_castSucc, mul_add]
    simp only [Fin.val_castSucc, Fin.val_last] at *
    rw [ih, Real.sinh_eq]
    push_cast
    have h₁ : exp c * exp (-(2*(N:ℝ)+1)*c) = exp (-2*(N:ℝ)*c) := by rw [← exp_add]; congr 1; ring
    have h₂ : exp (-c) * exp (-(2*(N:ℝ)+1)*c) = exp (-2*((N:ℝ)+1)*c) := by rw [← exp_add]; congr 1; ring
    linarith only [h₁,h₂]

private theorem paired_five (α η : ℝ) (hα : 0 < α) (N : ℕ) (d e : Fin N → ℝ)
    (hd : ∀ i, 0 < d i) (he : ∀ i, 0 < e i) (hp : ∀ i, d i + e i ≤ (2*(i:ℝ)+1)*η) :
    (∑ k ∈ Finset.range 5, ∑ i : Fin N, 4/oddIndex k*exp (-(2*(i:ℝ)+1)*(η*(α*oddIndex k)))) ≤
      ∑ i, (-log (tanh (α*d i)) - log (tanh (α*e i))) := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  have h₁ := log_tanh_five _ (mul_pos hα (hd i))
  have h₂ := log_tanh_five _ (mul_pos hα (he i))
  refine le_trans ?_ (show _ + _ ≤ _ from add_le_add h₁ h₂)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  have hℓ : 0 < oddIndex k := by dsimp [oddIndex]; positivity
  have hk := mul_le_mul_of_nonneg_left (paired_term (α*oddIndex k) _ _ _ (mul_pos hα hℓ) (hp i))
      (show 0 ≤ 2/oddIndex k by positivity)
  convert hk using 1 <;> ring_nf

private theorem one_odd_sum (N : ℕ) (η α ℓ : ℝ) (hη : 0 < η) (hα : 0 < α) (hℓ : 1 ≤ ℓ)
    (hlarge : 7 < 2*(N:ℝ)*η*α) :
    2*(998/1000)*((1/ℓ^2)/(α*η) - α*η/6) ≤
      ∑ i : Fin N, 4/ℓ*exp (-(2*(i:ℝ)+1)*(η*(α*ℓ))) := by
  let c := η*(α*ℓ)
  have hℓ₀ : 0 < ℓ := by linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hl : 7 < 2*(N:ℝ)*c := by
    dsimp [c]
    nlinarith [mul_nonneg (show 0 ≤ 2*(N:ℝ)*η*α by positivity) (sub_nonneg.mpr hℓ)]
  have hexp : 500 < exp (2*(N:ℝ)*c) := by
    have hbase : (5/2:ℝ) < exp 1 := by linarith [Real.exp_one_gt_d9]
    have hpow := pow_lt_pow_left₀ hbase (by norm_num) (by decide : (7:ℕ) ≠ 0)
    have hseven : exp 7 = (exp 1)^7 := by rw [show (7:ℝ)=(7:ℕ)*(1:ℝ) by norm_num,exp_nat_mul]
    apply lt_trans _ (exp_lt_exp.mpr hl)
    rw [hseven]
    norm_num at hpow
    linarith
  have hrem : (998/1000:ℝ) ≤ 1-exp (-2*(N:ℝ)*c) := by
    rw [show -2*(N:ℝ)*c = -(2*(N:ℝ)*c) by ring, exp_neg]
    have := (one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<500) hexp)
    rw [one_div] at this
    linarith only [this]
  rw [← Finset.mul_sum]
  have hsum := tail_odd_lattice_sum N c
  have hsinh := sinh_pos_iff.mpr hc
  have hrat : (4/ℓ) * (∑ i : Fin N, exp (-(2*(i:ℝ)+1)*c)) =
        2/ℓ * (1-exp (-2*(N:ℝ)*c)) * (1/sinh c) := by
    rw [← hsum]
    generalize (∑ i : Fin N, exp (-(2*(i:ℝ)+1)*c)) = T
    field_simp
    <;> ring
  rw [show η*(α*ℓ)=c by rfl, hrat]
  calc
    _ = (2/ℓ*(998/1000))*(1/c-c/6) := by dsimp [c]; field_simp
    _ ≤ (2/ℓ*(998/1000))*(1/sinh c) := by gcongr; exact inv_sinh_lower _ hc
    _ ≤ _ := by gcongr

/-- The five odd powers in the logarithmic expansion suffice for the node bound. -/
theorem tail_paired_log_bound (j : ℕ) (hj : 225 ≤ j) (η : ℝ)
    (hη : η = Real.pi/Real.sqrt (2*(j:ℝ)-1125/100)) (N : ℕ) (hN : N = ⌊3/η⌋₊)
    (d e : Fin N → ℝ) (hd : ∀ i, 0 < d i) (he : ∀ i, 0 < e i)
    (hp : ∀ i, d i + e i ≤ (2*(i:ℝ)+1)*η) :
    608/1000*Real.sqrt (2*(j:ℝ)-1125/100)-315/1000 <
      ∑ i, (-Real.log (Real.tanh ((11*Real.pi/28)*d i)) - Real.log (Real.tanh ((11*Real.pi/28)*e i))) := by
  let H := sqrt (2*(j:ℝ)-1125/100)
  let α := 11*Real.pi/28
  have hj' : (225:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  have hH : 209/10 < H := by
    have hsq : H^2 = 2*(j:ℝ)-1125/100 := sq_sqrt (by linarith)
    have hn : 0 ≤ H := sqrt_nonneg _
    nlinarith
  have hH₀ : 0 < H := by linarith
  have hη' : η = Real.pi/H := hη
  have hη₀ : 0 < η := hη' ▸ div_pos pi_pos hH₀
  have hηup : η < 151/1000 := by rw [hη',div_lt_iff₀ hH₀]; linarith [pi_lt_d4]
  have hαlo : 123/100 < α := by dsimp [α]; linarith [pi_gt_d4]
  have hαhi : α < 1235/1000 := by dsimp [α]; linarith [pi_lt_d4]
  have hα : 0 < α := by linarith
  have hNlo : 3-η < (N:ℝ)*η := by
    have ht := Nat.lt_floor_add_one (3/η)
    rw [← hN, div_lt_iff₀ hη₀] at ht
    linarith
  have hlarge : 7 < 2*(N:ℝ)*η*α := by
    nlinarith only [mul_lt_mul_of_pos_right hNlo hα, mul_lt_mul_of_pos_right hηup hα,
      hαlo]
  have hsum' : (∑ k ∈ Finset.range 5, 2*(998/1000)*((1/(oddIndex k)^2)/(α*η)-α*η/6)) ≤ _ :=
    Finset.sum_le_sum (s := Finset.range 5) (fun k _ => one_odd_sum N η α (oddIndex k)
      hη₀ hα (by dsimp [oddIndex]; have := Nat.cast_nonneg (α:=ℝ) k; linarith) hlarge)
  apply lt_of_lt_of_le _ (hsum'.trans (paired_five α η hα N d e hd he hp))
  have hden : α*Real.pi < 3879/1000 := by
    dsimp [α]
    nlinarith [mul_pos (sub_pos.mpr pi_lt_d4) (show 0 < 3.1416+Real.pi by positivity)]
  have hcoef : (608/1000)*H < 2*(998/1000)*(117469/99225)/(α*η) := by
    rw [hη', lt_div_iff₀ (by positivity)]
    field_simp
    nlinarith
  have herr : 2*(998/1000)*5*(α*η/6) < 315/1000 := by
    have hprod := mul_lt_mul_of_pos_right hαhi hη₀
    nlinarith
  have htotal : (∑ k ∈ Finset.range 5, 2*(998/1000)*((1/(oddIndex k)^2)/(α*η)-α*η/6)) =
      2*(998/1000)*(117469/99225)/(α*η)-2*(998/1000)*5*(α*η/6) := by
    norm_num [Finset.sum_range_succ, oddIndex, div_eq_mul_inv]
    ring
  rw [htotal]
  change 608/1000*H-315/1000 < _
  linarith only [hcoef,herr]

end Turan
