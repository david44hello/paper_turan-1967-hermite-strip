module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.LowerComparison

@[expose] public section

noncomputable section
open Polynomial
open scoped ComplexConjugate
namespace Turan.MehlerJets

theorem step_two_strict_geometry (m x : ℝ) (hm : 450 ≤ m)
    (hlo : Real.sqrt (9*m/5) ≤ x) (z : ℂ) (hz : ‖z-(x:ℂ)‖ = 1/Real.sqrt m) :
    let s := Real.sqrt m
    MonotoneOn (fun t : ℝ => t^2-2*t/s) (Set.Ici (1/s)) ∧
    0 < x-1/s ∧ x-1/s ≤ z.re ∧
    (x-1/s)^2-1/m ≤ z.re^2-z.im^2 ∧
    (x-1/s)^2-1/m = x^2-2*x/s ∧
    9*m/5-2*Real.sqrt (9/5) ≤ x^2-2*x/s ∧
    9*m/5-27/10 < 9*m/5-2*Real.sqrt (9/5) := by
  intro s
  have hm0 : 0 < m := by linarith
  have hs : 0 < s := Real.sqrt_pos.mpr hm0
  have hs2 : s^2 = m := Real.sq_sqrt hm0.le
  let K := Real.sqrt (9/5)
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hK2 : K^2 = 9/5 := Real.sq_sqrt (by norm_num)
  have hK1 : 1 ≤ K := by nlinarith
  have hs1 : 1 < s := by nlinarith
  have hstart : K*s ≤ x := by
    rwa [show 9*m/5 = (9/5)*m by ring, Real.sqrt_mul (by norm_num)] at hlo
  have hrad : 1/s < 1 := (div_lt_one hs).mpr hs1
  have hpos : 1/s < K*s := hrad.trans_le
    (by nlinarith only [hs1,hK1,mul_nonneg (sub_nonneg.mpr hK1) hs.le])
  have hx := hpos.trans_le hstart
  have hre := Complex.abs_re_le_norm (z-(x:ℂ))
  have him := Complex.abs_im_le_norm (z-(x:ℂ))
  rw [hz] at hre him
  change |z.re-x| ≤ 1/s at hre
  change |z.im-0| ≤ 1/s at him
  rw [sub_zero] at him
  have hX : x-1/s ≤ z.re := by linarith [(abs_le.mp hre).1]
  have hY := sq_le_sq.mpr (by rwa [abs_of_pos (one_div_pos.mpr hs)] :
    |z.im| ≤ |1/s|)
  have hmono : MonotoneOn (fun t : ℝ => t^2-2*t/s) (Set.Ici (1/s)) := by
    intro a ha b hb hab
    change 1/s ≤ a at ha
    change 1/s ≤ b at hb
    dsimp
    have h := mul_nonneg (sub_nonneg.mpr hab) (by linarith : 0 ≤ a+b-2*(1/s))
    simp only [div_eq_mul_inv] at h ⊢
    nlinarith only [h]
  have hsq : (1/s)^2 = 1/m := by rw [div_pow, hs2, one_pow]
  have hbase : (K*s)^2-2*(K*s)/s = 9*m/5-2*K := by
    rw [mul_pow, hK2, hs2]; field_simp
  refine ⟨hmono, sub_pos.mpr hx, hX, ?_, ?_, ?_, ?_⟩
  · nlinarith only [hsq, hY, pow_le_pow_left₀ (sub_pos.mpr hx).le hX 2]
  · linear_combination hsq
  · rw [← hbase]
    exact hmono hpos.le hx.le hstart
  · have hK : K < 27/20 := by nlinarith
    change 9*m/5-27/10 < 9*m/5-2*K
    linarith

private theorem high_mode_lower (m : ℕ) (z : ℂ)
    (hphi : 1/(5*Real.sqrt m) < ‖phi m z‖) (hm : 0 < (m:ℝ)) :
    Real.exp ((z.re^2-z.im^2)/2) < (5*Real.sqrt m)*‖psi m z‖ := by
  have he : (-z^2/2).re = -((z.re^2-z.im^2)/2) := by
    norm_num [pow_two, Complex.mul_re, Complex.div_ofNat_re]; ring
  rw [phi, norm_mul, Complex.norm_exp, he, Real.exp_neg] at hphi
  have h := (div_lt_iff₀ (by positivity)).mp hphi
  calc
    _ = Real.exp ((z.re^2-z.im^2)/2)*1 := by ring
    _ < _ := mul_lt_mul_of_pos_left h (Real.exp_pos _)
    _ = _ := by field_simp

theorem step_two_low_mode (n m : ℕ) (hm : 450 ≤ m) (hn : 2*n ≤ m) (x : ℝ)
    (hlo : Real.sqrt (9*(m:ℝ)/5) ≤ x) (z : ℂ)
    (hz : ‖z-(x:ℂ)‖ = 1/Real.sqrt m) (hphi : 1/(5*Real.sqrt m) < ‖phi m z‖) :
    let M := (m:ℝ)
    let E := -(3/5-Real.log 5/4)*M + 9/10 + 5/(12*M)
    let P := (25/24 : ℝ) ^ (1/4 : ℝ)
    ‖psi n z / psi m z‖ < 5*P*Real.sqrt M*Real.exp E ∧
    E < -(197/1000)*M + 901/1000 ∧ 5*P*Real.exp (901/1000) < 25/2 ∧
    ‖psi n z‖ < (25/2)*Real.sqrt M*Real.exp (-(197/1000)*M)*‖psi m z‖ := by
  intro M E P
  have hm' : (450:ℝ) ≤ M := by dsimp [M]; exact_mod_cast hm
  have hm0 : 0 < M := by linarith
  have hh : 2*(n:ℝ) ≤ M := by dsimp [M]; exact_mod_cast hn
  obtain ⟨_,_,_,hXY, hid, hx, hround⟩ := step_two_strict_geometry M x hm' hlo z hz
  have hgeom : 9*M/5-27/10 < z.re^2-z.im^2 := hround.trans_le (hx.trans (hid ▸ hXY))
  have hy := Complex.abs_im_le_norm (z-(x:ℂ))
  rw [hz] at hy
  have hY : z.im^2 ≤ 1/M := by
    have hy' : |z.im| ≤ 1/Real.sqrt M := by simpa using hy
    have h := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hy'
    simpa [div_pow, Real.sq_sqrt hm0.le] using h
  let A := (z.re^2-z.im^2)/2
  let B := z.re^2/6 + z.im^2/4 + (n:ℝ)/2*Real.log 5
  have hlog : Real.log 5 < 1.612 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
    refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 7)
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  have hb : B ≤ E+A := by
    dsimp only [A,B,E]
    rw [show 5/(12*M) = (5/12)*(1/M) by ring]
    linarith only [hgeom, hY, mul_le_mul_of_nonneg_right hh
      (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 5))]
  have hP0 : 0 < P := by dsimp [P]; positivity
  have hP4 : P^4 = 25/24 := by
    dsimp [P]; rw [← Real.rpow_mul_natCast (by norm_num)]; norm_num
  have hP : P < 1.011 := by
    by_contra! h
    have h' := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1.011) h 4
    rw [hP4] at h'; norm_num at h'
  have hc : 5*P*Real.exp (901/1000) < 25/2 := by
    have h := Real.exp_bound' (x := 901/1000) (by norm_num) (by norm_num) (n := 6) (by decide)
    norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h
    nlinarith only [hP, h, mul_lt_mul_of_pos_right hP (Real.exp_pos (901/1000))]
  have hE : E < -(197/1000)*M + 901/1000 := by
    have hy' : 5/(12*M) ≤ 5/(12*450:ℝ) := by gcongr
    dsimp only [E]
    nlinarith only [hy', mul_lt_mul_of_pos_right hlog hm0]
  have hweight : (1-(1:ℝ)/25)^(-(1:ℝ)/4) = P := by
    rw [show (-(1:ℝ)/4) = -(1/4) by ring, Real.rpow_neg (by norm_num),
      ← Real.inv_rpow (by norm_num)]
    norm_num [P]
  have hupper : ‖psi n z‖ ≤ P*Real.exp B := by
    have h := mul_le_mul_of_nonneg_right (lemma_nine n z) (Real.exp_pos (z.re^2/2)).le
    rw [hweight, mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add] at h
    convert h using 1 <;> first | (rw [show -z.re^2/2+z.re^2/2=0 by ring]; simp) | (congr 2; dsimp [B]; ring)
  have hhigh := high_mode_lower m z hphi hm0
  change Real.exp A < _ at hhigh
  have hpos : 0 < ‖psi m z‖ := by
    by_contra! h
    rw [le_antisymm h (norm_nonneg _), mul_zero] at hhigh
    exact (Real.exp_pos A).not_gt hhigh
  have hraw : ‖psi n z‖ < (5*P*Real.sqrt M*Real.exp E)*‖psi m z‖ := calc
    _ ≤ P*Real.exp B := hupper
    _ ≤ P*Real.exp (E+A) := by gcongr
    _ = (P*Real.exp E)*Real.exp A := by rw [Real.exp_add]; ring
    _ < _ := mul_lt_mul_of_pos_left hhigh (by positivity : 0 < P*Real.exp E)
    _ = _ := by ring
  refine ⟨by rwa [norm_div, div_lt_iff₀ hpos], hE, hc, hraw.trans ?_⟩
  apply mul_lt_mul_of_pos_right _ hpos
  calc
    _ < 5*P*Real.sqrt M*Real.exp (-(197/1000)*M+901/1000) := by gcongr
    _ = (5*P*Real.exp (901/1000))*(Real.sqrt M*Real.exp (-(197/1000)*M)) := by rw [Real.exp_add]; ring
    _ < _ := by simpa only [mul_assoc] using mul_lt_mul_of_pos_right hc
                  (by positivity : 0 < Real.sqrt M*Real.exp (-(197/1000)*M))

theorem step_two_affine_arithmetic (m : ℕ) (hm : 450 ≤ m) (x : ℝ)
    (hlo : Real.sqrt (9*(m:ℝ)/5) ≤ x)
    (hhi : x ≤ Real.sqrt (9*(m:ℝ)/5) + 3*Real.pi/Real.sqrt m)
    (z : ℂ) (hz : ‖z-(x:ℂ)‖ = 1/Real.sqrt m)
    (hphi : 1/(5*Real.sqrt m) < ‖phi m z‖) :
    let M := (m:ℝ)
    let s := Real.sqrt M
    let L := 2*Real.sqrt (9/5) + 1/s + (6*Real.pi+2)/M
    ‖1+2*z‖ ≤ L*s ∧ L < 278/100 ∧
    ‖(1+2*z) / psi m z‖ < 14*Real.exp (27/20)*M*Real.exp (-(9/10)*M) ∧
    14*Real.exp (27/20) < 55 ∧ (11/4)*s < Real.exp ((703/1000)*M) ∧
    55*M*Real.exp (-(9/10)*M) < 20*s*Real.exp (-(197/1000)*M) := by
  intro M s L
  have hm' : (450:ℝ) ≤ M := by dsimp [M]; exact_mod_cast hm
  have hm0 : 0 < M := by linarith
  have hs : 0 < s := Real.sqrt_pos.mpr hm0
  have hs2 : s^2=M := Real.sq_sqrt hm0.le
  have hs21 : 21 ≤ s := by nlinarith
  let K := Real.sqrt (9/5)
  have hKpos : 0 ≤ K := Real.sqrt_nonneg _
  have hK2 : K^2=9/5 := Real.sq_sqrt (by norm_num)
  have hK : K < 1.342 := by nlinarith
  have hxpos : 0 ≤ x := (Real.sqrt_nonneg _).trans hlo
  have hxs : x ≤ K*s + 3*Real.pi/s := by
    rwa [show 9*(m:ℝ)/5=(9/5)*(m:ℝ) by ring, Real.sqrt_mul (by norm_num)] at hhi
  have hz' : ‖z‖ ≤ x+1/s := by
    have h := norm_add_le (z-(x:ℂ)) (x:ℂ)
    rw [sub_add_cancel, hz, Complex.norm_of_nonneg hxpos] at h
    linarith
  have hlin : ‖1+2*z‖ ≤ L*s := by
    have h := (norm_add_le (1:ℂ) (2*z))
    norm_num at h
    have he : L*s = 2*K*s + 1 + (6*Real.pi+2)/s := by
      dsimp only [L]; change (2*K+1/s+(6*Real.pi+2)/M)*s = _
      rw [← hs2]; field_simp
    rw [he]
    simp only [div_eq_mul_inv] at hxs hz' ⊢
    nlinarith only [h, hxs, hz']
  have hL : L < 278/100 := by
    have h₁ : 1/s ≤ 1/21 := one_div_le_one_div_of_le (by norm_num) hs21
    have h₂ : (6*Real.pi+2)/M ≤ (6*3.15+2)/450 := by
      apply div_le_div₀ (by positivity) (by linarith only [Real.pi_lt_d2]) (by norm_num) hm'
    dsimp only [L]; change 2*K+1/s+(6*Real.pi+2)/M < _
    linarith only [hK,h₁,h₂]
  obtain ⟨_,_,_,hy, heq, hxy, hround⟩ := step_two_strict_geometry M x hm' hlo z hz
  let A := (z.re^2-z.im^2)/2
  have hA : 9/10*M-27/20 < A := by
    have h := hround.trans_le (hxy.trans (heq ▸ hy))
    dsimp [A]; linarith
  have hhi' := high_mode_lower m z hphi hm0
  have hden : Real.exp A / (5*s) < ‖psi m z‖ := by
    rw [div_lt_iff₀ (by positivity)]
    exact hhi'.trans_eq (mul_comm ..)
  have hlin' : ‖1+2*z‖ < (14/5)*s :=
    hlin.trans_lt (mul_lt_mul_of_pos_right (by linarith only [hL]) hs)
  have hexp : Real.exp (-A) < Real.exp (27/20)*Real.exp (-(9/10)*M) := by
    rw [← Real.exp_add, Real.exp_lt_exp]; linarith
  have h55 : 14*Real.exp (27/20) < 55 := by
    have hu := Real.exp_bound' (x:=27/40) (by norm_num) (by norm_num) (n:=5) (by decide)
    norm_num [Finset.sum_range_succ,Nat.factorial_succ] at hu
    rw [show (27/20:ℝ)=27/40+27/40 by norm_num, Real.exp_add]
    nlinarith only [mul_self_le_mul_self (Real.exp_pos _).le hu]
  have hgap : (11/4)*s < Real.exp ((703/1000)*M) := by
    have h := Real.add_one_le_exp ((703/1000)*M)
    nlinarith only [h, hs2, sq_nonneg (s-2), hm']
  refine ⟨hlin,hL,?_,h55,hgap,?_⟩
  · rw [norm_div]
    calc
      _ < ((14/5)*s)/(Real.exp A/(5*s)) :=
        div_lt_div₀ hlin' hden.le (by positivity) (by positivity)
      _ = 14*M*Real.exp (-A) := by rw [Real.exp_neg, ← hs2]; field_simp
      _ < _ := (mul_lt_mul_of_pos_left hexp (by positivity : 0 < 14*M)).trans_eq (by ring)
  · have h := mul_lt_mul_of_pos_right hgap (by positivity : 0 < 20*s*Real.exp (-(9/10)*M))
    calc
      _ = ((11/4)*s)*(20*s*Real.exp (-(9/10)*M)) := by rw [← hs2]; ring
      _ < _ := h
      _ = _ := by
        rw [mul_left_comm (Real.exp _), ← Real.exp_add]
        congr 2
        ring

end Turan.MehlerJets
