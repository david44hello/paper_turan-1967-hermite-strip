-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.TailDefs
import Turan.Degree
import Turan.RealZeros
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace Turan

private def rootProduct (s : Multiset ℂ) : Polynomial ℂ := (s.map (X - C ·)).prod

private theorem norm_sum_derivatives_le (s : Multiset ℂ) (f : ℂ → Polynomial ℂ)
    (z : ℂ) (k : ℕ) (B : ℝ) (h : ∀ w ∈ s, ‖(derivative^[k] (f w)).eval z‖ ≤ B) :
    ‖(derivative^[k] (s.map f).sum).eval z‖ ≤ s.card * B := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons w s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ← Module.End.pow_apply, map_add, eval_add,
      Multiset.card_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    simp only [Module.End.pow_apply]
    exact (norm_add_le _ _).trans ((add_le_add (h w (Multiset.mem_cons_self ..))
      (ih fun u hu => h u (Multiset.mem_cons_of_mem hu))).trans_eq (add_comm ..))

/-- Differentiating a product removes one factor for each occurrence of a root. -/
theorem polynomial_derivatives_of_root_distance (p : Polynomial ℂ) (z : ℂ) (m k : ℕ)
    (K : ℝ) (hK : 0 ≤ K) (hm : p.natDegree ≤ m)
    (hd : ∀ w ∈ p.roots, 1 ≤ K * ‖z - w‖) :
    ‖(derivative^[k] p).eval z‖ ≤ (m * K) ^ k * ‖p.eval z‖ := by
  have bound (s : Multiset ℂ) (hs : s.card ≤ m) (h : ∀ w ∈ s, 1 ≤ K * ‖z-w‖) :
      ‖(derivative^[k] (rootProduct s)).eval z‖ ≤ (m*K)^k * ‖(rootProduct s).eval z‖ := by
    induction k generalizing s with
    | zero => simp
    | succ k ih =>
      have hder : (rootProduct s).derivative = (s.map fun w => rootProduct (s.erase w)).sum := by
        simp only [rootProduct, derivative_prod, derivative_X_sub_C, mul_one]
      rw [Function.iterate_succ_apply, hder]
      calc
        _ ≤ s.card * ((m*K)^k * (K * ‖(rootProduct s).eval z‖)) := by
          apply norm_sum_derivatives_le
          intro w hw
          have hsub := Multiset.erase_le w s
          refine (ih (s.erase w) ((Multiset.card_le_card hsub).trans hs)
            (fun u hu => h u (Multiset.mem_of_le hsub hu))).trans ?_
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hcons : rootProduct s = (X-C w)*rootProduct (s.erase w) := by
            conv_lhs => rw [← Multiset.cons_erase hw]
            simp [rootProduct]
          rw [hcons, eval_mul, eval_sub, eval_X, eval_C, norm_mul, ← mul_assoc]
          exact le_mul_of_one_le_left (norm_nonneg _) (h w hw)
        _ ≤ (m*K)^(k+1) * ‖(rootProduct s).eval z‖ := by
          rw [pow_succ]
          calc
            _ ≤ (m:ℝ) * ((m*K)^k * (K * ‖(rootProduct s).eval z‖)) := by gcongr
            _ = _ := by ring
  have hfac : p = C p.leadingCoeff * rootProduct p.roots := (IsAlgClosed.splits p).eq_prod_roots
  have hp := bound p.roots ((card_roots' p).trans hm) hd
  calc
    _ = ‖p.leadingCoeff‖ * ‖(derivative^[k] (rootProduct p.roots)).eval z‖ := by
      conv_lhs => rw [hfac, iterate_derivative_C_mul, eval_mul, eval_C, norm_mul]
    _ ≤ ‖p.leadingCoeff‖ * ((m*K)^k * ‖(rootProduct p.roots).eval z‖) :=
      mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = _ := by
      conv_rhs => rw [hfac, eval_mul, eval_C, norm_mul]
      ring

private def scale (n : ℕ) : ℝ := Real.sqrt (2^n * (n.factorial:ℝ))

private theorem scale_sq (n : ℕ) : scale n ^ 2 = 2^n * (n.factorial:ℝ) := by
  apply Real.sq_sqrt
  positivity

private theorem scale_pos (n : ℕ) : 0 < scale n := by
  have := Nat.factorial_pos n
  unfold scale
  positivity

private theorem family_scaled_eval (n m : ℕ) (a b z : ℂ) :
    (family n m (a / scale n) (b / scale m)).eval z = normalizedFamily n m a b z := by
  simp [family, normalizedFamily, psi, scale, eval_add, eval_mul]
  ring

/-- The width difference 0.87 - 0.76 gives the root-distance estimate for every derivative order. -/
private theorem recover_derivatives (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m) (a b c : ℂ)
    (hs : emptyStrip (normalizedFamily n m a b) (87/100)) (hy : |c.im| < 76/100) (k : ℕ) :
    let p := family n m (a / scale n) (b / scale m)
    ‖(derivative^[k] p).eval c‖ ≤ ((m:ℝ)*(100/11))^k * ‖p.eval c‖ := by
  dsimp only
  apply polynomial_derivatives_of_root_distance _ _ _ _ _ (by norm_num)
  · rw [family_degree n m hn hnm]
    split_ifs <;> omega
  · intro w hw
    have he := isRoot_of_mem_roots hw
    change (family n m _ _).eval w = 0 at he
    rw [family_scaled_eval] at he
    have hout : 87/100 ≤ |w.im| := le_of_not_gt fun hin => hs w hin he
    have him := Complex.abs_im_le_norm (c - w)
    rw [Complex.sub_im, abs_sub_comm] at him
    have htri := abs_sub_abs_le_abs_sub w.im c.im
    linarith

private def osc (p : Polynomial ℂ) : Polynomial ℂ :=
  C (1/2) * p.derivative.derivative - X * p.derivative

private theorem osc_add (p q : Polynomial ℂ) : osc (p+q) = osc p + osc q := by
  simp only [osc, derivative_add]
  ring

private theorem osc_C_mul (a : ℂ) (p : Polynomial ℂ) : osc (C a*p) = C a*osc p := by
  simp only [osc, derivative_C_mul]
  ring

private theorem osc_H (j : ℕ) : osc (hermite j) = -C (j:ℂ)*hermite j := by
  apply Polynomial.funext
  intro z
  have he := congrArg (eval z) (hermite_equation j)
  simp only [osc, eval_mul, eval_X, eval_C, eval_neg, eval_sub, eval_ofNat, eval_natCast,
    nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] at he ⊢
  linear_combination he / 2

private theorem osc_const (a : ℂ) : osc (C a) = 0 := by simp [osc]

private theorem osc_X : osc X = -X := by simp [osc]

private theorem recover_identities (n m : ℕ) (A B c : ℂ) :
    let p := family n m A B
    let N := (n:ℂ)
    let M := (m:ℂ)
    2*(N-1)*(M-1) = N*M*p.derivative.eval c + (N+M)*(osc p).derivative.eval c +
      (osc (osc p)).derivative.eval c ∧
    (M-N)*A*(hermite n).derivative.eval c =
      M*p.derivative.eval c + (osc p).derivative.eval c - 2*(M-1) := by
  let p := family n m A B
  let N := (n:ℂ)
  let M := (m:ℂ)
  have hform : p = C 1 + C 2*X + C A*hermite n + C B*hermite m := by simp [p, family, map_ofNat]
  have hE : osc p = C (-2)*X + C (-N*A)*hermite n + C (-M*B)*hermite m := by
    rw [hform]
    simp only [osc_add, osc_const, osc_C_mul, osc_H, osc_X]
    simp only [map_neg, map_mul, N, M]
    ring
  have hEE : osc (osc p) = C 2*X + C (N^2*A)*hermite n + C (M^2*B)*hermite m := by
    rw [hE]
    simp only [osc_add, osc_C_mul, osc_H, osc_X]
    simp only [map_neg, map_mul, map_pow, N, M]
    ring
  change _ = _ * _ * p.derivative.eval c + _ * (osc p).derivative.eval c +
    (osc (osc p)).derivative.eval c ∧ _ = _ * p.derivative.eval c + (osc p).derivative.eval c - _
  rw [hEE, hE, hform]
  simp only [derivative_add, derivative_C, derivative_C_mul, derivative_X, mul_one, eval_add,
    eval_zero, eval_C, eval_mul, N, M]
  constructor <;> ring

private theorem osc_first (p : Polynomial ℂ) (c : ℂ) :
    (osc p).derivative.eval c =
      (1/2)*p.derivative.derivative.derivative.eval c -
        c*p.derivative.derivative.eval c - p.derivative.eval c := by
  simp only [osc, derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add, derivative_X, one_mul,
    eval_sub, eval_mul, eval_add, eval_X, eval_C]
  ring

private theorem osc_second (p : Polynomial ℂ) (c : ℂ) :
    (osc (osc p)).derivative.eval c =
      (1/4)*p.derivative.derivative.derivative.derivative.derivative.eval c -
      c*p.derivative.derivative.derivative.derivative.eval c +
      (c^2-2)*p.derivative.derivative.derivative.eval c +
      3*c*p.derivative.derivative.eval c + p.derivative.eval c := by
  simp only [osc, derivative_sub, derivative_add, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_X, one_mul, eval_sub, eval_add, eval_mul, eval_X, eval_C]
  ring

private theorem recover_operator_bounds (p : Polynomial ℂ) (c : ℂ) (M : ℝ) (hm : 450 ≤ M)
    (hc : ‖c‖ ≤ 11/5)
    (hb : ∀ k : ℕ, ‖(derivative^[k] p).eval c‖ ≤ (M*(100/11))^k * ‖p.eval c‖) :
    ‖(osc p).derivative.eval c‖ ≤ 400*M^3 * ‖p.eval c‖ ∧
    ‖(osc (osc p)).derivative.eval c‖ ≤ 16000*M^5 * ‖p.eval c‖ := by
  let d (k : ℕ) := (derivative^[k] p).eval c
  let V := M*(100/11)
  let T := ‖p.eval c‖
  have hd (k : ℕ) : ‖d k‖ ≤ V^k*T := hb k
  have hM : 0 ≤ M := by linarith
  have hc2 : ‖c^2-2‖ ≤ 7 := by
    refine (norm_sub_le ..).trans ?_
    rw [norm_pow, Complex.norm_ofNat]
    nlinarith [sq_le_sq₀ (norm_nonneg c) (by norm_num : (0:ℝ) ≤ 11/5) |>.mpr hc]
  have hfirst : ‖(osc p).derivative.eval c‖ ≤
      (1/2*V^3 + (11/5)*V^2 + V)*T := by
    rw [osc_first]
    change ‖(1/2:ℂ)*d 3-c*d 2-d 1‖ ≤ _
    grw [norm_sub_le, norm_sub_le]
    simp only [norm_mul, norm_div, norm_one, Complex.norm_ofNat]
    calc
      _ ≤ (1/2)*(V^3*T) + (11/5)*(V^2*T) + V^1*T := by gcongr <;> apply hd
      _ = _ := by ring
  have hsecond : ‖(osc (osc p)).derivative.eval c‖ ≤
      (1/4*V^5 + (11/5)*V^4 + 7*V^3 + (33/5)*V^2 + V)*T := by
    rw [osc_second]
    change ‖(1/4:ℂ)*d 5-c*d 4+(c^2-2)*d 3+3*c*d 2+d 1‖ ≤ _
    grw [norm_add_le, norm_add_le, norm_add_le, norm_sub_le]
    simp only [norm_mul, norm_div, norm_one, Complex.norm_ofNat]
    calc
      _ ≤ (1/4)*(V^5*T)+(11/5)*(V^4*T)+7*(V^3*T)+3*(11/5)*(V^2*T)+V^1*T := by
        gcongr <;> apply hd
      _ = _ := by ring
  obtain ⟨t, ht, htM⟩ := exists_nonneg_add_of_le hm
  constructor
  · apply hfirst.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply sub_nonneg.mp
    dsimp [V]
    rw [← htM]
    ring_nf
    positivity
  · apply hsecond.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply sub_nonneg.mp
    dsimp [V]
    rw [← htM]
    ring_nf
    positivity

/-- Projection onto the real axis decreases every linear factor of a real-rooted polynomial. -/
theorem norm_eval_re_le (p : Polynomial ℂ) (hreal : ∀ w ∈ p.roots, w.im = 0) (z : ℂ) :
    ‖p.eval (z.re : ℂ)‖ ≤ ‖p.eval z‖ := by
  have hprod (s : Multiset ℂ) (hs : ∀ w ∈ s, w.im = 0) :
      ‖(s.map ((z.re:ℂ) - ·)).prod‖ ≤ ‖(s.map (z - ·)).prod‖ := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons w s ih =>
      have hw : w = (w.re : ℂ) := Complex.ext rfl (hs w (Multiset.mem_cons_self ..))
      have hwle : ‖(z.re:ℂ) - w‖ ≤ ‖z-w‖ := by
        conv_lhs => rw [hw, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact Complex.abs_re_le_norm (z-w)
      simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact mul_le_mul hwle (ih fun u hu => hs u (Multiset.mem_cons_of_mem hu))
        (norm_nonneg _) (norm_nonneg _)
  simp only [(IsAlgClosed.splits p).eval_eq_prod_roots, norm_mul]
  exact mul_le_mul_of_nonneg_left (hprod _ hreal) (norm_nonneg _)

private def valR (n : ℕ) (x : ℝ) := ((hermite n).eval (x:ℂ)).re
private def slopeR (n : ℕ) (x : ℝ) := ((hermite n).derivative.eval (x:ℂ)).re

private theorem valR_step (n : ℕ) (x : ℝ) :
    valR (n+2) x = 2*x*valR (n+1) x - 2*(n+1:ℝ)*valR n x := by
  rw [valR, hermite, eval_sub, eval_smul]
  simp [valR, eval_mul, nsmul_eq_mul, Complex.mul_re, Complex.mul_im]

private theorem slopeR_succ (n : ℕ) (x : ℝ) :
    slopeR (n+1) x = 2*(n+1:ℝ)*valR n x := by
  simp [slopeR, valR, hermite_derivative, nsmul_eq_mul, Complex.mul_re]

/-- The Hermite recurrence gives a positive lower bound for its consecutive determinant.
The additional term in the induction is twice a real square. -/
private theorem hermite_determinant (n : ℕ) (x : ℝ) :
    2^(n+1)*(n.factorial:ℝ) ≤ valR (n+1) x ^ 2 - valR n x * valR (n+2) x := by
  induction n with
  | zero => simp [valR, hermite, eval_mul, Complex.mul_re]; ring_nf; rfl
  | succ n ih =>
    have hid : valR (n+2) x^2 - valR (n+1) x * valR (n+3) x =
        2*(valR (n+1) x)^2 +
        2*(n+1:ℝ)*(valR (n+1) x^2 - valR n x * valR (n+2) x) := by
      rw [valR_step (n+1)]
      push_cast
      linear_combination valR (n+2) x * (valR_step n x)
    rw [hid, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ _ (n+1)]
    nlinarith only [mul_le_mul_of_nonneg_left ih (show 0 ≤ 2*(n+1:ℝ) by positivity),
      sq_nonneg (valR (n+1) x)]

/-- A lower bound for the oscillator energy. At zero the mixed term vanishes. -/
private theorem oscillator_energy_lower (n : ℕ) (hn : 0 < n) (x : ℝ) :
    scale n^2 ≤ (n:ℝ)*valR n x^2 - x*valR n x*slopeR n x + slopeR n x^2/2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have h := mul_le_mul_of_nonneg_left (hermite_determinant k x)
    (show 0 ≤ (k:ℝ)+1 by positivity)
  rw [scale_sq, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, slopeR_succ]
  rw [valR_step k] at h
  simp only [Nat.succ_eq_add_one] at *
  linarith only [h]

/-- The normalized oscillator energy at zero is at least 1/n. -/
theorem recover_energy_at_zero (n : ℕ) (hn : 0 < n) :
    1 ≤ (n:ℝ)*‖psi n 0‖^2 + ‖deriv (psi n) 0‖^2/2 := by
  have he := oscillator_energy_lower n hn 0
  have HD : HasDerivAt (psi n) ((hermite n).derivative.eval 0 / (scale n:ℂ)) 0 :=
    ((hermite n).hasDerivAt 0).div_const _
  rw [HD.deriv]
  change 1 ≤ (n:ℝ)*‖(hermite n).eval 0 / (scale n:ℂ)‖^2 + _
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (scale_pos n), div_pow]
  field_simp [ne_of_gt (scale_pos n)]
  apply (le_div_iff₀ (sq_pos_of_pos (scale_pos n))).mpr
  have hu := Complex.abs_re_le_norm ((hermite n).eval 0)
  have hv := Complex.abs_re_le_norm ((hermite n).derivative.eval 0)
  simp [valR, slopeR] at he
  have hu2 := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hu
  have hv2 := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hv
  rw [sq_abs] at hu2 hv2
  nlinarith only [he, mul_le_mul_of_nonneg_left hu2 (Nat.cast_nonneg n : (0:ℝ) ≤ n), hv2]

private theorem recovery_size_arithmetic {N M T : ℝ}
    (hn : 2 ≤ N) (hm : 450 ≤ M) (hT : 0 < T)
    (h : 2*(N-1)*(M-1) ≤ (N*M*(10*M)+(N+M)*(400*M^3)+16000*M^5)*T) :
    1 < 9000*M^4*T := by
  have hcoef : N*M*(10*M)+(N+M)*(400*M^3)+16000*M^5 <
      2*(N-1)*(M-1)*(9000*M^4) := by
    obtain ⟨u, hu, hu'⟩ := exists_nonneg_add_of_le hn
    obtain ⟨v, hv, hv'⟩ := exists_nonneg_add_of_le hm
    apply sub_pos.mp
    rw [← hu', ← hv']
    ring_nf
    positivity
  have hprod := h.trans_lt (mul_lt_mul_of_pos_right hcoef hT)
  have hpos : 0 < 2*(N-1)*(M-1) := by
    have : 0 < N-1 := by linarith
    have : 0 < M-1 := by linarith
    positivity
  apply (mul_lt_mul_iff_right₀ hpos).mp
  linarith only [hprod]

private theorem recovery_slope_arithmetic {N M T S : ℝ} (hm : 450 ≤ M) (hh : 2*N ≤ M)
    (hT : 0 < T) (hsize : 1 < 9000*M^4*T) (hS : 0 ≤ S)
    (h : (M-N)*S ≤ (M*(10*M)+400*M^3)*T+2*(M-1)) : S ≤ 50000*M^4*T := by
  have hpoly : M*(10*M) + 400*M^3 ≤ 1000*M^5 := by
    obtain ⟨v, hv, hv'⟩ := exists_nonneg_add_of_le hm
    apply sub_nonneg.mp
    rw [← hv']
    ring_nf
    positivity
  have hleft := mul_le_mul_of_nonneg_right (show M/2 ≤ M-N by linarith) hS
  have hconst := mul_le_mul_of_nonneg_left hsize.le (show 0 ≤ 2*M by linarith)
  have hsmall := mul_le_mul_of_nonneg_right hpoly hT.le
  apply (mul_le_mul_iff_right₀ (show 0 < M/2 by linarith)).mp
  nlinarith only [hleft, h, hconst, hsmall, (show 0 ≤ M^5*T by positivity)]

private theorem recover_quantities (n m : ℕ) (hn : 2 ≤ n) (hm : 450 ≤ m) (hh : 2*n ≤ m)
    (A B c : ℂ) (hc : ‖c‖ ≤ 11/5)
    (hval : 1+2*c+A*(hermite n).eval c = 0) :
    let p := family n m A B
    0 < ‖p.eval c‖ →
    (∀ k : ℕ, ‖(derivative^[k] p).eval c‖ ≤ ((m:ℝ)*(100/11))^k * ‖p.eval c‖) →
    1 < 9000*(m:ℝ)^4*‖p.eval c‖ ∧
    ‖A‖*max ‖(hermite n).eval c‖ ‖(hermite n).derivative.eval c‖ ≤ 50000*(m:ℝ)^4*‖p.eval c‖ := by
  intro p hT hb
  let N : ℝ := n
  let M : ℝ := m
  let T := ‖p.eval c‖
  have hn' : 2 ≤ N := by dsimp [N]; exact_mod_cast hn
  have hm' : 450 ≤ M := by dsimp [M]; exact_mod_cast hm
  have hh' : 2*N ≤ M := by dsimp [N,M]; exact_mod_cast hh
  have hNm : 0 ≤ M-N := by linarith
  have hN : 0 ≤ N := by linarith
  have hM : 0 ≤ M := by linarith
  have hT' : 0 ≤ T := hT.le
  have h1 : ‖p.derivative.eval c‖ ≤ 10*M*T := by
    refine (hb 1).trans ?_
    rw [pow_one]
    change M*(100/11)*T ≤ 10*M*T
    apply mul_le_mul_of_nonneg_right _ hT'
    linarith only [hM]
  obtain ⟨h3,h5⟩ := recover_operator_bounds p c M hm' hc hb
  obtain ⟨hid,ha⟩ := recover_identities n m A B c
  have hNorm1 : ‖((N:ℂ)-1)‖ = N-1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  have hNorm2 : ‖((M:ℂ)-1)‖ = M-1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  have hNormAdd : ‖(N:ℂ)+(M:ℂ)‖ = N+M := by
    rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hNormSub : ‖(M:ℂ)-(N:ℂ)‖ = M-N := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hNm]
  have id₁ : 2*((N:ℂ)-1)*((M:ℂ)-1) = (N:ℂ)*M*p.derivative.eval c +
      ((N:ℂ)+M)*(osc p).derivative.eval c + (osc (osc p)).derivative.eval c := by
    simpa only [N, M, Complex.ofReal_natCast] using hid
  have id₂ : ((M:ℂ)-(N:ℂ))*A*(hermite n).derivative.eval c =
      (M:ℂ)*p.derivative.eval c+(osc p).derivative.eval c-2*((M:ℂ)-1) := by
    simpa only [N, M, Complex.ofReal_natCast] using ha
  have hsize : 1 < 9000*M^4*T := by
    apply recovery_size_arithmetic hn' hm' hT
    have h := congrArg norm id₁
    simp only [norm_mul, Complex.norm_ofNat, hNorm1, hNorm2] at h
    rw [h]
    grw [norm_add_le, norm_add_le]
    simp only [norm_mul, hNormAdd, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN,
      abs_of_nonneg hM]
    calc
      _ ≤ N*M*(10*M*T)+(N+M)*(400*M^3*T)+16000*M^5*T := by gcongr
      _ = _ := by ring
  refine ⟨hsize, ?_⟩
  rw [mul_max_of_nonneg _ _ (norm_nonneg A), max_le_iff]
  constructor
  · have ha0 : A*(hermite n).eval c = -(1+2*c) := by linear_combination hval
    have hval' : ‖A‖*‖(hermite n).eval c‖ ≤ 1+2*‖c‖ := by
      rw [← norm_mul, ha0, norm_neg]
      simpa only [norm_mul, norm_one, Complex.norm_ofNat] using norm_add_le (1:ℂ) (2*c)
    change _ ≤ 50000*M^4*T
    linarith only [hc, hval', hsize]
  · apply recovery_slope_arithmetic hm' hh' hT hsize (by positivity)
    have h := congrArg norm id₂
    simp only [norm_mul, hNormSub] at h
    rw [← mul_assoc, h]
    grw [norm_sub_le, norm_add_le]
    simp only [norm_mul, hNorm2, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hM]
    calc
      _ ≤ M*(10*M*T)+400*M^3*T+2*(M-1) := by gcongr
      _ = _ := by ring

private theorem scale_le_hermite_max (n m : ℕ) (hn : 2 ≤ n) (hnm : n+3 ≤ m)
    (c : ℂ) (hx : |c.re| ≤ 2) :
    scale n ≤ Real.sqrt (m:ℝ) * max ‖(hermite n).eval c‖ ‖(hermite n).derivative.eval c‖ := by
  let Q := max ‖(hermite n).eval c‖ ‖(hermite n).derivative.eval c‖
  let u := valR n c.re
  let v := slopeR n c.re
  have hQ : 0 ≤ Q := (norm_nonneg _).trans (le_max_left ..)
  have hu : |u| ≤ Q := by
    apply (Complex.abs_re_le_norm _).trans
    refine (norm_eval_re_le _ ?_ c).trans (le_max_left ..)
    exact fun w hw => (hermite_real_simple n w (isRoot_of_mem_roots hw)).1
  have hv : |v| ≤ Q := by
    apply (Complex.abs_re_le_norm _).trans
    refine (norm_eval_re_le _ ?_ c).trans (le_max_right ..)
    intro w hw
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    have he := isRoot_of_mem_roots hw
    change (hermite (k+1)).derivative.eval w = 0 at he
    rw [hermite_derivative, eval_smul, nsmul_eq_mul] at he
    exact (hermite_real_simple k w ((mul_eq_zero.mp he).resolve_left
      (by exact_mod_cast (show 2*(k+1) ≠ 0 by omega)))).1
  have hu2 : u^2 ≤ Q^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hQ).mpr hu
  have hv2 : v^2 ≤ Q^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hQ).mpr hv
  have hcross : -(c.re*u*v) ≤ 2*Q^2 := by
    apply (neg_le_abs _).trans
    rw [abs_mul, abs_mul, pow_two, ← mul_assoc]
    gcongr
  have he : scale n^2 ≤ (n:ℝ)*u^2 - c.re*u*v + v^2/2 :=
    oscillator_energy_lower n (by omega) c.re
  have hnm' : (n:ℝ)+3 ≤ m := by exact_mod_cast hnm
  apply (sq_le_sq₀ (scale_pos n).le (mul_nonneg (Real.sqrt_nonneg _) hQ)).mp
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  nlinarith only [he, mul_le_mul_of_nonneg_left hu2 (Nat.cast_nonneg n : (0:ℝ) ≤ n),
    hcross, hv2, mul_le_mul_of_nonneg_right hnm' (sq_nonneg Q), sq_nonneg Q]

/-- Recover the size of the normalized family and its lower Hermite coefficient at the trinomial zero. -/
theorem lemma_eleven (n m : ℕ) (hm : 450 ≤ m) (hn : 2 ≤ n) (hhalf : 2*n ≤ m)
    (a b c : ℂ) (hs : emptyStrip (normalizedFamily n m a b) (87/100))
    (hc : 1 + 2*c + a*psi n c = 0) (hx : |c.re| ≤ 2) (hy : |c.im| < 76/100) :
    normalizedFamily n m a b c ≠ 0 ∧
    1 < 9000*(m:ℝ)^4 * ‖normalizedFamily n m a b c‖ ∧
    1+‖a‖ < 110000*(m:ℝ)^((9:ℝ)/2) * ‖normalizedFamily n m a b c‖ := by
  have hne := hs c (show |c.im| < 87/100 by linarith)
  let A := a / (scale n : ℂ)
  let B := b / (scale m : ℂ)
  let p := family n m A B
  let T := ‖p.eval c‖
  let M : ℝ := m
  have hM : 450 ≤ M := by dsimp [M]; exact_mod_cast hm
  have hT : 0 < T := norm_pos_iff.mpr (by rwa [show p.eval c = _ from family_scaled_eval n m a b c])
  have hc' : ‖c‖ ≤ 11/5 := by
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 11/5)).mp
    rw [Complex.sq_norm, Complex.normSq_apply]
    have h1 := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)).mpr hx
    have h2 := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 76/100)).mpr hy.le
    nlinarith [sq_abs c.re, sq_abs c.im]
  have hval : 1+2*c+A*(hermite n).eval c = 0 := by
    dsimp [A, psi, scale] at hc ⊢
    linear_combination hc
  obtain ⟨hsize, hamax⟩ := recover_quantities n m hn hm hhalf A B c hc' hval hT
    (recover_derivatives n m hn (by omega) a b c hs hy)
  have hscale := scale_le_hermite_max n m hn (by omega) c hx
  have hid : ‖a‖ = ‖A‖*scale n := by
    simp [A, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (scale_pos n),
      (scale_pos n).ne']
  have ha : ‖a‖ ≤ 50000*M^4*T*Real.sqrt M := by
    rw [hid]
    calc
      _ ≤ ‖A‖*(Real.sqrt M * max ‖(hermite n).eval c‖ ‖(hermite n).derivative.eval c‖) :=
        mul_le_mul_of_nonneg_left hscale (norm_nonneg _)
      _ = (‖A‖*max ‖(hermite n).eval c‖ ‖(hermite n).derivative.eval c‖)*Real.sqrt M := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hamax (Real.sqrt_nonneg _)
  have hsqrt : 1 ≤ Real.sqrt M := by
    apply (Real.le_sqrt (by norm_num) (by linarith)).mpr
    linarith
  have hrpow : M^((9:ℝ)/2) = M^4 * Real.sqrt M := by
    rw [show (9:ℝ)/2 = 4 + 1/2 by norm_num, Real.rpow_add (by linarith : 0 < M),
      ← Real.sqrt_eq_rpow, Real.rpow_ofNat]
  have hfloor : 0 ≤ M^4*T := mul_nonneg (by positivity) hT.le
  refine ⟨hne, ?_, ?_⟩
  · simpa only [p, A, B, family_scaled_eval] using hsize
  · rw [← family_scaled_eval n m a b c]
    change 1+‖a‖ < 110000*M^((9:ℝ)/2)*T
    rw [hrpow]
    change 1 < 9000*M^4*T at hsize
    nlinarith only [ha, hsize, mul_le_mul_of_nonneg_right hsqrt hfloor, hfloor]

end Turan
