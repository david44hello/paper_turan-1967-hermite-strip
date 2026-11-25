-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.LowerTailRealEnergy
import Turan.SlotDefs

noncomputable section
open Polynomial
namespace Turan.RecoveryDetails

def normalizedPoly (n m : ℕ) (a b : ℂ) : Polynomial ℂ :=
  family n m (a / (Real.sqrt (2^n * (n.factorial:ℝ)) : ℂ))
    (b / (Real.sqrt (2^m * (m.factorial:ℝ)) : ℂ))

def D (m : ℕ) : ℝ := 100*(m:ℝ)/11

def jetBound (p : Polynomial ℂ) (c : ℂ) (m : ℕ) : Prop :=
  p.eval c ≠ 0 ∧ ∀ k : ℕ, 1 ≤ k → k ≤ 5 →
    ‖(derivative^[k] p).eval c / p.eval c‖ ≤ D m ^ k


theorem recovery_geometry (m : ℕ) (hm : 450 ≤ m) (c : ℂ)
    (hx : |c.re| ≤ 2) (hy : |c.im| < 0.76) :
    ‖c‖ < Real.sqrt (4+0.76^2) ∧ Real.sqrt (4+0.76^2) < 2.14 ∧ 4090 ≤ D m := by
  have hm' : 450 ≤ (m:ℝ) := by exact_mod_cast hm
  have h₁ := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)).mpr hx
  have h₂ := (sq_lt_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 0.76)).mpr hy
  rw [sq_abs] at h₁ h₂
  refine ⟨(Real.lt_sqrt (norm_nonneg c)).mpr ?_, ?_, ?_⟩
  · rw [Complex.sq_norm, Complex.normSq_apply]
    linarith
  · apply (Real.sqrt_lt' (by norm_num)).mpr
    norm_num
  · unfold D
    linarith

def reciprocalTerms (m : ℕ) : Fin 3 → ℝ :=
  ![D m / (m:ℝ)^4, (1/2+1/(m:ℝ))*0.501*(D m)^3/(m:ℝ)^4,
    0.251*(D m)^5/(2*(m:ℝ))/(m:ℝ)^4]

private theorem reciprocal_forms (m : ℕ) (hm : 0 < (m:ℝ)) :
    let u := 1/(m:ℝ)
    reciprocalTerms m 0 = (100/11)*u^3 ∧
    reciprocalTerms m 1 = (1/2+u)*0.501*(100/11)^3*u ∧
    reciprocalTerms m 2 = 0.251*(100/11)^5/2 := by
  dsimp [reciprocalTerms, D]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp

theorem reciprocal_arithmetic (m : ℕ) (hm : 450 ≤ m) :
    reciprocalTerms m 0 < 1/1000000 ∧
    reciprocalTerms m 1 < 0.50223*0.501*(100/11)^3/(m:ℝ) ∧
    0.50223*0.501*(100/11)^3/(m:ℝ) < 0.43 ∧
    reciprocalTerms m 2 = 0.251*(100/11)^5/2 ∧ (0.251:ℝ)*(100/11)^5/2 < 7792.6 ∧
    (∀ k : Fin 3, AntitoneOn (fun t => reciprocalTerms t k) (Set.Ici 450)) ∧
    1/(1-1/(m:ℝ)) ≤ 1.0023 := by
  have hM : 450 ≤ (m:ℝ) := by exact_mod_cast hm
  have hpos : 0 < (m:ℝ) := by linarith
  have hu : 1/(m:ℝ) ≤ 1/450 := one_div_le_one_div_of_le (by norm_num) hM
  obtain ⟨h₀,h₁,h₂⟩ := reciprocal_forms m hpos
  refine ⟨?_, ?_, ?_, h₂, by norm_num, ?_, ?_⟩
  · rw [h₀]
    calc
      _ ≤ (100/11)*(1/450:ℝ)^3 := by gcongr
      _ < _ := by norm_num
  · rw [h₁, div_eq_mul_one_div (0.50223*0.501*(100/11)^3) (m:ℝ)]
    have h : 1/2 + 1/(m:ℝ) < 0.50223 := by linarith only [hu]
    gcongr
  · rw [div_eq_mul_one_div]
    calc
      _ ≤ (0.50223:ℝ)*0.501*(100/11)^3*(1/450) := by gcongr
      _ < _ := by norm_num
  · intro k i hi j hj hij
    have hi' : 0 < (i:ℝ) := by exact_mod_cast (show 0 < i by change 450 ≤ i at hi; omega)
    have hj' : 0 < (j:ℝ) := hi'.trans_le (by exact_mod_cast hij)
    have hji := one_div_le_one_div_of_le hi' (show (i:ℝ) ≤ j by exact_mod_cast hij)
    obtain ⟨i₀,i₁,i₂⟩ := reciprocal_forms i hi'
    obtain ⟨j₀,j₁,j₂⟩ := reciprocal_forms j hj'
    change reciprocalTerms j k ≤ reciprocalTerms i k
    fin_cases k
    · change reciprocalTerms j 0 ≤ reciprocalTerms i 0
      rw [i₀,j₀]; gcongr
    · change reciprocalTerms j 1 ≤ reciprocalTerms i 1
      rw [i₁,j₁]; gcongr
    · change reciprocalTerms j 2 ≤ reciprocalTerms i 2
      rw [i₂,j₂]
  · apply (div_le_iff₀ (by linarith only [hu] : 0 < 1-1/(m:ℝ))).mpr
    linarith only [hu]

theorem recovery_final_arithmetic (m : ℕ) (hm : 450 ≤ m) (A T : ℝ)
    (hT : 1 < 9000*(m:ℝ)^4*T) (hA : A < 100000*(m:ℝ)^4*Real.sqrt ((m:ℝ)+2)*T) :
    let M : ℝ := m
    let C₁ := 9000/Real.sqrt M + 100000*Real.sqrt (1+2/M)
    let B := M^((9:ℝ)/2)*T
    9000/Real.sqrt 450 < 424.3 ∧ 100000*Real.sqrt (1+2/450) < 100222 ∧
    1+A < C₁*B ∧ C₁*B < 100650*B ∧ 100650*B < 110000*B := by
  dsimp only
  have hM : 450 ≤ (m:ℝ) := by exact_mod_cast hm
  have hpos : 0 < (m:ℝ) := by linarith
  have hT' : 0 < T := by
    by_contra! h
    linarith only [hT, mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 9000*(m:ℝ)^4 by positivity) h]
  have hs := Real.sqrt_pos.mpr hpos
  have h₁ : 9000/Real.sqrt 450 < 424.3 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 450), Real.sqrt_nonneg 450,
      sq_nonneg (Real.sqrt 450 - 9000/424.3)]
  have h₂ : 100000*Real.sqrt (1+2/450) < 100222 := by
    have h : Real.sqrt (1+2/450) < (100222/100000:ℝ) := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    linarith
  have hrat : 2/(m:ℝ) ≤ 2/450 := by gcongr
  have hcoef : 9000/Real.sqrt m+100000*Real.sqrt (1+2/(m:ℝ)) < 100650 := by
    calc
      _ ≤ 9000/Real.sqrt 450+100000*Real.sqrt (1+2/450) := by gcongr
      _ < _ := by linarith
  have hpow : (m:ℝ)^((9:ℝ)/2) = (m:ℝ)^4 * Real.sqrt m := by
    rw [show (9:ℝ)/2 = 4+1/2 by norm_num, Real.rpow_add hpos, ← Real.sqrt_eq_rpow, Real.rpow_ofNat]
  have hroot : Real.sqrt (1+2/(m:ℝ))*Real.sqrt m = Real.sqrt ((m:ℝ)+2) := by
    rw [← Real.sqrt_mul (by positivity), add_mul, one_mul, div_mul_cancel₀ _ hpos.ne']
  rw [hpow]
  refine ⟨h₁,h₂,?_,?_,?_⟩
  · have hsum := add_lt_add hT hA
    rw [← hroot] at hsum
    convert hsum using 1
    field_simp
  · calc
      _ = (9000/Real.sqrt m+100000*Real.sqrt (1+2/(m:ℝ)))*((m:ℝ)^4*Real.sqrt m*T) := by ring
      _ < _ := (mul_lt_mul_of_pos_right hcoef (by positivity)).trans_eq (by ring)
  · gcongr
    norm_num

private theorem D_lower (m : ℕ) (hm : 450 ≤ m) : 4090 ≤ D m := by
  have : 450 ≤ (m:ℝ) := by exact_mod_cast hm
  unfold D
  linarith

private def jet (p : Polynomial ℂ) (c : ℂ) (k : ℕ) :=
  (derivative^[k] p).eval c / p.eval c

/-- Differentiate the oscillator before taking quotients at c. -/
private theorem oscillator_jets (p : Polynomial ℂ) (c : ℂ) :
    let d := jet p c
    (EStar p).derivative.eval c / p.eval c = (1/2)*d 3-c*d 2-d 1 ∧
    (EStar (EStar p)).derivative.eval c / p.eval c =
      (1/4)*d 5-c*d 4+(c^2-2)*d 3+3*c*d 2+d 1 := by
  simp only [EStar, derivative_sub, derivative_add, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_X, one_mul, eval_sub, eval_mul, eval_add, eval_X, eval_C]
  constructor <;> dsimp [jet, Function.iterate_succ_apply] <;> ring

theorem recovery_operators (p : Polynomial ℂ) (c : ℂ) (m : ℕ) (hm : 450 ≤ m)
    (hc : ‖c‖ < 2.2) (hjet : jetBound p c m) :
    let v := D m
    let h₃ := v^3/2+2.2*v^2+v
    let h₅ := v^5/4+2.2*v^4+6.84*v^3+6.6*v^2+v
    ‖c^2-2‖ < 6.84 ∧ 2.2/v + 6.84/v^2 + 6.6/v^3 + 1/v^4 < 0.001 ∧
    ‖(EStar p).derivative.eval c / p.eval c‖ ≤ h₃ ∧ h₃ < 0.501*v^3 ∧
    ‖(EStar (EStar p)).derivative.eval c / p.eval c‖ ≤ h₅ ∧ h₅ < 0.251*v^5 := by
  let v := D m
  let d := jet p c
  have hv : 4090 ≤ v := D_lower m hm
  have hd (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 5) : ‖d k‖ ≤ v^k := hjet.2 k hk hk'
  have hc2 : ‖c^2-2‖ < 6.84 := by
    refine (norm_sub_le ..).trans_lt ?_
    rw [norm_pow, Complex.norm_ofNat]
    nlinarith only [(sq_lt_sq₀ (norm_nonneg c) (by norm_num : (0:ℝ) ≤ 2.2)).mpr hc]
  have hsmall : 2.2/v + 6.84/v^2 + 6.6/v^3 + 1/v^4 < 0.001 := by
    calc
      _ ≤ 2.2/4090 + 6.84/(4090:ℝ)^2 + 6.6/4090^3 + 1/4090^4 := by gcongr
      _ < _ := by norm_num
  obtain ⟨h₃,h₅⟩ := oscillator_jets p c
  obtain ⟨t,ht,htv⟩ := exists_nonneg_add_of_le hv
  refine ⟨hc2, hsmall, ?_, ?_, ?_, ?_⟩
  · rw [h₃]
    change ‖(1/2:ℂ)*d 3-c*d 2-d 1‖ ≤ v^3/2+2.2*v^2+v
    grw [norm_sub_le, norm_sub_le]
    simp only [norm_mul, norm_div, norm_one, Complex.norm_ofNat]
    calc
      _ ≤ (1/2)*v^3+2.2*v^2+v^1 := by gcongr <;> apply hd <;> decide
      _ = _ := by ring
  · change v^3/2+2.2*v^2+v < 0.501*v^3
    apply sub_pos.mp
    rw [← htv]
    ring_nf
    positivity
  · rw [h₅]
    change ‖(1/4:ℂ)*d 5-c*d 4+(c^2-2)*d 3+3*c*d 2+d 1‖ ≤
      v^5/4+2.2*v^4+6.84*v^3+6.6*v^2+v
    grw [norm_add_le, norm_add_le, norm_add_le, norm_sub_le]
    simp only [norm_mul, norm_div, norm_one, Complex.norm_ofNat]
    calc
      _ ≤ (1/4)*v^5+2.2*v^4+6.84*v^3+3*2.2*v^2+v^1 := by gcongr <;> apply hd <;> decide
      _ = _ := by ring
  · change v^5/4+2.2*v^4+6.84*v^3+6.6*v^2+v < 0.251*v^5
    apply sub_pos.mp
    rw [← htv]
    ring_nf
    positivity

private def normDen (j : ℕ) : ℂ := Real.sqrt (2^j*(j.factorial:ℝ))

private def mode (j : ℕ) : Polynomial ℂ := C (normDen j)⁻¹ * hermite j

private theorem mode_eval (j : ℕ) (z : ℂ) : (mode j).eval z = psi j z := by
  simp only [mode, eval_mul, eval_C, psi, normDen, div_eq_mul_inv]
  ring

private theorem mode_slope (j : ℕ) (z : ℂ) : (mode j).derivative.eval z = deriv (psi j) z := by
  have h : (fun w => (mode j).eval w) = psi j := funext (mode_eval j)
  exact (h ▸ ((mode j).hasDerivAt z) : HasDerivAt (psi j) _ z).deriv.symm

private theorem normalized_form (n m : ℕ) (a b : ℂ) :
    normalizedPoly n m a b = hermite 0 + hermite 1 + C a*mode n + C b*mode m := by
  simp only [normalizedPoly, family, mode, normDen, hermite, div_eq_mul_inv, map_mul]
  ring

theorem normalizedPoly_eval (n m : ℕ) (a b z : ℂ) :
    (normalizedPoly n m a b).eval z = normalizedFamily n m a b z := by
  rw [normalized_form]
  simp [hermite, eval_mul, eval_add, mode_eval, normalizedFamily]

private theorem osc_add (p q : Polynomial ℂ) : EStar (p+q) = EStar p + EStar q := by
  simp only [EStar, derivative_add]; ring

private theorem osc_C_mul (a : ℂ) (p : Polynomial ℂ) : EStar (C a*p) = C a*EStar p := by
  simp only [EStar, derivative_C_mul]; ring

private theorem remove_add (k : ℕ) (p q : Polynomial ℂ) :
    removeMode k (p+q) = removeMode k p + removeMode k q := by
  simp only [removeMode, osc_add]; ring

private theorem remove_C_mul (k : ℕ) (a : ℂ) (p : Polynomial ℂ) :
    removeMode k (C a*p) = C a*removeMode k p := by
  simp only [removeMode, osc_C_mul]; ring

private theorem remove_H (k j : ℕ) :
    removeMode k (hermite j) = C (1-(j:ℂ)/k)*hermite j := by
  apply Polynomial.funext
  intro z
  have he := congrArg (eval z) (hermite_equation j)
  simp only [eval_sub, eval_neg, nsmul_eq_mul, eval_mul, eval_ofNat, eval_natCast,
    eval_X, Nat.cast_mul, Nat.cast_ofNat] at he
  simp only [removeMode, EStar, eval_add, eval_mul, eval_C, eval_sub, eval_X]
  linear_combination ((k:ℂ)⁻¹ / 2)*he

private theorem remove_mode (k j : ℕ) :
    removeMode k (mode j) = C (1-(j:ℂ)/k)*mode j := by
  rw [mode, remove_C_mul, remove_H]; ring

private def gain (m j : ℕ) : ℝ := 1-(j:ℝ)/m

private theorem gain_cast (m j : ℕ) : (gain m j : ℂ) = 1-(j:ℂ)/m := by simp [gain]

private theorem filtered_form (n m : ℕ) (hm : 0 < m) (a b : ℂ) :
    removeMode m (normalizedPoly n m a b) = hermite 0 + C (gain m 1 : ℂ)*hermite 1 +
      C (a*(gain m n : ℂ))*mode n := by
  have hm0 : (m:ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [normalized_form]
  simp only [remove_add, remove_C_mul, remove_H, remove_mode, gain_cast, Nat.cast_zero,
    zero_div, sub_zero, map_one, one_mul, div_self hm0, sub_self, map_zero, zero_mul,
    mul_zero, add_zero, map_mul]
  ring

private theorem twice_filtered (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (a b : ℂ) :
    removeMode n (removeMode m (normalizedPoly n m a b)) =
      hermite 0 + C ((gain n 1 : ℂ)*gain m 1)*hermite 1 := by
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [filtered_form n m hm]
  simp only [remove_add, remove_C_mul, remove_H, remove_mode]
  simp only [gain_cast, Nat.cast_zero,
    zero_div, sub_zero, map_one, one_mul, div_self hn0, sub_self, map_zero, zero_mul,
    mul_zero, add_zero, map_mul]
  ring

private theorem remove_value (k : ℕ) (p : Polynomial ℂ) (c : ℂ) :
    (removeMode k p).eval c = p.eval c + (EStar p).eval c / (k:ℂ) := by
  simp [removeMode, eval_add, eval_mul]; ring

private theorem remove_slope (k : ℕ) (p : Polynomial ℂ) (c : ℂ) :
    (removeMode k p).derivative.eval c = p.derivative.eval c + (EStar p).derivative.eval c/(k:ℂ) := by
  simp [removeMode, eval_add, eval_mul]; ring

private theorem twice_slope (n m : ℕ) (p : Polynomial ℂ) (c : ℂ) :
    (removeMode n (removeMode m p)).derivative.eval c =
      p.derivative.eval c + (1/(n:ℂ)+1/(m:ℂ))*(EStar p).derivative.eval c +
        (1/((n:ℂ)*m))*(EStar (EStar p)).derivative.eval c := by
  simp only [removeMode, osc_add, osc_C_mul, derivative_add, derivative_C_mul, eval_add, eval_mul, eval_C]
  ring

theorem recovery_one_filter (p : Polynomial ℂ) (c : ℂ) (m : ℕ) (hm : 450 ≤ m)
    (hc : ‖c‖ < 2.2) (hjet : jetBound p c m) :
    let M : ℝ := m
    let v := D m
    let B := 1+(v^2/2+2.2*v)/M
    let C₁ := v+0.501*v^3/M
    ‖(removeMode m p).eval c / p.eval c‖ ≤ B ∧ B = (100/11)^2*M/2+21 ∧
    B < 41.33*M+21 ∧ 41.33*M+21 < 43*M ∧
    ‖(removeMode m p).derivative.eval c / p.eval c‖ ≤ C₁ ∧
    C₁ < 376.41*M^2+9.1*M ∧ 376.41*M^2+9.1*M < 390*M^2 := by
  let M : ℝ := m
  let v := D m
  let d := jet p c
  have hM : 450 ≤ M := by dsimp [M]; exact_mod_cast hm
  have hpos : 0 < M := by linarith
  have hd₁ : ‖d 1‖ ≤ v := by simpa only [jet, d, v, pow_one] using hjet.2 1 (by decide) (by decide)
  have hd₂ : ‖d 2‖ ≤ v^2 := hjet.2 2 (by decide) (by decide)
  obtain ⟨_,_,h₃,h₃',_,_⟩ := recovery_operators p c m hm hc hjet
  have hEq : (EStar p).eval c / p.eval c = d 2/2 - c*d 1 := by
    simp [EStar, d, jet, eval_sub, eval_mul]; ring
  have hE : ‖(EStar p).eval c / p.eval c‖ ≤ v^2/2+2.2*v := by
    rw [hEq]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_div, norm_mul, Complex.norm_ofNat]
    gcongr
  have hval : (removeMode m p).eval c / p.eval c =
      1 + ((EStar p).eval c / p.eval c) / (m:ℂ) := by
    rw [remove_value, add_div, div_self hjet.1]; ring
  have hslope : (removeMode m p).derivative.eval c / p.eval c =
      d 1 + ((EStar p).derivative.eval c / p.eval c) / (m:ℂ) := by
    rw [remove_slope, add_div]; change _ = p.derivative.eval c / p.eval c + _; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hval]
    refine (norm_add_le ..).trans ?_
    rw [norm_one, norm_div, Complex.norm_natCast]
    gcongr
  · dsimp [D]
    field_simp
    ring
  · change 1+(v^2/2+2.2*v)/M < 41.33*M+21
    change 1+((100*M/11)^2/2+2.2*(100*M/11))/M < _
    field_simp
    nlinarith only [hpos, sq_pos_of_pos hpos]
  · change 41.33*M+21 < 43*M
    linarith
  · rw [hslope]
    refine (norm_add_le ..).trans ?_
    rw [norm_div, Complex.norm_natCast]
    exact add_le_add hd₁ (div_le_div_of_nonneg_right (h₃.trans h₃'.le) hpos.le)
  · change 100*M/11+0.501*(100*M/11)^3/M < 376.41*M^2+9.1*M
    field_simp
    nlinarith only [pow_pos hpos 3, sq_pos_of_pos hpos]
  · change 376.41*M^2+9.1*M < 390*M^2
    nlinarith only [mul_le_mul_of_nonneg_right hM hpos.le, hpos]

theorem reciprocal_recovery (n m : ℕ) (hn : 2 ≤ n) (hm : 450 ≤ m) (hh : 2*n ≤ m)
    (a b c : ℂ) (hc : ‖c‖ < 2.2) (hjet : jetBound (normalizedPoly n m a b) c m) :
    let v := D m
    let T := ‖normalizedFamily n m a b c‖
    (1-1/(m:ℝ))/T ≤ v+(1/2+1/(m:ℝ))*0.501*v^3+0.251*v^5/(2*(m:ℝ)) ∧
    1/T < 7811*(m:ℝ)^4 ∧ 1 < 9000*(m:ℝ)^4*T := by
  let p := normalizedPoly n m a b
  let N : ℝ := n
  let M : ℝ := m
  let T := ‖p.eval c‖
  let v := D m
  let e := (EStar p).derivative.eval c / p.eval c
  let e₂ := (EStar (EStar p)).derivative.eval c / p.eval c
  have hM : 450 ≤ M := by dsimp [M]; exact_mod_cast hm
  have hN : 2 ≤ N := by dsimp [N]; exact_mod_cast hn
  have hMpos : 0 < M := by linarith
  have hNpos : 0 < N := by linarith
  have hT : 0 < T := norm_pos_iff.mpr hjet.1
  have hTval : ‖normalizedFamily n m a b c‖ = T := congrArg norm (normalizedPoly_eval ..).symm
  have hiN : 1/N ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hN
  have hiM : 1/M ≤ 1/450 := one_div_le_one_div_of_le (by norm_num) hM
  have hg : 0 < 1-1/M := by linarith
  obtain ⟨_,_,h₃,h₃',h₅,h₅'⟩ := recovery_operators p c m hm hc hjet
  have he : ‖e‖ ≤ 0.501*v^3 := h₃.trans h₃'.le
  have he₂ : ‖e₂‖ ≤ 0.251*v^5 := h₅.trans h₅'.le
  have hd : ‖jet p c 1‖ ≤ v := by simpa only [jet, p, v, pow_one] using hjet.2 1 (by decide) (by decide)
  have hid : ((2*(1-1/N)*(1-1/M) : ℝ):ℂ)/p.eval c =
      jet p c 1 + ((1/N+1/M : ℝ):ℂ)*e + ((1/(N*M) : ℝ):ℂ)*e₂ := by
    have h := twice_slope n m p c
    rw [show removeMode n (removeMode m p) = _ from
      twice_filtered n m (by omega) (lt_of_lt_of_le (by omega : 0 < 2*n) hh) a b] at h
    simp [hermite, derivative_mul, eval_mul, gain_cast] at h
    dsimp [N,M,e,e₂,jet]
    push_cast
    linear_combination h / p.eval c
  have hsum : (1-1/M)/T ≤ v+(1/2+1/M)*0.501*v^3+0.251*v^5/(2*M) := by
    have hgain : 1-1/M ≤ 2*(1-1/N)*(1-1/M) := by
      exact le_mul_of_one_le_left hg.le (by linarith only [hiN])
    calc
      _ ≤ (2*(1-1/N)*(1-1/M))/T := div_le_div_of_nonneg_right hgain hT.le
      _ = ‖((2*(1-1/N)*(1-1/M) : ℝ):ℂ)/p.eval c‖ := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg.le.trans hgain)]
      _ ≤ ‖jet p c 1‖ + (1/N+1/M)*‖e‖ + (1/(N*M))*‖e₂‖ := by
        rw [hid]
        grw [norm_add_le, norm_add_le]
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1/N+1/M),
          abs_of_nonneg (by positivity : 0 ≤ 1/(N*M)), le_refl]
      _ ≤ v + (1/2+1/M)*(0.501*v^3)+(1/(2*M))*(0.251*v^5) := by
        gcongr
      _ = _ := by ring
  obtain ⟨h₀,h₁,h₁',h₂,h₂',_,hfactor⟩ := reciprocal_arithmetic m hm
  have hbud : v+(1/2+1/M)*0.501*v^3+0.251*v^5/(2*M) < 7793.031*M^4 := by
    have hsum' : reciprocalTerms m 0 + reciprocalTerms m 1 + reciprocalTerms m 2 < 7793.031 := by
      linarith only [h₀,h₁.trans h₁',h₂,h₂']
    have h := mul_lt_mul_of_pos_right hsum' (pow_pos hMpos 4)
    convert h using 1
    change _ = (v/M^4 + ((1/2+1/M)*0.501*v^3)/M^4 + (0.251*v^5/(2*M))/M^4)*M^4
    field_simp
  have hrecip : 1/T < 7811*M^4 := by
    calc
      _ = (1/(1-1/M))*((1-1/M)/T) := by field_simp [show M-1 ≠ 0 by linarith]
      _ < (1/(1-1/M))*(7793.031*M^4) :=
        mul_lt_mul_of_pos_left (hsum.trans_lt hbud) (one_div_pos.mpr hg)
      _ ≤ 1.0023*(7793.031*M^4) := mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ < _ := by nlinarith only [pow_pos hMpos 4]
  dsimp only
  rw [hTval]
  exact ⟨hsum, hrecip, (div_lt_iff₀ hT).mp (hrecip.trans (by nlinarith only [pow_pos hMpos 4]))⟩

theorem recovery_subtraction (n m : ℕ) (hn : 2 ≤ n) (hm : 450 ≤ m) (hh : 2*n ≤ m)
    (a b c : ℂ) (hc : ‖c‖ < 2.2) (hjet : jetBound (normalizedPoly n m a b) c m) :
    let M : ℝ := m
    let T := ‖normalizedFamily n m a b c‖
    let u := ‖a‖*‖psi n c‖
    let v := ‖a‖*‖deriv (psi n) c‖
    let g := 1-(n:ℝ)/M
    let k := Real.sqrt (2*(n:ℝ))
    1/2 ≤ g ∧ 2 ≤ k ∧ u*g < 43*M*T+5.4 ∧ 43*M*T+5.4 < (43*M+48600*M^4)*T ∧
    v*g < 390*M^2*T+2 ∧ 390*M^2*T+2 < (390*M^2+18000*M^4)*T ∧
    u < (86*M+97200*M^4)*T ∧ (86*M+97200*M^4)*T < 100000*M^4*T ∧
    v/k < (390*M^2+18000*M^4)*T ∧ (390*M^2+18000*M^4)*T < 100000*M^4*T := by
  let M : ℝ := m
  let p := normalizedPoly n m a b
  let q := removeMode m p
  let T := ‖p.eval c‖
  let u := ‖a‖*‖psi n c‖
  let v := ‖a‖*‖deriv (psi n) c‖
  let g := gain m n
  let γ := gain m 1
  let k := Real.sqrt (2*(n:ℝ))
  have hM : 450 ≤ M := by dsimp [M]; exact_mod_cast hm
  have hMpos : 0 < M := by linarith
  have hN : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hh' : 2*(n:ℝ) ≤ M := by dsimp [M]; exact_mod_cast hh
  have hT : 0 < T := norm_pos_iff.mpr hjet.1
  have hg : 1/2 ≤ g := by
    have : (n:ℝ)/M ≤ 1/2 := (div_le_iff₀ hMpos).mpr (by linarith)
    change 1/2 ≤ 1-(n:ℝ)/M
    linarith
  have hk : 2 ≤ k := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by linarith)
  have hγ : 0 ≤ γ ∧ γ ≤ 1 := by
    simp only [γ, gain, Nat.cast_one]
    change 0 ≤ 1-1/M ∧ 1-1/M ≤ 1
    have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 450) hM
    constructor <;> linarith [one_div_pos.mpr hMpos]
  have hTval : ‖normalizedFamily n m a b c‖ = T := congrArg norm (normalizedPoly_eval ..).symm
  obtain ⟨_,_,hsize⟩ := reciprocal_recovery n m hn hm hh a b c hc hjet
  rw [hTval] at hsize
  change 1 < 9000*M^4*T at hsize
  obtain ⟨h₀,_,h₀',h₀'',h₁,h₁',h₁''⟩ := recovery_one_filter p c m hm hc hjet
  have hq : ‖q.eval c‖ < 43*M*T :=
    (div_lt_iff₀ hT).mp (by simpa only [norm_div] using (h₀.trans_lt (h₀'.trans h₀'')))
  have hq' : ‖q.derivative.eval c‖ < 390*M^2*T :=
    (div_lt_iff₀ hT).mp (by simpa only [norm_div] using (h₁.trans_lt (h₁'.trans h₁'')))
  have hform := filtered_form n m (by omega) a b
  change q = hermite 0 + C (γ:ℂ)*hermite 1 + C (a*(g:ℂ))*mode n at hform
  have huval : a*(g:ℂ)*psi n c = q.eval c - (1+2*(γ:ℂ)*c) := by
    rw [hform]
    simp [hermite, eval_mul, eval_add, mode_eval]
    ring
  have hvval : a*(g:ℂ)*deriv (psi n) c = q.derivative.eval c - 2*(γ:ℂ) := by
    rw [hform]
    simp only [hermite, derivative_add, derivative_C, derivative_mul, derivative_one,
      derivative_X, derivative_ofNat, zero_mul, zero_add, mul_one, eval_add,
      eval_mul, eval_ofNat, eval_C, mode_slope]
    ring
  have huNorm : u*g = ‖a*(g:ℂ)*psi n c‖ := by
    simp only [u, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ g)]
    ring
  have hvNorm : v*g = ‖a*(g:ℂ)*deriv (psi n) c‖ := by
    simp only [v, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ g)]
    ring
  have haff : ‖1+2*(γ:ℂ)*c‖ ≤ 1+2*‖c‖ := by
    refine (norm_add_le ..).trans ?_
    simp only [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hγ.1, Complex.norm_ofNat]
    nlinarith only [mul_le_mul_of_nonneg_right hγ.2 (norm_nonneg c)]
  have hu : u*g < 43*M*T + 5.4 := by
    rw [huNorm, huval]
    exact (norm_sub_le ..).trans_lt (add_lt_add hq (haff.trans_lt (by linarith)))
  have hv : v*g < 390*M^2*T + 2 := by
    rw [hvNorm, hvval]
    refine (norm_sub_le ..).trans_lt (add_lt_add_of_lt_of_le hq' ?_)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hγ.1, Complex.norm_ofNat]
    linarith only [hγ.2]
  have hu' : 43*M*T+5.4 < (43*M+48600*M^4)*T := by linarith only [hsize]
  have hv' : 390*M^2*T+2 < (390*M^2+18000*M^4)*T := by linarith only [hsize]
  have hscaledU : u < (86*M+97200*M^4)*T := by
    nlinarith only [hu.trans hu', mul_le_mul_of_nonneg_left hg (show 0 ≤ u by dsimp [u]; positivity)]
  have hscaledV : v/k < (390*M^2+18000*M^4)*T := by
    apply (div_lt_iff₀ (by linarith : 0 < k)).mpr
    nlinarith only [hv.trans hv', mul_le_mul_of_nonneg_left hg (show 0 ≤ v by dsimp [v]; positivity),
      mul_le_mul_of_nonneg_right hk (show 0 ≤ (390*M^2+18000*M^4)*T by positivity)]
  dsimp only
  rw [hTval]
  refine ⟨hg, hk, hu, hu', hv, hv', hscaledU, ?_, hscaledV, ?_⟩
  all_goals
    apply mul_lt_mul_of_pos_right _ hT
    obtain ⟨t, ht, he⟩ := exists_nonneg_add_of_le hM
    change 450+t = (m:ℝ) at he
    apply sub_pos.mp
    rw [← he]
    ring_nf
    positivity

theorem jetBound_of_emptyStrip (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m) (a b c : ℂ)
    (hf : emptyStrip (normalizedFamily n m a b) (87/100)) (hy : |c.im| < 76/100) :
    jetBound (normalizedPoly n m a b) c m := by
  let p := normalizedPoly n m a b
  have hpc : p.eval c ≠ 0 := by
    change (normalizedPoly n m a b).eval c ≠ 0
    rw [normalizedPoly_eval]
    exact hf c (by linarith)
  refine ⟨hpc, fun k _ _ => ?_⟩
  have hdegree : p.natDegree ≤ m := by
    unfold p normalizedPoly
    rw [family_degree n m hn hnm]
    split_ifs <;> omega
  have hsep (w : ℂ) (hw : w ∈ p.roots) : 1 ≤ (100/11)*‖c-w‖ := by
    have hzero := isRoot_of_mem_roots hw
    change (normalizedPoly n m a b).eval w = 0 at hzero
    rw [normalizedPoly_eval] at hzero
    have hout : 87/100 ≤ |w.im| := le_of_not_gt fun hin => hf w hin hzero
    have him := Complex.abs_im_le_norm (c-w)
    rw [Complex.sub_im, abs_sub_comm] at him
    linarith [abs_sub_abs_le_abs_sub w.im c.im]
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hpc)]
  simpa only [D, mul_div_assoc, mul_comm (100:ℝ) m] using
    polynomial_derivatives_of_root_distance p c m k (100/11) (by norm_num) hdegree hsep

theorem recovery_weighted_max (n m : ℕ) (hn : 2 ≤ n) (hh : 2*n ≤ m) (c : ℂ) :
    1/Real.sqrt ((m:ℝ)+2) ≤ 1/Real.sqrt (2*(n:ℝ)+2) ∧
    1/Real.sqrt (2*(n:ℝ)+2) ≤ max ‖psi n c‖ (‖deriv (psi n) c‖/Real.sqrt (2*(n:ℝ))) := by
  exact LowerTailSteps.complex_mode_floor n m (by omega) hh c

theorem recovery_weighted_coefficient (n m : ℕ) (hn : 2 ≤ n) (hm : 450 ≤ m) (hh : 2*n ≤ m)
    (a b c : ℂ) (hc : ‖c‖ < 2.2) (hjet : jetBound (normalizedPoly n m a b) c m) :
    ‖a‖ < 100000*(m:ℝ)^4*Real.sqrt ((m:ℝ)+2)*‖normalizedFamily n m a b c‖ := by
  let M : ℝ := m
  let T := ‖normalizedFamily n m a b c‖
  let B := 100000*M^4*T
  let u := ‖psi n c‖
  let v := ‖deriv (psi n) c‖/Real.sqrt (2*(n:ℝ))
  obtain ⟨_,_,_,_,_,_,hu,hu',hv,hv'⟩ := recovery_subtraction n m hn hm hh a b c hc hjet
  have hau : ‖a‖*u < B := hu.trans hu'
  have hav : ‖a‖*v < B := by
    change ‖a‖*(‖deriv (psi n) c‖/_) < _
    rw [← mul_div_assoc]
    exact hv.trans hv'
  have hmax : ‖a‖*max u v < B := by
    rw [mul_max_of_nonneg _ _ (norm_nonneg a)]
    exact max_lt hau hav
  have hfloor := (recovery_weighted_max n m hn hh c).1.trans (recovery_weighted_max n m hn hh c).2
  have hlow : ‖a‖/Real.sqrt (M+2) < B := by
    rw [div_eq_mul_one_div]
    exact (mul_le_mul_of_nonneg_left hfloor (norm_nonneg a)).trans_lt hmax
  have hres := (div_lt_iff₀ (by dsimp [M]; positivity : 0 < Real.sqrt (M+2))).mp hlow
  change ‖a‖ < 100000*M^4*Real.sqrt (M+2)*T
  exact hres.trans_eq (by dsimp [B]; ring)

end Turan.RecoveryDetails
