module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TailDefs
public import Turan.SlotDefs

@[expose] public section

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
    ‖c‖ < Real.sqrt (4+0.76^2) ∧ Real.sqrt (4+0.76^2) < 2.14 ∧ 4090 ≤ D m := by sorry

theorem recovery_operators (p : Polynomial ℂ) (c : ℂ) (m : ℕ) (hm : 450 ≤ m)
    (hc : ‖c‖ < 2.2) (hjet : jetBound p c m) :
    let v := D m
    let h₃ := v^3/2+2.2*v^2+v
    let h₅ := v^5/4+2.2*v^4+6.84*v^3+6.6*v^2+v
    ‖c^2-2‖ < 6.84 ∧ 2.2/v + 6.84/v^2 + 6.6/v^3 + 1/v^4 < 0.001 ∧
    ‖(EStar p).derivative.eval c / p.eval c‖ ≤ h₃ ∧ h₃ < 0.501*v^3 ∧
    ‖(EStar (EStar p)).derivative.eval c / p.eval c‖ ≤ h₅ ∧ h₅ < 0.251*v^5 := by sorry

def reciprocalTerms (m : ℕ) : Fin 3 → ℝ :=
  ![D m / (m:ℝ)^4, (1/2+1/(m:ℝ))*0.501*(D m)^3/(m:ℝ)^4,
    0.251*(D m)^5/(2*(m:ℝ))/(m:ℝ)^4]

theorem reciprocal_arithmetic (m : ℕ) (hm : 450 ≤ m) :
    reciprocalTerms m 0 < 1/1000000 ∧
    reciprocalTerms m 1 < 0.50223*0.501*(100/11)^3/(m:ℝ) ∧
    0.50223*0.501*(100/11)^3/(m:ℝ) < 0.43 ∧
    reciprocalTerms m 2 = 0.251*(100/11)^5/2 ∧ (0.251:ℝ)*(100/11)^5/2 < 7792.6 ∧
    (∀ k : Fin 3, AntitoneOn (fun t => reciprocalTerms t k) (Set.Ici 450)) ∧
    1/(1-1/(m:ℝ)) ≤ 1.0023 := by sorry

theorem reciprocal_recovery (n m : ℕ) (hn : 2 ≤ n) (hm : 450 ≤ m) (hh : 2*n ≤ m)
    (a b c : ℂ) (hc : ‖c‖ < 2.2) (hjet : jetBound (normalizedPoly n m a b) c m) :
    let v := D m
    let T := ‖normalizedFamily n m a b c‖
    (1-1/(m:ℝ))/T ≤ v+(1/2+1/(m:ℝ))*0.501*v^3+0.251*v^5/(2*(m:ℝ)) ∧
    1/T < 7811*(m:ℝ)^4 ∧ 1 < 9000*(m:ℝ)^4*T := by sorry

theorem recovery_one_filter (p : Polynomial ℂ) (c : ℂ) (m : ℕ) (hm : 450 ≤ m)
    (hc : ‖c‖ < 2.2) (hjet : jetBound p c m) :
    let M : ℝ := m
    let v := D m
    let B := 1+(v^2/2+2.2*v)/M
    let C₁ := v+0.501*v^3/M
    ‖(removeMode m p).eval c / p.eval c‖ ≤ B ∧ B = (100/11)^2*M/2+21 ∧
    B < 41.33*M+21 ∧ 41.33*M+21 < 43*M ∧
    ‖(removeMode m p).derivative.eval c / p.eval c‖ ≤ C₁ ∧
    C₁ < 376.41*M^2+9.1*M ∧ 376.41*M^2+9.1*M < 390*M^2 := by sorry

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
    v/k < (390*M^2+18000*M^4)*T ∧ (390*M^2+18000*M^4)*T < 100000*M^4*T := by sorry

theorem recovery_weighted_max (n m : ℕ) (hn : 2 ≤ n) (hh : 2*n ≤ m) (c : ℂ) :
    1/Real.sqrt ((m:ℝ)+2) ≤ 1/Real.sqrt (2*(n:ℝ)+2) ∧
    1/Real.sqrt (2*(n:ℝ)+2) ≤ max ‖psi n c‖ (‖deriv (psi n) c‖/Real.sqrt (2*(n:ℝ))) := by sorry

theorem recovery_weighted_coefficient (n m : ℕ) (hn : 2 ≤ n) (hm : 450 ≤ m) (hh : 2*n ≤ m)
    (a b c : ℂ) (hc : ‖c‖ < 2.2) (hjet : jetBound (normalizedPoly n m a b) c m) :
    ‖a‖ < 100000*(m:ℝ)^4*Real.sqrt ((m:ℝ)+2)*‖normalizedFamily n m a b c‖ := by sorry

theorem recovery_final_arithmetic (m : ℕ) (hm : 450 ≤ m) (A T : ℝ)
    (hT : 1 < 9000*(m:ℝ)^4*T) (hA : A < 100000*(m:ℝ)^4*Real.sqrt ((m:ℝ)+2)*T) :
    let M : ℝ := m
    let C₁ := 9000/Real.sqrt M + 100000*Real.sqrt (1+2/M)
    let B := M^((9:ℝ)/2)*T
    9000/Real.sqrt 450 < 424.3 ∧ 100000*Real.sqrt (1+2/450) < 100222 ∧
    1+A < C₁*B ∧ C₁*B < 100650*B ∧ 100650*B < 110000*B := by sorry

end Turan.RecoveryDetails
