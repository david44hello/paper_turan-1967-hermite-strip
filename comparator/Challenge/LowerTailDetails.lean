module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TailDefs
public import Challenge.LowerRadialDefs
public import Challenge.LowerEnergyDef
public import Challenge.LowerScalarDefs
public import Turan.Oscillator

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

noncomputable section
open Filter Metric Set
open scoped ComplexConjugate
namespace Turan.LowerTailSteps

/-! Lower-index circle constants, Section 4. -/

def farInterval (m : ℕ) : Set ℝ :=
  Icc (Real.sqrt (9 * (m : ℝ) / 5))
    (Real.sqrt (9 * (m : ℝ) / 5) + 3 * Real.pi / Real.sqrt m)

theorem far_potential (m : ℕ) (hm : 450 ≤ m) (t : ℝ) (ht : t ∈ farInterval m) :
    (14 / 100 : ℝ) * m < 2 * (m : ℝ) + 1 - t ^ 2 := by sorry

theorem far_zero_slope (m : ℕ) (hm : 450 ≤ m) (x : ℝ) (hx : x ∈ farInterval m)
    (hz : psi m (x : ℂ) = 0) :
    (26 / 100 : ℝ) < ‖deriv (phi m) (x : ℂ)‖ := by sorry

theorem far_affine (m : ℕ) (hm : 450 ≤ m) (x : ℝ) (hx : x ∈ farInterval m)
    (z : ℂ) (hz : ‖z - (x : ℂ)‖ = 1 / Real.sqrt m) :
    ‖1 + 2*z‖ < (278 / 100 : ℝ) * Real.sqrt m := by sorry

theorem far_affine_ratio (m : ℕ) (hm : 450 ≤ m) (x : ℝ) (hx : x ∈ farInterval m)
    (z : ℂ) (hz : ‖z - (x : ℂ)‖ = 1 / Real.sqrt m)
    (hφ : 1 / (5 * Real.sqrt m) < ‖phi m z‖) :
    ‖1 + 2*z‖ < 55 * (m : ℝ) * Real.exp (-(9/10 : ℝ) * m) * ‖psi m z‖ := by sorry

theorem logTail_decreases : logTail 450 < -12 ∧ StrictAntiOn logTail (Ici 450) := by sorry

theorem logTail_rate :
    (∀ M ∈ Ici (450 : ℝ), HasDerivAt logTail
      (5/M + (76/100 : ℝ) / Real.sqrt (2*M) - 197/1000) M) ∧
    StrictAntiOn (deriv logTail) (Ici 450) ∧
    -(1606/10000 : ℝ) < deriv logTail 450 ∧ deriv logTail 450 < -(1605/10000 : ℝ) := by sorry

/-! Energy and vertical propagation. The vector uses the Euclidean norm on ℂ². -/

def modeVector (m : ℕ) (z : ℂ) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![psi m z, deriv (psi m) z / (Real.sqrt (2*(m:ℝ)) : ℂ)]

def verticalMatrix (m : ℕ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let s : ℂ := Real.sqrt (2*(m:ℝ))
  !![0, s; -s, 2*z]

theorem even_center (k : ℕ) :
    (psi (2*k) 0)^2 = (((((2*k).choose k : ℕ) : ℝ) / 4^k : ℝ) : ℂ) ∧
    1 / (2*(k:ℝ)+1) ≤ ‖psi (2*k) 0‖^2 := by sorry

attribute [-instance] CommCStarAlgebra.toNormedCommRing in
theorem realEnergy_derivative_min (m : ℕ) (hm : 1 ≤ m) :
    (∀ t : ℝ, HasDerivAt (realEnergy m)
      (2*t*‖deriv (psi m) (t : ℂ)‖^2 / (m : ℝ)) t) ∧
    1 / ((m : ℝ) + 1) ≤ realEnergy m 0 ∧
    (∀ t : ℝ, realEnergy m 0 ≤ realEnergy m t) := by sorry

theorem realEnergy_comparison (m : ℕ) (hm : 1 ≤ m) :
    (∀ t : ℝ, 0 ≤ t → deriv (realEnergy m) t ≤ 4*t*realEnergy m t) ∧
    Function.Even (realEnergy m) ∧
    (∀ t : ℝ, realEnergy m t ≤ realEnergy m 0 * Real.exp (2*t^2)) := by sorry

theorem realEnergy_origin_even (k : ℕ) (hk : 1 ≤ k) :
    realEnergy (2*k) 0 = (((2*k).choose k : ℕ) : ℝ) / 4^k ∧ realEnergy (2*k) 0 ≤ 1 := by sorry

theorem realEnergy_origin_odd (k : ℕ) :
    realEnergy (2*k+1) 0 = ‖psi (2*k) 0‖^2 ∧ realEnergy (2*k+1) 0 ≤ 1 := by sorry

attribute [-instance] CommCStarAlgebra.toNormedCommRing in
theorem complex_mode_floor (n m : ℕ) (hn : 1 ≤ n) (hh : 2*n ≤ m) (c : ℂ) :
    1 / Real.sqrt ((m:ℝ)+2) ≤ 1 / Real.sqrt (2*(n:ℝ)+2) ∧
    1 / Real.sqrt (2*(n:ℝ)+2) ≤
      max ‖psi n c‖ (‖deriv (psi n) c‖ / Real.sqrt (2*(n:ℝ))) := by sorry

theorem real_segment (m : ℕ) (hm : 1 ≤ m) (X : ℝ) (hX : |X| ≤ 2) :
    realEnergy m X ≤ Real.exp (2*X^2) ∧ Real.exp (2*X^2) ≤ Real.exp 8 ∧
    ‖modeVector m (X : ℂ)‖ = Real.sqrt (realEnergy m X) ∧
    ‖modeVector m (X : ℂ)‖ ≤ Real.exp 4 := by sorry

theorem vertical_operator (m : ℕ) (hm : 1 ≤ m) (z : ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (verticalMatrix m z)‖ ≤ Real.sqrt (2*(m:ℝ)) + 2*‖z‖ := by sorry

theorem vertical_segment (m : ℕ) (hm : 1 ≤ m) (c : ℂ)
    (hX : |c.re| ≤ 2) (hY : |c.im| < 76/100) :
    (∀ s ∈ Icc (0 : ℝ) 1, ‖(c.re : ℂ) + (s*c.im : ℝ)*Complex.I‖ < 214/100) ∧
    ‖modeVector m c‖ ≤ ‖modeVector m (c.re : ℂ)‖ *
      Real.exp ((Real.sqrt (2*(m:ℝ)) + 428/100) * |c.im|) := by sorry

theorem lower_vertical_chain (m : ℕ) (hm : 1 ≤ m) (c : ℂ)
    (hX : |c.re| ≤ 2) (hY : |c.im| < 76/100) :
    realEnergy m c.re ≤ Real.exp (2*c.re^2) ∧
    ‖psi m c‖ ≤ ‖modeVector m c‖ ∧
    ‖modeVector m c‖ ≤ Real.exp 4 * Real.exp ((76/100)*Real.sqrt (2*(m:ℝ))+326/100) ∧
    Real.exp 4 * Real.exp ((76/100)*Real.sqrt (2*(m:ℝ))+326/100) <
      Real.exp (8+(76/100)*Real.sqrt (2*(m:ℝ))) := by sorry

theorem polar_log_concavity (x r s : ℝ) (hr : 0 < r) :
    ConcaveOn ℝ {t : ℝ | t ∈ Icc (-1 : ℝ) 1 ∧ 0 < factorDistanceSq x r s t}
      (fun t => Real.log (factorDistanceSq x r s t)/2) ∧
    ConcaveOn ℝ (Icc (-1 : ℝ) 1) (gaussianLog x r) := by sorry

theorem polar_log_values (x r s θ : ℝ) (hr : 0 < r) :
    let z := (x : ℂ) + r * Complex.exp ((θ : ℂ)*Complex.I)
    (z ≠ (s : ℂ) → Real.log ‖z-(s : ℂ)‖ = Real.log (factorDistanceSq x r s (Real.cos θ))/2) ∧
    Real.log ‖Complex.exp (-z^2/2)‖ = gaussianLog x r (Real.cos θ) := by sorry

theorem mehler_diagonal_term (n : ℕ) (z : ℂ) :
    let term := fun k : ℕ => (1/5 : ℝ)^k * ‖psi k z‖^2
    let K := (Real.sqrt (1 - 1/25 : ℝ))⁻¹ * Real.exp (z.re^2/3 + z.im^2/2)
    (∀ k : ℕ, ((1/5 : ℂ)^k * psi k z * psi k (conj z)) = (term k : ℂ)) ∧
    HasSum term K ∧ term n ≤ ∑' k, term k ∧ term n ≤ K := by sorry

/-! The signed Volterra operator and the two factorial series, Appendix A.1. -/

def volterraOp (j : ℕ) (ξ ρ : ℝ) (f : ℂ → ℂ) (v : ℂ) : ℂ :=
  -v^2 * ∫ t : ℝ in 0..1,
    ((1-t : ℝ) : ℂ) * radialPotential j ξ ρ ((t : ℂ)*v) * f ((t : ℂ)*v)

def radialAffine (j : ℕ) (ξ ρ : ℝ) (v : ℂ) : ℂ :=
  radialMode j ξ ρ 0 + radialSlope j ξ ρ * v

def volterraTerm (j : ℕ) (ξ ρ : ℝ) (k : ℕ) : ℂ → ℂ :=
  (volterraOp j ξ ρ)^[k] (radialAffine j ξ ρ)

theorem radial_integral_equation (j : ℕ) (ξ ρ : ℝ) (hρ : 0 < ρ) (v : ℂ) (hv : ‖v‖ ≤ 1) :
    ‖radialPotential j ξ ρ v‖ ≤ circleQ j ξ ρ ∧
    radialMode j ξ ρ v = radialAffine j ξ ρ v + volterraOp j ξ ρ (radialMode j ξ ρ) v := by sorry

theorem factorial_integral (ℓ : ℕ) :
    (∫ t : ℝ in 0..1, (1-t)*t^ℓ / (ℓ.factorial : ℝ)) = 1/((ℓ+2).factorial : ℝ) := by sorry

theorem volterra_factorial_bounds (j : ℕ) (ξ ρ : ℝ) (hρ : 0 < ρ)
    (k : ℕ) (v : ℂ) (hv : ‖v‖ ≤ 1) :
    let T := volterraOp j ξ ρ
    let A := radialMode j ξ ρ 0
    let δ := radialSlope j ξ ρ
    let Q := circleQ j ξ ρ
    let evenBound := Q^k * ‖A‖ * ‖v‖^(2*k) / ((2*k).factorial : ℝ)
    let oddBound := Q^k * ‖δ‖ * ‖v‖^(2*k+1) / ((2*k+1).factorial : ℝ)
    ‖(T^[k] (fun _ => A)) v‖ ≤ evenBound ∧
    ‖(T^[k] (fun w => δ*w)) v‖ ≤ oddBound ∧
    ‖volterraTerm j ξ ρ k v‖ ≤ evenBound + oddBound := by sorry

attribute [-instance] CommCStarAlgebra.toNormedCommRing in
theorem volterra_series_solves (j : ℕ) (ξ ρ : ℝ) (hρ : 0 < ρ) :
    let term := volterraTerm j ξ ρ
    let F := fun v => ∑' k, term k v
    TendstoUniformlyOn (fun N v => ∑ k ∈ Finset.range N, term k v) F atTop (closedBall 0 1) ∧
    ContinuousOn F (closedBall 0 1) ∧
    ∀ v ∈ closedBall (0:ℂ) 1, F v = radialAffine j ξ ρ v + volterraOp j ξ ρ F v := by sorry

attribute [-instance] CommCStarAlgebra.toNormedCommRing in
theorem volterra_unique (j : ℕ) (ξ ρ : ℝ) (hρ : 0 < ρ) (f g : ℂ → ℂ)
    (hf : ContinuousOn f (closedBall 0 1)) (hg : ContinuousOn g (closedBall 0 1))
    (hef : ∀ v ∈ closedBall (0:ℂ) 1, f v = radialAffine j ξ ρ v + volterraOp j ξ ρ f v)
    (heg : ∀ v ∈ closedBall (0:ℂ) 1, g v = radialAffine j ξ ρ v + volterraOp j ξ ρ g v) :
    let M := sSup ((fun w => ‖f w-g w‖) '' closedBall (0:ℂ) 1)
    (∀ k : ℕ, ∀ v ∈ closedBall (0:ℂ) 1,
      ‖f v-g v‖ ≤ M * (circleQ j ξ ρ)^k / ((2*k).factorial : ℝ)) ∧
    EqOn f g (closedBall (0:ℂ) 1) := by sorry

attribute [-instance] CommCStarAlgebra.toNormedCommRing in
theorem radialMode_hasSum (j : ℕ) (ξ ρ : ℝ) (hρ : 0 < ρ) (v : ℂ) (hv : ‖v‖ ≤ 1) :
    HasSum (fun k => volterraTerm j ξ ρ k v) (radialMode j ξ ρ v) := by sorry

attribute [-instance] CommCStarAlgebra.toNormedCommRing in
theorem volterra_remainder_series (j : ℕ) (ξ ρ : ℝ) (hρ : 0 < ρ) (v : ℂ) (hv : ‖v‖ ≤ 1) :
    let u := radialMode j ξ ρ
    let δ := radialSlope j ξ ρ
    let Q := circleQ j ξ ρ
    let term := volterraTerm j ξ ρ
    let E := ∑' k : ℕ, Q^k / ((2*k).factorial : ℝ)
    let O := ∑' k : ℕ, Q^(k+1) / ((2*(k+1)+1).factorial : ℝ)
    u v - δ*v = u 0 + ∑' k : ℕ, term (k+1) v ∧
    ‖u v - δ*v‖ ≤ ‖u 0‖*E + ‖δ‖*O ∧
    E = Real.cosh (Real.sqrt Q) ∧ O = Real.sinh (Real.sqrt Q)/Real.sqrt Q - 1 := by sorry

end Turan.LowerTailSteps
