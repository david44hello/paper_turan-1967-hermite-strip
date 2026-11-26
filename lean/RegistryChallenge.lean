-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.

module

public import Mathlib

@[expose] public section

/-!
# Turán's Hermite strip problem
The polynomial is defined using physicists' Hermite polynomials. The upper bound
and its equality classification take the four explicit certificate conditions
below. The smaller-strip counterexample is unconditional.
-/

namespace Turan.NumeralFacts
/-- Proof instances for the fixed integer literals in the certificate formulas. -/
scoped instance (priority := 2000) atLeastTwo2 : Nat.AtLeastTwo 2 := inferInstance
scoped instance (priority := 2000) atLeastTwo3 : Nat.AtLeastTwo 3 := inferInstance
scoped instance (priority := 2000) atLeastTwo4 : Nat.AtLeastTwo 4 := inferInstance
scoped instance (priority := 2000) atLeastTwo5 : Nat.AtLeastTwo 5 := inferInstance
scoped instance (priority := 2000) atLeastTwo6 : Nat.AtLeastTwo 6 := inferInstance
scoped instance (priority := 2000) atLeastTwo9 : Nat.AtLeastTwo 9 := inferInstance
scoped instance (priority := 2000) atLeastTwo10 : Nat.AtLeastTwo 10 := inferInstance
scoped instance (priority := 2000) atLeastTwo15 : Nat.AtLeastTwo 15 := inferInstance
scoped instance (priority := 2000) atLeastTwo16 : Nat.AtLeastTwo 16 := inferInstance
scoped instance (priority := 2000) atLeastTwo30 : Nat.AtLeastTwo 30 := inferInstance
scoped instance (priority := 2000) atLeastTwo36 : Nat.AtLeastTwo 36 := inferInstance
scoped instance (priority := 2000) atLeastTwo76 : Nat.AtLeastTwo 76 := inferInstance
scoped instance (priority := 2000) atLeastTwo87 : Nat.AtLeastTwo 87 := inferInstance
scoped instance (priority := 2000) atLeastTwo100 : Nat.AtLeastTwo 100 := inferInstance
scoped instance (priority := 2000) atLeastTwo256 : Nat.AtLeastTwo 256 := inferInstance
scoped instance (priority := 2000) atLeastTwo1000 : Nat.AtLeastTwo 1000 := inferInstance
scoped instance (priority := 2000) atLeastTwo1733 : Nat.AtLeastTwo 1733 := inferInstance
end Turan.NumeralFacts
open scoped Turan.NumeralFacts

noncomputable section
open Polynomial
open scoped ComplexConjugate
namespace Turan

/-- The physicists' Hermite polynomials. -/
def hermite : ℕ → Polynomial ℂ
  | 0 => 1
  | 1 => 2 * Polynomial.X
  | k + 2 => 2 * Polynomial.X * hermite (k + 1) - (2 * (k + 1 : ℕ) : ℕ) • hermite k

/-- The polynomial whose zeros are studied. -/
def family (n m : ℕ) (a b : ℂ) : Polynomial ℂ :=
  1 + 2 * Polynomial.X + Polynomial.C a * hermite n + Polynomial.C b * hermite m

/-- Real parameter determining the nonreal extremal roots of the cubics. -/
def u : ℝ := Real.sinh (Real.arsinh 1 / 3) / 2
/-- Sharp half-width of the horizontal strip centered on the real axis. -/
def h : ℝ := Real.sqrt (3 / 4 + 3 * u ^ 2)
/-- The shifted root with positive imaginary part of the first extremal cubic. -/
def W : ℂ := ⟨u, h⟩
/-- Coefficient of the third Hermite polynomial in that extremizer. -/
def extremalB : ℂ := (12 * W ^ 2 - 12 * W + 9)⁻¹
/-- Coefficient of the second Hermite polynomial in that extremizer. -/
def extremalA : ℂ := (3 - 6 * W) * extremalB

/-- Nonnegative majorant parameter for the oscillator on a circle of radius ρ about ξ. -/
def circleQ (j : ℕ) (ξ ρ : ℝ) : ℝ :=
  ρ^2 * (|2 * (j : ℝ) + 1 - ξ^2| + 2 * |ξ| * ρ + ρ^2)

/-- The integer scale used by the finite trinomial certificates. -/
def chartScale (n : ℕ) : ℕ := (2*n - 1).sqrt + 1

/-- The even polynomial has value one at zero. The odd polynomial has
derivative equal to the integer scale there. -/
def chartMode (n : ℕ) : Polynomial ℂ :=
  let p := hermite n
  let s := if Even n then (p.eval 0)⁻¹ else (chartScale n : ℂ)/p.derivative.eval 0
  C s * p

/-- The affine pencil and its mode in either normalized trinomial chart. -/
def trinomialChart (n : ℕ) (swap : Bool) (θ : ℂ) : Polynomial ℂ :=
  let low := C (chartScale n : ℂ) * (X + C (1/2))
  if swap then C θ * low + chartMode n else low + C θ * chartMode n

/-- The uniform coefficient inequalities supplied by the supplement's finite
dyadic covers. The centers and radii have the same grids as its records. -/
def TrinomialDiskCheck : Prop :=
  ∀ n : ℕ, 4 ≤ n → n ≤ 79 → ∀ (swap : Bool) (θ : ℂ),
    |θ.re| ≤ 1 → 0 ≤ θ.im → θ.im ≤ 1 →
    ∃ (x y : ℤ) (t k : ℕ), t ∈ ([4,6,8,12,16,24,32] : List ℕ) ∧ 1 ≤ k ∧ k ≤ 4 ∧
      let w : ℂ := ⟨(x : ℝ)/16384, (y : ℝ)/16384⟩
      let r : ℝ := (t : ℝ)/(16*chartScale n)
      let p := (trinomialChart n swap θ).comp (C w + C (r : ℂ)*X)
      ‖w‖ + r < 9/10 ∧ |w.im| + r < 76/100 ∧
        (∑ d ∈ p.support.erase k, ‖p.coeff d‖) < ‖p.coeff k‖

/-- The three polynomials in each finite projective cover, with the integer
normalizations used to form its Taylor coefficients. -/
def lowBasis (n m : ℕ) : Fin 3 → Polynomial ℂ :=
  if (n,m) = (3,5) then ![8*X+4, 8*X^3+6, 8*X^5+15]
  else if n = 2 then ![8+16*X, -8+16*X^2, 15-30*X^4+4*X^6]
  else if n = 3 then ![15+30*X, 15+30*X+C (5/2)*hermite 3, C (-1/8)*hermite 6]
  else ![15+30*X, C (5/4)*hermite 4, C (1/4)*(hermite 6+15*hermite 4)]

/-- Each chart fixes one coefficient to one. The other two range over
the closed complex box used by the exact verifier. -/
def ProjectiveDiskCheck (basis : Fin 3 → Polynomial ℂ) (grid : ℕ) (height : ℝ) (degree : ℕ) : Prop :=
  ∀ (i : Fin 3) (u : Fin 3 → ℂ), u i = 1 →
    (∀ j, |(u j).re| ≤ 1 ∧ |(u j).im| ≤ 1) →
    ∃ (x y : ℤ) (r k : ℕ), 0 < r ∧ 1 ≤ k ∧ k ≤ degree ∧
      let w : ℂ := ⟨(x : ℝ)/grid, (y : ℝ)/grid⟩
      let ρ : ℝ := (r : ℝ)/grid
      let p := (∑ j, C (u j)*basis j).comp (C w + C (ρ:ℂ)*X)
      |w.im| + ρ ≤ height ∧ (∑ d ∈ p.support.erase k, ‖p.coeff d‖) < ‖p.coeff k‖

/-- Projective Taylor-dominance certificate for the pair (3,5). -/
def QuinticChartCheck : Prop := ProjectiveDiskCheck (lowBasis 3 5) 65536 (29491/32768) 5
/-- Projective Taylor-dominance certificates for (2,6), (3,6) and (4,6). -/
def SexticChartCheck : Prop :=
  ∀ n ∈ ([2,3,4] : List ℕ), ProjectiveDiskCheck (lowBasis n 6) 65536 (57016/65536) 6

/-- Hermite mode multiplied by 128 to the power of its degree. -/
def scaledMode (j : ℕ) : Polynomial ℂ := C (128^j) * hermite j

/-- Expansion of the scaled Hermite mode under z = x + rX. -/
def circleJet (j : ℕ) (x r : ℝ) : Polynomial ℂ :=
  (scaledMode j).comp (C (x:ℂ) + C (r:ℂ)*X)

/-- Sum of the moduli of the coefficients of the circle expansion. -/
def circleMass (j : ℕ) (x r : ℝ) : ℝ :=
  let p := circleJet j x r
  ∑ k ∈ p.support, ‖p.coeff k‖

/-- Real part of the linear coefficient of the circle expansion. -/
def circlePivot (j : ℕ) (x r : ℝ) : ℝ := ((circleJet j x r).coeff 1).re

/-- Smaller modulus of the mode at the two real endpoints. -/
def circleEndMin (j : ℕ) (x r : ℝ) : ℝ :=
  min ‖(scaledMode j).eval ((x-r:ℝ):ℂ)‖ ‖(scaledMode j).eval ((x+r:ℝ):ℂ)‖

/-- The real endpoint values of the scaled mode have opposite signs. -/
def bracketed (j : ℕ) (x r : ℝ) : Prop :=
  ((scaledMode j).eval ((x-r:ℝ):ℂ)).re * ((scaledMode j).eval ((x+r:ℝ):ℂ)).re < 0

/-- Outward series bounds used for the two oscillator majorants. -/
def seriesUpper (Q : ℝ) (offset : ℕ) : ℝ :=
  let term k := Q^k / ((2*k+offset).factorial:ℝ)
  let ratio := Q / ((26+offset:ℕ)*(25+offset:ℕ):ℝ)
  (∑ k ∈ Finset.range 13, term k) + term 12 * ratio / (1-ratio)

/-- Linear coefficient corrected for the Gaussian oscillator factor. -/
def weightedPivot (j : ℕ) (x r : ℝ) : ℝ :=
  circlePivot j x r - x*r*((scaledMode j).eval (x:ℂ)).re

/-- Series upper bound for the higher terms of the weighted expansion. -/
def weightedError (j : ℕ) (x r : ℝ) : ℝ :=
  let q := circleQ j x r
  seriesUpper q 0 * ‖(scaledMode j).eval (x:ℂ)‖ +
    (seriesUpper q 1 - 1)*|weightedPivot j x r|

/-- Squared normalization factor for the scaled degree-j Hermite mode. -/
def scaledNormSq (j : ℕ) : ℕ := 32768^j * j.factorial

/-- The six certificate row tests used in linear elimination. -/
inductive CircleTest where
  | affine | low | high | joint | weighted | giroux
  deriving DecidableEq

/-- One circle certificate row with lattice coordinates and integer projection weights. -/
structure CircleRow where
  test : CircleTest
  center : ℤ
  radius : ℕ
  s : ℕ
  t : ℕ

/-- The real center, in units of 1/256. -/
def CircleRow.x (w : CircleRow) : ℝ := (w.center:ℝ)/256
/-- The radius, in units of 1/256. -/
def CircleRow.r (w : CircleRow) : ℝ := (w.radius:ℝ)/256

/-- The checks independent of the two unknown coefficient magnitudes. -/
def CircleRow.valid (w : CircleRow) (n m : ℕ) (sign : ℝ) : Prop :=
  let x := w.x
  let r := w.r
  let projected := fun d e : ℝ => w.s^2+w.t^2 ≤ 100 ∧ 0 ≤ sign*d*e
  w.test = .giroux ∨ (0 < r ∧ r < 87/100 ∧ match w.test with
    | .affine => x = -1/2
    | .low => bracketed n x r
    | .high => bracketed m x r
    | .joint => projected (circlePivot n x r) (circlePivot m x r)
    | .weighted => circleQ n x r ≤ 36 ∧ circleQ m x r ≤ 36 ∧
        projected (weightedPivot n x r) (weightedPivot m x r)
    | .giroux => True)

/-- The rational half-plane checked for a single row. All arguments of
the coefficient evaluations are real lattice points. -/
def CircleRow.cut (w : CircleRow) (n m : ℕ) (A B : ℝ) : Prop :=
  let x := w.x
  let r := w.r
  let pmax := |1+2*x| + 2*r
  let joint := fun (d e dn em p : ℝ) =>
    A*((w.s:ℝ)/10*|d| - dn) + B*((w.t:ℝ)/10*|e| - em) ≤ p
  match w.test with
  | .affine => 2*r ≤ A*circleMass n x r + B*circleMass m x r
  | .low => A*circleEndMin n x r ≤ pmax + B*circleMass m x r
  | .high => B*circleEndMin m x r ≤ pmax + A*circleMass n x r
  | .joint => joint (circlePivot n x r) (circlePivot m x r)
      (circleMass n x r - |circlePivot n x r|) (circleMass m x r - |circlePivot m x r|) pmax
  | .weighted => joint (weightedPivot n x r) (weightedPivot m x r)
      (weightedError n x r) (weightedError m x r)
      (pmax * 2^(⌈3*(|x| * r+r^2/2)/2⌉ : ℤ))
  | .giroux => (87/100)*((2*m*scaledNormSq m).sqrt:ℝ)*B ≤
      1733/1000 + ((scaledNormSq n).sqrt+1:ℝ)*A

/-- The finite list in each sign sector has no feasible pair of nonnegative
coefficient magnitudes. This is the output of the exact linear elimination. -/
def CircleCertificate (n m : ℕ) : Prop :=
  ∀ sign ∈ ([-1,1] : List ℝ), ∃ rows : List CircleRow,
    (∀ w ∈ rows, w.valid n m sign) ∧
    ∀ A B : ℝ, 0 ≤ A → 0 ≤ B → ¬(∀ w ∈ rows, w.cut n m A B)

/-- Coefficients of a polynomial after mapping the unit disk to a specified disk. -/
def diskExpansion (p : Polynomial ℂ) (w : ℂ) (r : ℝ) : Polynomial ℂ :=
  p.comp (C w + C (r : ℂ)*X)

/-- Sum of the moduli of all nonzero polynomial coefficients. -/
def coefficientMass (p : Polynomial ℂ) : ℝ := ∑ j ∈ p.support, ‖p.coeff j‖

/-- Modulus of one coefficient minus the sum for the remaining coefficients. -/
def coefficientMargin (p : Polynomial ℂ) (k : ℕ) : ℝ :=
  ‖p.coeff k‖ - ∑ j ∈ p.support.erase k, ‖p.coeff j‖

/-- Hermite mode normalized at zero using its value or derivative according to parity. -/
def transferMode (n : ℕ) : Polynomial ℂ :=
  let p := hermite n
  C (if Even n then (p.eval 0)⁻¹ else 2/p.derivative.eval 0) * p

/-- One of the two normalized pencils in the paired-circle test. -/
def transferPencil (n : ℕ) (swap : Bool) (θ : ℂ) : Polynomial ℂ :=
  let P := 1 + 2*X
  if swap then transferMode n + C θ * P else P + C θ * transferMode n

/-- Arithmetic content of the paired-circle check. The first circle brackets
a real zero of the upper mode. The strict last inequality compares only
Taylor coefficients and endpoint values. -/
def TransferCertificate (n m : ℕ) : Prop :=
  ∀ (swap : Bool) (θ : ℂ), ‖θ‖ ≤ 1 → 0 ≤ θ.im →
  ∃ (w : ℂ) (ri x ro : ℝ) (k : ℕ), 0 < ri ∧ 0 < ro ∧ 1 ≤ k ∧
    |w.im|+ri < 87/100 ∧ ro < 87/100 ∧
    ((hermite m).eval ((x-ro:ℝ):ℂ)).re * ((hermite m).eval ((x+ro:ℝ):ℂ)).re < 0 ∧
    let S := transferPencil n swap θ
    let L := min ‖(hermite m).eval ((x-ro:ℝ):ℂ)‖ ‖(hermite m).eval ((x+ro:ℝ):ℂ)‖
    coefficientMass (diskExpansion S (x:ℂ) ro) * coefficientMass (diskExpansion (hermite m) w ri) <
      coefficientMargin (diskExpansion S w ri) k * L

/-- Power-of-two scale obtained from the squared norm of a mode. -/
def ratioScale (j : ℕ) : ℕ := 2^((scaledNormSq j).log2/2)

/-- The scaled mode divided by its ratio scale. -/
def ratioMode (j : ℕ) : Polynomial ℂ := C ((ratioScale j : ℂ)⁻¹) * scaledMode j

/-- Coefficient of degree k in exp(-xrv-r²v²/2). -/
def gaugeCoeff (x r : ℝ) (k : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (k/2+1),
    (-x*r)^(k-2*l)*(-r^2/2)^l /
      (((k-2*l).factorial:ℝ)*(l.factorial:ℝ))

/-- Degree-k Taylor coefficient after multiplication by the gauge exponential. -/
def gaugedJet (j : ℕ) (x r : ℝ) (k : ℕ) : ℂ :=
  let p := diskExpansion (ratioMode j) x r
  ∑ l ∈ Finset.range (k+1), p.coeff l * (gaugeCoeff x r (k-l) : ℂ)

/-- Explicit upper bound used for the truncated oscillator expansion. -/
def omittedTail (j : ℕ) (x r : ℝ) : ℝ :=
  let q := circleQ j x (2*r)
  (‖gaugedJet j x r 0‖*seriesUpper q 0 + 2*‖gaugedJet j x r 1‖*seriesUpper q 1)/1024

/-- Pointwise form of the exact coefficient tests on the two ratio charts.
The disk at -1/2 controls the inverse scale. The second disk tests a positive
Taylor coefficient through order ten, with separate bounds for both tails. -/
def RatioCertificate (n m : ℕ) : Prop :=
  ∀ (i j : ℕ), ((i=n ∧ j=m) ∨ (i=m ∧ j=n)) → ∀ χ : ℂ, ‖χ‖ ≤ 1 → 0 ≤ χ.im →
  ∃ (X₀ : ℤ) (R U k : ℕ), 0 < R ∧ 0 < U ∧ 1 ≤ k ∧ k ≤ 10 ∧
    let x : ℝ := X₀/256
    let r : ℝ := R/256
    let r₀ : ℝ := U/256
    r < 87/100 ∧ r₀ < 87/100 ∧ circleQ i x (2*r) ≤ 36 ∧ circleQ j x (2*r) ≤ 36 ∧
    let invBound := (coefficientMass (diskExpansion (ratioMode i) (-1/2) r₀) +
      ‖χ‖*coefficientMass (diskExpansion (ratioMode j) (-1/2) r₀))/(2*r₀)
    let c := fun l => gaugedJet i x r l + χ*gaugedJet j x r l
    (∑ l ∈ (Finset.range 11).erase k, ‖c l‖) + omittedTail i x r + ‖χ‖*omittedTail j x r +
      invBound*(|1+2*x|+2*r)*2^(⌈3*(|x| * r+r^2/2)/2⌉ : ℤ) < ‖c k‖

/-- Signed crossings of the positive real ray, with the lower endpoint included. -/
def rayCross (a b : ℂ) : ℤ :=
  if a.im ≤ 0 ∧ 0 < b.im ∧ 0 < a.re*b.im-b.re*a.im then 1
  else if b.im ≤ 0 ∧ 0 < a.im ∧ a.re*b.im-b.re*a.im < 0 then -1 else 0

/-- One polynomial image segment and its two nominal endpoints fit in a disk avoiding zero. -/
def EdgeCheck (p : Polynomial ℂ) (u v A B center : ℂ) : Prop :=
  let e := p.comp (C ((u+v)/2) + C ((v-u)/2)*X)
  ‖A-center‖ < ‖center‖ ∧ ‖B-center‖ < ‖center‖ ∧
  ‖e.coeff 0-center‖ + ∑ k ∈ e.support.erase 0, ‖e.coeff k‖ < ‖center‖

/-- A closed chain in the strip and the nominal polygon. Every edge disk
contains the nominal endpoints and the actual polynomial on the segment. -/
def PolygonCheck (p : Polynomial ℂ) (h : ℝ) : Prop :=
  ∃ (N : ℕ) (v A center : ℕ → ℂ), 0 < N ∧ v N = v 0 ∧ A N = A 0 ∧
    (∀ i ≤ N, |(v i).im| < h) ∧
    (∀ i < N, EdgeCheck p (v i) (v (i+1)) (A i) (A (i+1)) (center i)) ∧
    0 < ∑ i ∈ Finset.range N, rayCross (A i) (A (i+1))

/-- A disk in the strip has a dominant nonconstant Taylor coefficient. -/
def StripDiskCheck (p : Polynomial ℂ) (h : ℝ) : Prop :=
  ∃ (w : ℂ) (r : ℝ) (k : ℕ), 0 < r ∧ |w.im|+r < h ∧ 1 ≤ k ∧
    0 < coefficientMargin (diskExpansion p w r) k

/-- Normalization of the modes in the two high-coefficient charts. -/
def windingMode (j m : ℕ) : Polynomial ℂ :=
  let p := hermite j
  C (if Even j then (p.eval 0)⁻¹ else (chartScale m:ℂ)/p.derivative.eval 0) * p

/-- Pointwise consequence of the rectangle and disk leaves. The affine circle
is listed explicitly so the bound on the inverse coefficient scale is proved
from a zero-free strip, separately from the computations. -/
def WindingCertificate (n m : ℕ) : Prop :=
  ∀ (i j : ℕ), ((i=n ∧ j=m) ∨ (i=m ∧ j=n)) → ∀ χ : ℂ, ‖χ‖ ≤ 1 → 0 ≤ χ.im →
  ∃ r : ℝ, 0 < r ∧ r < 87/100 ∧
    ∀ κ : ℂ, ‖κ‖ ≤ (coefficientMass (diskExpansion (windingMode i m) (-1/2) r) +
      ‖χ‖*coefficientMass (diskExpansion (windingMode j m) (-1/2) r))/(2*r) →
    let p := windingMode i m + C χ*windingMode j m + C κ*(1+2*X)
    PolygonCheck p (87/100) ∨ StripDiskCheck p (87/100)

/-- The four classes of exact certificates for the finite range. The partition
check covers the index pairs; the class verifiers supply their coefficient
inequalities. None of the four alternatives asserts the existence of a zero. -/
def MiddleChecks : Prop :=
  ∀ n m : ℕ, 2 ≤ n → n < m → 7 ≤ m → m ≤ 449 →
    CircleCertificate n m ∨ RatioCertificate n m ∨
      TransferCertificate n m ∨ WindingCertificate n m

/-- Given the four finite checks, every eligible quadrinomial has a zero in the closed strip of half-width h. -/
theorem theorem_one_closed_given (G1 : TrinomialDiskCheck) (middle : MiddleChecks)
    (F1 : QuinticChartCheck) (E10 : SexticChartCheck)
    (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m) (a b : ℂ) :
    ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| ≤ h := by sorry

/-- Every smaller half-width fails for some quadrinomial. The proof uses an explicit cubic. -/
theorem theorem_one_sharp (t : ℝ) (ht : t < h) :
    ∃ n m : ℕ, 2 ≤ n ∧ n < m ∧ ∃ a b : ℂ,
      ∀ z : ℂ, (family n m a b).eval z = 0 → t < |z.im| := by sorry

/-- Given the four finite checks, exactly the two stated cubics have no zero in the open strip of half-width h. -/
theorem theorem_one_extremizers_given (G1 : TrinomialDiskCheck) (middle : MiddleChecks)
    (F1 : QuinticChartCheck) (E10 : SexticChartCheck)
    (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m) (a b : ℂ) :
    (∀ z : ℂ, (family n m a b).eval z = 0 → h ≤ |z.im|) ↔
    n=2 ∧ m=3 ∧ ((a=extremalA ∧ b=extremalB) ∨
      (a=conj extremalA ∧ b=conj extremalB)) := by sorry

end Turan
