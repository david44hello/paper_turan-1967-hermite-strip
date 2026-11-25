-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Oscillator

noncomputable section
open Polynomial
namespace Turan

def scaledMode (j : ℕ) : Polynomial ℂ := C (128^j) * hermite j

def circleJet (j : ℕ) (x r : ℝ) : Polynomial ℂ :=
  (scaledMode j).comp (C (x:ℂ) + C (r:ℂ)*X)

def circleMass (j : ℕ) (x r : ℝ) : ℝ :=
  let p := circleJet j x r
  ∑ k ∈ p.support, ‖p.coeff k‖

def circlePivot (j : ℕ) (x r : ℝ) : ℝ := ((circleJet j x r).coeff 1).re

def circleEndMin (j : ℕ) (x r : ℝ) : ℝ :=
  min ‖(scaledMode j).eval ((x-r:ℝ):ℂ)‖ ‖(scaledMode j).eval ((x+r:ℝ):ℂ)‖

def bracketed (j : ℕ) (x r : ℝ) : Prop :=
  ((scaledMode j).eval ((x-r:ℝ):ℂ)).re * ((scaledMode j).eval ((x+r:ℝ):ℂ)).re < 0

/-- Outward series bounds used for the two oscillator majorants. -/
def seriesUpper (Q : ℝ) (offset : ℕ) : ℝ :=
  let term k := Q^k / ((2*k+offset).factorial:ℝ)
  let ratio := Q / ((26+offset:ℕ)*(25+offset:ℕ):ℝ)
  (∑ k ∈ Finset.range 13, term k) + term 12 * ratio / (1-ratio)

def weightedPivot (j : ℕ) (x r : ℝ) : ℝ :=
  circlePivot j x r - x*r*((scaledMode j).eval (x:ℂ)).re

def weightedError (j : ℕ) (x r : ℝ) : ℝ :=
  let q := circleQ j x r
  seriesUpper q 0 * ‖(scaledMode j).eval (x:ℂ)‖ +
    (seriesUpper q 1 - 1)*|weightedPivot j x r|

def scaledNormSq (j : ℕ) : ℕ := 32768^j * j.factorial

inductive CircleTest where
  | affine | low | high | joint | weighted | giroux
  deriving DecidableEq

structure CircleRow where
  test : CircleTest
  center : ℤ
  radius : ℕ
  s : ℕ
  t : ℕ

def CircleRow.x (w : CircleRow) : ℝ := (w.center:ℝ)/256
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

end Turan
