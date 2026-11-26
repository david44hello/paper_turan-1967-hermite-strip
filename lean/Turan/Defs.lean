module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Analytic.Basic

@[expose] public section

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
namespace Turan

/-- The physicists' Hermite polynomials. -/
def hermite : ℕ → Polynomial ℂ
  | 0 => 1
  | 1 => 2 * Polynomial.X
  | k + 2 => 2 * Polynomial.X * hermite (k + 1) - (2 * (k + 1 : ℕ) : ℕ) • hermite k

/-- The polynomial whose zeros are studied. -/
def family (n m : ℕ) (a b : ℂ) : Polynomial ℂ :=
  1 + 2 * Polynomial.X + Polynomial.C a * hermite n + Polynomial.C b * hermite m

def u : ℝ := Real.sinh (Real.arsinh 1 / 3) / 2
def h : ℝ := Real.sqrt (3 / 4 + 3 * u ^ 2)
def W : ℂ := ⟨u, h⟩
def extremalB : ℂ := (12 * W ^ 2 - 12 * W + 9)⁻¹
def extremalA : ℂ := (3 - 6 * W) * extremalB

/-- The symmetric equation for the three shifted zeros. -/
def rootRelation (x y v : ℂ) : Prop := 4 * x * y * v + x + y + v + 1 = 0

def third (w : ℂ) : ℂ := -(2 * w + 1) / (4 * w ^ 2 + 1)

end Turan
