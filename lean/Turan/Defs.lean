-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Analytic.Basic

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
