-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.TransferDefs
import Turan.TrinomialDefs

noncomputable section
open Polynomial
namespace Turan

/-- Signed crossings of the positive real ray, with the lower endpoint included. -/
def rayCross (a b : ℂ) : ℤ :=
  if a.im ≤ 0 ∧ 0 < b.im ∧ 0 < a.re*b.im-b.re*a.im then 1
  else if b.im ≤ 0 ∧ 0 < a.im ∧ a.re*b.im-b.re*a.im < 0 then -1 else 0

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

end Turan
