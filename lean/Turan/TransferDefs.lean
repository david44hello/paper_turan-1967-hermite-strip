-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs

noncomputable section
open Polynomial
namespace Turan

def diskExpansion (p : Polynomial ℂ) (w : ℂ) (r : ℝ) : Polynomial ℂ :=
  p.comp (C w + C (r : ℂ)*X)

def coefficientMass (p : Polynomial ℂ) : ℝ := ∑ j ∈ p.support, ‖p.coeff j‖

def coefficientMargin (p : Polynomial ℂ) (k : ℕ) : ℝ :=
  ‖p.coeff k‖ - ∑ j ∈ p.support.erase k, ‖p.coeff j‖

def transferMode (n : ℕ) : Polynomial ℂ :=
  let p := hermite n
  C (if Even n then (p.eval 0)⁻¹ else 2/p.derivative.eval 0) * p

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

end Turan
