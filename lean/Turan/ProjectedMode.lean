module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.RouteDefs
public import Turan.Hermite

@[expose] public section

noncomputable section
open Polynomial
namespace Turan

private theorem EStar_add (p q : Polynomial ℂ) : EStar (p+q) = EStar p + EStar q := by
  simp only [EStar, derivative_add]
  ring

private theorem EStar_C_mul (c : ℂ) (p : Polynomial ℂ) :
    EStar (C c * p) = C c * EStar p := by
  simp only [EStar, derivative_C_mul]
  ring

private theorem EStar_hermite (j : ℕ) : EStar (hermite j) = C (-(j:ℂ)) * hermite j := by
  apply Polynomial.funext
  intro w
  have h := congrArg (eval w) (hermite_equation j)
  simp only [EStar, eval_sub, eval_mul, eval_X, eval_C, eval_neg, eval_ofNat,
    nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, eval_natCast] at h ⊢
  linear_combination h / 2

/-- Shifting by the other index kills its mode. The second application of the
oscillator then recovers the denominator in the affine part of the projection. -/
private theorem projected_mode_ordered (j k : ℕ) (hj : (j:ℂ) ≠ 0) (hk : (k:ℂ) ≠ 0)
    (a b z ρ : ℂ) (hρ : ρ * (1+2*(1-1/(j:ℂ))*(1-1/(k:ℂ))*z) = 1+2*(1-1/(k:ℂ))*z) :
    let p := family j k a b
    let t := EStar p + C (k:ℂ)*p
    ((k:ℂ)-j)*a*(hermite j).eval z = (1-ρ)*t.eval z - (ρ/(j:ℂ))*(EStar t).eval z := by
  let t := EStar (family j k a b) + C (k:ℂ) * family j k a b
  let u := ((k:ℂ)-j)*a*(hermite j).eval z
  change u = (1-ρ)*t.eval z - (ρ/(j:ℂ))*(EStar t).eval z
  have ht : t = C (k:ℂ)*hermite 0 + C ((k:ℂ)-1)*hermite 1 +
      C (((k:ℂ)-j)*a)*hermite j := by
    change EStar (hermite 0 + hermite 1 + C a * hermite j + C b * hermite k) +
      C (k:ℂ) * (hermite 0 + hermite 1 + C a * hermite j + C b * hermite k) = _
    simp only [EStar_add, EStar_C_mul, EStar_hermite, Nat.cast_zero, Nat.cast_one,
      map_neg, map_zero, map_one, map_mul, map_sub]
    ring
  have htval : t.eval z = k + 2*((k:ℂ)-1)*z + u := by
    rw [ht]
    simp only [hermite, eval_add, eval_mul, eval_C, eval_one, eval_ofNat, eval_X, u]
    ring
  have hEval : (EStar t).eval z = -2*((k:ℂ)-1)*z - j*u := by
    rw [ht]
    simp only [EStar_add, EStar_C_mul, EStar_hermite, Nat.cast_zero, Nat.cast_one]
    simp only [eval_add, eval_mul, eval_C, hermite, eval_one, eval_ofNat, eval_X, u]
    ring
  have hden : t.eval z + (EStar t).eval z / j =
      k * (1+2*(1-1/(j:ℂ))*(1-1/(k:ℂ))*z) := by
    rw [htval, hEval]
    field_simp [hj, hk]
    ring
  calc
    u = t.eval z - k * (1+2*(1-1/(k:ℂ))*z) := by
      rw [htval]
      field_simp [hk]
      ring
    _ = t.eval z - ρ * (t.eval z + (EStar t).eval z / j) := by rw [hden, ← hρ]; ring
    _ = _ := by ring

theorem projected_mode_identity (n m j j' : ℕ) (hn : 2 ≤ n) (hnm : n<m)
    (hj : (j=n ∧ j'=m) ∨ (j=m ∧ j'=n)) (a b : ℂ) (z : ℂ)
    (hz : 1+2*(1-1/(n:ℂ))*(1-1/(m:ℂ))*z ≠ 0) :
    let p := family n m a b
    let β := if j=n then a else b
    let t := EStar p + C (j':ℂ)*p
    ((j':ℂ)-j)*β*(hermite j).eval z =
      (1-projectedRatio n m j' z)*t.eval z -
        (projectedRatio n m j' z/(j:ℂ))*(EStar t).eval z := by
  have hn0 : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm0 : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hratio (k : ℕ) : projectedRatio n m k z * (1+2*(1-1/(n:ℂ))*(1-1/(m:ℂ))*z) =
      1+2*(1-1/(k:ℂ))*z := div_mul_cancel₀ _ hz
  rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa only [ite_true] using projected_mode_ordered _ _ hn0 hm0 a b z _ (hratio _)
  · have hswap : family j' j a b = family j j' b a := by unfold family; ring
    simp only [ite_eq_right hnm.ne', hswap]
    apply projected_mode_ordered _ _ hm0 hn0 b a z
    rw [mul_right_comm (2:ℂ) (1-1/(j:ℂ)) (1-1/(j':ℂ))]
    exact hratio j'

end Turan

#print axioms Turan.projected_mode_identity
